module Lib
    ( someFunc
    ) where

import System.Environment
import Text.Parsec.Pos (SourcePos)
import Text.Parsec.Error (ParseError)
import Text.Parsec.String
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Prim (parse, getPosition)
import Data.Char
import Data.List
import Control.Applicative
import Control.Monad (liftM2)

someFunc :: IO ()
someFunc = do
  args <- getArgs
  traceEval (args !! 0)

data Expr = Num SourcePos Int
          | Var SourcePos String
          | App SourcePos Expr Expr
          | Abs SourcePos String Expr
  deriving Show

num :: Parser Expr
num = do
  pos <- getPosition
  n <- many1 digit
  spaces
  return $ Num pos (read n)

sym :: Parser String
sym = do
  x <- symhead
  xs <- many symtail
  spaces
  return (x:xs)
  where
    symhead = satisfy isLetter <|> char '_'
    symtail = symhead <|> satisfy isDigit

var :: Parser Expr
var = do
  pos <- getPosition
  s <- sym
  return $ Var pos s

parens :: Parser Expr
parens = do
  char '('
  spaces
  e <- expr
  char ')'
  spaces
  return e

abst :: Parser Expr
abst = do
  pos <- getPosition
  string "lambda"
  many1 space
  v <- sym
  char '.'
  spaces
  e <- expr
  return $ Abs pos v e

abstCurry = do
  pos <- getPosition
  string "lambda"
  many1 space
  vs <- many1 sym
  char '.'
  spaces
  e <- expr
  return $ foldr (Abs pos) e vs

term :: Parser Expr
term = abstCurry <|> num <|> var <|> parens

leadingSpace :: Parser Expr
leadingSpace = do
  many1 space
  expr

expr :: Parser Expr
expr = do
  pos <- getPosition
  chainl1 term (return (App pos)) <|> leadingSpace

absExpr :: Parser PrettyAbsExpr
absExpr = do
  rawExpr <- expr <* eof
  let xs = getFreeVars rawExpr
  absExpr <- toAbsExpr rawExpr xs
  return $ PrettyAbsExpr absExpr xs
  
getFreeVars :: Expr -> [String]
getFreeVars e = case e of
  Num pos n -> []
  Var pos s -> [s]
  App pos f a -> nub ((getFreeVars f) ++ (getFreeVars a))
  Abs pos s e -> delete s (getFreeVars e)

data AbsExpr = AbsNum Int
             | AbsVar Int
             | AbsApp AbsExpr AbsExpr
             | AbsAbs String AbsExpr
  deriving Show

data PrettyAbsExpr = PrettyAbsExpr AbsExpr [String]

absUncurry :: AbsExpr -> Maybe (AbsExpr, [String])
absUncurry exp = _uncurry exp []
  where _uncurry exp ss = case exp of
          AbsAbs s e -> _uncurry e (s:ss)
          _ -> Just (exp, ss)

instance Show PrettyAbsExpr where
  show (PrettyAbsExpr (AbsNum n) _) = show n
  show (PrettyAbsExpr (AbsVar n) xs) = (xs !! n)
  show (PrettyAbsExpr (AbsApp f a) xs) = func' ++ " " ++ args'
    where
      func = show (PrettyAbsExpr f xs)
      args = show (PrettyAbsExpr a xs)
      doparens s = "(" ++ s ++ ")"
      func' = case f of
                AbsAbs _ _ -> doparens func
                _ -> func
      args' = case a of
                AbsApp _ _ -> doparens args
                AbsAbs _ _ -> doparens args
                _ -> args
  show (PrettyAbsExpr (aa @ (AbsAbs _ _)) xs) = "lambda" ++ args ++ ". " ++ body
    where
      Just (e, ss) = absUncurry aa
      args = foldr (\a b -> (b ++ " " ++ a)) "" ss
      body = show (PrettyAbsExpr e (ss++xs))

toAbsExpr :: Expr -> [String] -> Parser AbsExpr
toAbsExpr e xs = case e of
  Num pos n -> return $ AbsNum n
  Var pos s -> case findIndex (== s) xs of
    Just n -> return $ AbsVar n
    _ -> fail "error AbsExpr"
  App pos f a -> do 
    f' <- toAbsExpr f xs
    a' <- toAbsExpr a xs
    return $ AbsApp f' a'
  Abs pos s e -> do
    e' <- toAbsExpr e (s:xs)
    return $ AbsAbs s e'

parseToPrettyAbsExpr :: String -> Either ParseError PrettyAbsExpr
parseToPrettyAbsExpr s = parse absExpr "(unknown)" s

addFreeIndex :: AbsExpr -> Int -> Int -> AbsExpr
addFreeIndex e inc fre = case e of
  AbsVar vn | vn >= fre -> AbsVar (vn+inc)
  AbsApp f a -> AbsApp (addFreeIndex' f fre) (addFreeIndex' a fre)
  AbsAbs s e -> AbsAbs s (addFreeIndex' e (fre+1))
  _ -> e
  where addFreeIndex' e fre = addFreeIndex e inc fre

incFreeIndex e n = addFreeIndex e (1) n
decFreeIndex e n = addFreeIndex e (-1) n

subst :: AbsExpr -> Int -> AbsExpr -> AbsExpr
subst el n er = case el of
  AbsVar vn | vn == n -> er
  AbsApp f a -> AbsApp (subst f n er) (subst a n er)
  AbsAbs s e -> AbsAbs s (subst e (n+1) (incFreeIndex er n))
  _ -> el

data EvalStopEvent = EvalStopEvent String

eval1 :: AbsExpr -> [String] -> [AbsExpr] -> Either EvalStopEvent AbsExpr
eval1 exp xs env = case exp of
  AbsNum _ -> success
  AbsAbs _ _ -> success
  AbsVar n | n < length env -> return (env !! n)
           | otherwise -> noSymbol n
  AbsApp f@(AbsApp _ _) a -> liftM2 AbsApp (eval1 f xs env) (return a)
  AbsApp f a@(AbsApp _ _) -> liftM2 AbsApp (return f) (eval1 a xs env)
  AbsApp (AbsVar fn) a | fn < length env -> return $ AbsApp (env !! fn) a
                       | otherwise -> noSymbol fn
  AbsApp f (AbsVar an) | an < length env -> return $ AbsApp f (env !! an)
                       | otherwise -> noSymbol an
  AbsApp (AbsAbs _ e) a -> return $ (decFreeIndex (subst e 0 (incFreeIndex a 0)) 1)
  _ -> cantEvaluate
  where
    success = fail "success"
    noSymbol n = fail $ "no symbol \"" ++ (xs !! n) ++ "\" in scope"
    cantEvaluate = fail $ "not evaluatable expression \"" ++ (show $ PrettyAbsExpr exp xs) ++"\""

traceEval :: String -> IO ()
traceEval s = case parseToPrettyAbsExpr s of
  Left err -> print err
  Right (PrettyAbsExpr exp xs) -> trace exp
    where
      trace exp = do
        print (PrettyAbsExpr exp xs)
        case eval1 exp xs [] of
          Right e -> trace e
          Left (EvalStopEvent msg) -> putStrLn $ msg
