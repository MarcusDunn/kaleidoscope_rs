#![allow(dead_code)]

use std::convert::TryFrom;
use std::fs::File;
use std::io::{BufReader, Read};
use std::iter::Peekable;
use std::process::exit;
use std::vec::IntoIter;

#[derive(Debug, PartialEq)]
enum Token {
    Definition,
    External,
    Identifier(String),
    Number(f64),
    Symbol(char),
}

struct Tokenizer {
    contents: String,
}

impl Tokenizer {
    fn new(file: File) -> Result<Tokenizer, std::io::Error> {
        let mut contents = String::new();
        BufReader::new(file).read_to_string(&mut contents)?;
        Ok(Tokenizer { contents })
    }
}

#[derive(PartialEq, Debug)]
enum Expression {
    Number(f64),
    Expression(Box<Expression>),
    Variable(String),
    Binary(Box<BinaryExpression>),
    Call(Box<CallExpression>),
}

#[derive(PartialEq, Debug)]
struct CallExpression {
    callee: String,
    args: Vec<Expression>,
}

struct PrototypeAst {
    name: String,
    args: Vec<String>,
}

struct FunctionAst {
    proto: PrototypeAst,
    body: Expression,
}

#[derive(PartialEq, Debug)]
struct BinaryExpression {
    op: BinaryOperator,
    lhs: Expression,
    rhs: Expression,
}

#[derive(Debug, Eq, PartialEq)]
struct TokenizerError(String);

impl IntoIterator for Tokenizer {
    type Item = Token;
    type IntoIter = IntoIter<Token>;

    fn into_iter(self) -> Self::IntoIter {
        self.contents
            .split_whitespace()
            .map(|word| {
                if word == "def" {
                    Token::Definition
                } else if word == "extern" {
                    Token::External
                } else if let Ok(number) = word.parse::<f64>() {
                    Token::Number(number)
                } else if word.starts_with(|c: char| !c.is_alphanumeric()) {
                    Token::Symbol(word.chars().next().unwrap())
                } else {
                    Token::Identifier(String::from(word))
                }
            })
            .collect::<Vec<_>>()
            .into_iter()
    }
}

#[derive(Debug, Eq, PartialEq)]
enum BinaryOperator {
    Plus,
    Minus,
    Multiply,
    Divide,
    GreaterThan,
    LessThan,
}

impl BinaryOperator {
    fn precedence(&self) -> u8 {
        use BinaryOperator::*;
        match self {
            GreaterThan | LessThan => 1,
            Plus | Minus => 2,
            Multiply | Divide => 3,
        }
    }
}

impl TryFrom<char> for BinaryOperator {
    type Error = ();

    fn try_from(value: char) -> Result<Self, Self::Error> {
        match value {
            '+' => Ok(BinaryOperator::Plus),
            '-' => Ok(BinaryOperator::Minus),
            '*' => Ok(BinaryOperator::Multiply),
            '/' => Ok(BinaryOperator::Divide),
            '>' => Ok(BinaryOperator::GreaterThan),
            '<' => Ok(BinaryOperator::LessThan),
            _ => Err(()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tokenize_def() {
        let tokenizer = Tokenizer {
            contents: "def".to_string(),
        };
        assert_eq!(tokenizer.into_iter().next(), Some(Token::Definition))
    }

    #[test]
    fn tokenize_identifier() {
        let tokenizer = Tokenizer {
            contents: "defa".to_string(),
        };
        assert_eq!(
            tokenizer.into_iter().next(),
            Some(Token::Identifier(String::from("defa")))
        )
    }

    #[test]
    fn tokenize_extern() {
        let tokenizer = Tokenizer {
            contents: "extern".to_string(),
        };
        assert_eq!(tokenizer.into_iter().next(), Some(Token::External))
    }

    #[test]
    fn tokenize_number() {
        let tokenizer = Tokenizer {
            contents: "1.23".to_string(),
        };
        assert_eq!(tokenizer.into_iter().next(), Some(Token::Number(1.23)))
    }

    #[test]
    fn tokenize_symbol() {
        let tokenizer = Tokenizer {
            contents: "+".to_string(),
        };
        assert_eq!(tokenizer.into_iter().next(), Some(Token::Symbol('+')))
    }

    #[test]
    fn tokenize_series() {
        let token_iter = Tokenizer {
            contents: "1.23 def   extern helloWorld   1.23421 externblah ( )".to_string(),
        }
        .into_iter();
        let expected = vec![
            Token::Number(1.23),
            Token::Definition,
            Token::External,
            Token::Identifier("helloWorld".to_string()),
            Token::Number(1.23421),
            Token::Identifier("externblah".to_string()),
            Token::Symbol('('),
            Token::Symbol(')'),
        ];
        for (a, b) in token_iter.zip(expected) {
            assert_eq!(a, b)
        }
    }

    #[test]
    fn two_plus_one() {
        let one = Expression::Number(1.0);
        let two = Expression::Number(1.0);
        let _ = Expression::Binary(Box::new(BinaryExpression {
            op: BinaryOperator::Plus,
            lhs: one,
            rhs: two,
        }));
    }

    #[test]
    fn parse_simple_function_call() {
        let tokens = vec![
            Token::Identifier(String::from("println")),
            Token::Symbol('('),
            Token::Symbol(')'),
        ];
        let expected = Expression::Call(Box::new(CallExpression {
            callee: String::from("println"),
            args: vec![],
        }));
        assert_eq!(parse(&mut tokens.into_iter().peekable()), Ok(expected))
    }

    #[test]
    fn parse_more_complex_function_call() {
        let tokens = vec![
            Token::Identifier(String::from("println")),
            Token::Symbol('('),
            Token::Identifier(String::from("concat")),
            Token::Symbol('('),
            Token::Identifier(String::from("string1")),
            Token::Symbol(','),
            Token::Identifier(String::from("string2")),
            Token::Symbol(')'),
            Token::Symbol(')'),
        ];
        let expected = Expression::Call(Box::new(CallExpression {
            callee: String::from("println"),
            args: vec![Expression::Call(Box::new(CallExpression {
                callee: String::from("concat"),
                args: vec![
                    Expression::Variable(String::from("string1")),
                    Expression::Variable(String::from("string2")),
                ],
            }))],
        }));
        assert_eq!(parse(&mut tokens.into_iter().peekable()), Ok(expected))
    }

    #[test]
    fn simple_binary_operator() {
        let tokens = vec![
            Token::Identifier(String::from("num1")),
            Token::Symbol('+'),
            Token::Identifier(String::from("num2")),
        ];
        let expected = Expression::Binary(Box::new(BinaryExpression {
            op: BinaryOperator::Plus,
            lhs: Expression::Variable(String::from("num1")),
            rhs: Expression::Variable(String::from("num2")),
        }));
        assert_eq!(parse(&mut tokens.into_iter().peekable()), Ok(expected))
    }

    #[test]
    fn chained_binary_operator() {
        let tokens = vec![
            Token::Identifier(String::from("num1")),
            Token::Symbol('+'),
            Token::Identifier(String::from("num2")),
            Token::Symbol('*'),
            Token::Identifier(String::from("num3")),
        ];
        let expected = Expression::Binary(Box::new(BinaryExpression {
            op: BinaryOperator::Plus,
            lhs: Expression::Variable(String::from("num1")),
            rhs: Expression::Binary(Box::new(BinaryExpression {
                op: BinaryOperator::Multiply,
                lhs: Expression::Variable(String::from("num2")),
                rhs: Expression::Variable(String::from("num3")),
            })),
        }));
        assert_eq!(parse(&mut tokens.into_iter().peekable()), Ok(expected))
    }

    #[test]
    fn chained_binary_operator_2() {
        let tokens = vec![
            Token::Identifier(String::from("num1")),
            Token::Symbol('*'),
            Token::Identifier(String::from("num2")),
            Token::Symbol('+'),
            Token::Identifier(String::from("num3")),
        ];
        let expected = Expression::Binary(Box::new(BinaryExpression {
            op: BinaryOperator::Plus,
            lhs: Expression::Binary(Box::new(BinaryExpression {
                op: BinaryOperator::Multiply,
                lhs: Expression::Variable(String::from("num1")),
                rhs: Expression::Variable(String::from("num2")),
            })),
            rhs: Expression::Variable(String::from("num3")),
        }));
        assert_eq!(parse(&mut tokens.into_iter().peekable()), Ok(expected))
    }
}

fn main() -> Result<(), std::io::Error> {
    let token_iter = Tokenizer::new(File::open("main.marc")?)?.into_iter();
    let _ = parse(&mut token_iter.peekable());
    Ok(())
}

// todo, better error handling with EOF
fn parse(mut token_iter: &mut Peekable<impl Iterator<Item = Token>>) -> Result<Expression, String> {
    if let Some(token) = token_iter.next() {
        let expression = match token {
            Token::Definition => { todo!() }
            Token::External => { todo!() }
            Token::Identifier(name) => {
                if let Some(Token::Symbol('(')) = token_iter.peek() {
                    let _ = token_iter.next(); // pop off the '('
                    let mut arguments: Vec<Expression> = Vec::new();
                    loop {
                        if let Some(token) = token_iter.peek() {
                            match token {
                                Token::Symbol(')') => {
                                    let _ = token_iter.next(); // pop off the ')'
                                    break;
                                }
                                Token::Symbol(',') => {
                                    let _ = token_iter.next(); // pop off the ','
                                    continue;
                                }
                                _ => {
                                    match parse(token_iter) {
                                        Ok(argument) => arguments.push(argument),
                                        Err(error_message) => return Err(format!("Error while parsing arguments to {}: {}", name, error_message)),
                                    }
                                }
                            }
                        } else {
                            return Err(format!("Error while parsing arguments to {}: missing closing parenthesis around arguments", name));
                        }
                    }
                    Ok(Expression::Call(Box::new(CallExpression {
                        callee: name,
                        args: arguments,
                    })))
                } else {
                    Ok(Expression::Variable(name))
                }
            }
            Token::Number(num) => { Ok(Expression::Number(num)) }
            Token::Symbol('(') => {
                match parse(&mut token_iter) {
                    Ok(inner_expression) => {
                        match token_iter.next() {
                            Some(Token::Symbol(')')) => Ok(inner_expression),
                            Some(token) => Err(format!("found {:?} after a single expression inside parenthesis, perhaps missing closing parenthesis?", token)),
                            None => Err(String::from("reached end of input while parsing expression inside parenthesis, perhaps missing closing parenthesis?"))
                        }
                    }
                    Err(error_message) => {
                        Err(format!("could not find an expression inside parenthesis, instead got: {}", error_message))
                    }
                }
            }
            _ => panic!()
        };
        match expression {
            Ok(expression) => check_binary_expression(expression, 0, token_iter),
            Err(error_message) => Err(error_message),
        }
    } else {
        Err(String::from("reached end of iterator"))
    }
}

fn check_binary_expression(
    left_hand_side: Expression,
    left_hand_side_precedence: u8,
    token_iter: &mut Peekable<impl Iterator<Item = Token>>,
) -> Result<Expression, String> {
    match token_iter.peek() {
        Some(Token::Symbol(s)) => match BinaryOperator::try_from(*s) {
            Ok(binary_operator) => {
                if binary_operator.precedence() < left_hand_side_precedence {
                    Ok(left_hand_side)
                } else {
                    let _ = token_iter.next(); // pop binary operator
                    if let Ok(right_hand_side) = parse(token_iter) {
                        if let Some(token) = token_iter.peek() {
                            todo!()
                        } else {
                            Ok(Expression::Binary(Box::new(BinaryExpression {
                                op: binary_operator,
                                lhs: left_hand_side,
                                rhs: right_hand_side,
                            })))
                        }
                    } else {
                        Err(format!(
                            "missing right hand side of binary operator {:?}",
                            binary_operator
                        ))
                    }
                }
            }
            Err(_) => Ok(left_hand_side),
        },
        _ => Ok(left_hand_side),
    }
}
