// use log_derive::{logfn, logfn_inputs};

#[derive(Clone, PartialEq, Debug)]
pub enum Value<'a> {
    /// Scalar value
    /// - strings
    /// - booleans
    /// - numbers
    /// - nulls
    Scalar(&'a str),
    /// Sequence
    /// - flow style
    ///   [x, y, z]
    /// - block style
    ///   - x
    ///   - y
    ///   - z
    Sequence(Vec<Value<'a>>),
    /// Mapping
    /// - flow style
    ///   { x: 1, y: 2 }
    /// - block style
    ///   x: 1
    ///   y: 2
    Mapping(Vec<Entry<'a>>),
}

#[derive(Clone, PartialEq, Debug)]
pub struct Entry<'a> {
    key: Value<'a>,
    value: Value<'a>,
}

pub fn parse<'a>(input: &'a str) -> Result<Value<'a>, &'static str> {
    // XXX: not sure if needed to evaluate the indent
    parse_value(input.trim(), 0).map(|(_idx, value)| value)
    // let input = input.trim();

    // let mut idx = 0;
    // let mut value = None;

    // // parse outer later for value
    // while idx != input.len() {
    //     dbg!(idx);
    //     let (len, next_value) = parse_value(&input[idx..], 0)?;
    //     idx += len;
    //     value = match (value, next_value) {
    //         // join individual sequence
    //         // (Some(Value::Sequence(seq1)), Value::Sequence(seq2)) => Some(Value::Sequence(
    //         //     seq1.into_iter().chain(seq2.into_iter()).collect(),
    //         // )),
    //         (None, value) => Some(value),
    //         parsed => unimplemented!("{:?}", parsed),
    //     };
    //     let msg = format!("loop {} {}", idx, input.len());
    //     dbg!(msg);
    // }
    // Ok(value.unwrap())
}

/// helper function to count blanks starting from idx for input string
fn blanks(input: &str, idx: usize) -> usize {
    let input = input[idx..].as_bytes().iter();
    input.take_while(|&b| *b == b' ').count()
}

fn parse_value<'a>(input: &'a str, indent: usize) -> Result<(usize, Value<'a>), &'static str> {
    let msg = format!("parsing {}", input);
    dbg!(msg);

    // default next character to empty if not available
    let nc = if input[1..].len() != 0 {
        input.as_bytes()[1]
    } else {
        b' '
    };

    // match first character to determine next parser
    match input.as_bytes()[0] {
        b'[' => parse_flow_sequence(&input[0..], indent),
        b'{' => parse_flow_mapping(&input[0..], indent),
        b'-' if nc == b' ' => parse_block_sequence(&input[0..], indent),
        b'?' if nc == b' ' => parse_block_mapping(&input[0..], indent),
        b'a'..=b'z' | b'0'..=b'9' | b'-' => parse_flow_scalar(&input[0..], indent),
        b']' => return Err("closing tag"), // fallback
        b'}' => return Err("closing tag"), // fallback
        c => unimplemented!("{:?}", c as char),
    }
}

/// input: "abc" (no whitespaces)
fn parse_flow_scalar<'a>(
    input: &'a str,
    _indent: usize,
) -> Result<(usize, Value<'a>), &'static str> {
    // can ignore the first parsed input
    // limit to input.len to avoid overflow
    for idx in 1..input.len() {
        dbg!(input.as_bytes()[idx] as char);
        match input.as_bytes()[idx] {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b' ' => continue,
            // XXX: count last spaces instead of trim_end?
            _ => return Ok((idx, Value::Scalar(dbg!(&input[..idx]).trim_end()))),
        }
    }
    Ok((input.len(), Value::Scalar(dbg!(input.trim_end()))))
}

#[test]
fn flow_scalar_ignore_whitespace() {
    assert_eq!(parse_flow_scalar("1\n", 0), Ok((1, Value::Scalar("1"))));
}

#[test]
fn scalar_negative() {
    assert_eq!(parse("-1"), Ok(Value::Scalar("-1")));
}

/// input: "[..."
fn parse_flow_sequence<'a>(
    input: &'a str,
    _indent: usize,
) -> Result<(usize, Value<'a>), &'static str> {
    let mut sequences = Vec::new();
    let mut idx = 1;

    for _i in 1..128 {
        idx += input[idx..]
            .as_bytes()
            .iter()
            .take_while(|&b| *b == b' ')
            .count();
        if let Ok((len, value)) = parse_value(&input[idx..], 0) {
            idx += len;
            sequences.push(value);
        }
        idx += input[idx..]
            .as_bytes()
            .iter()
            .take_while(|&b| *b == b' ')
            .count();
        dbg!(&input[idx..]);

        match input.as_bytes()[idx] {
            b']' => return Ok((idx + 1, Value::Sequence(sequences))),
            b',' => idx += 1,
            c => unimplemented!("{:?}", c as char),
        }
        dbg!(format!("loop {}", _i));
    }
    Err("recursion limit")
}

#[test]
fn flow_sequence_empty() {
    assert_eq!(parse("[]"), Ok(Value::Sequence(vec![])));
}

#[test]
fn flow_sequence_empty_spaces() {
    assert_eq!(parse("[] "), Ok(Value::Sequence(vec![])));
    assert_eq!(parse(" []"), Ok(Value::Sequence(vec![])));
}

#[test]
fn flow_sequence_single() {
    assert_eq!(parse("[1]"), Ok(Value::Sequence(vec![Value::Scalar("1")])));
}

#[test]
fn flow_sequence_compact() {
    assert_eq!(
        parse("[1,2]"),
        Ok(Value::Sequence(vec![
            Value::Scalar("1"),
            Value::Scalar("2")
        ]))
    );
    assert_eq!(
        parse("[1,2,3]"),
        Ok(Value::Sequence(vec![
            Value::Scalar("1"),
            Value::Scalar("2"),
            Value::Scalar("3")
        ]))
    );
}

#[test]
fn flow_sequence_relax() {
    let output = Ok(Value::Sequence(vec![
        Value::Scalar("1"),
        Value::Scalar("2"),
    ]));
    assert_eq!(parse("[1, 2]"), output);
    assert_eq!(parse("[1 ,2]"), output);
    assert_eq!(parse("[ 1, 2 ]"), output);
}

#[test]
fn flow_sequence_extra_comma() {
    let output = Ok(Value::Sequence(vec![
        Value::Scalar("1"),
        Value::Scalar("2"),
    ]));
    assert_eq!(parse("[1,2,]"), output);
    assert_eq!(parse("[1, 2,]"), output);
    assert_eq!(parse("[1, 2, ]"), output);
    assert_eq!(parse("[1 , 2 , ]"), output);
}

#[test]
fn flow_sequence_nested() {
    assert_eq!(
        parse("[[]]"),
        Ok(Value::Sequence(vec![Value::Sequence(vec![])]))
    );
    assert_eq!(
        parse("[[1], [2]]"),
        Ok(Value::Sequence(vec![
            Value::Sequence(vec![Value::Scalar("1")]),
            Value::Sequence(vec![Value::Scalar("2")]),
        ]))
    );
    assert_eq!(
        parse("[[1,2]]"),
        Ok(Value::Sequence(vec![Value::Sequence(vec![
            Value::Scalar("1"),
            Value::Scalar("2"),
        ])]))
    );
}

/// input: "- ...\n"
fn parse_block_sequence<'a>(
    input: &'a str,
    indent: usize,
) -> Result<(usize, Value<'a>), &'static str> {
    let mut sequences = Vec::new();
    let mut idx = 1;
    dbg!(&input[idx..]);
    dbg!(indent);

    // get inner indent on first run (- not counted)
    let inner_indent = input[idx..]
        .as_bytes()
        .iter()
        .take_while(|&b| *b == b' ')
        .count();
    idx += inner_indent;

    // check to see if document ended
    if idx == input.len() {
        return Ok((idx, Value::Sequence(sequences)));
    }

    idx += input[idx..]
        .as_bytes()
        .iter()
        .take_while(|&b| *b == b' ')
        .count();
    if let Ok((len, value)) = parse_value(&input[idx..], indent + 1 + inner_indent) {
        sequences.push(value);
        idx += len;
    } else {
        return Ok((idx, Value::Sequence(sequences)));
    }
    dbg!(format!("loop 0 {}", indent));

    for _i in 1..128 {
        dbg!(&input[idx..]);
        // continue parsing if newline is avaliable
        if idx == input.len() || input.as_bytes()[idx] != b'\n' {
            return Ok((idx, Value::Sequence(sequences)));
        }
        dbg!(&input[idx..]);

        // previous indent, fallback if not matched
        for i in idx + 1..idx + 1 + indent {
            if input.as_bytes()[i] != b' ' {
                return Ok((idx, Value::Sequence(dbg!(sequences))));
            }
        }
        // XXX: ignore parsing newline and indent multiple times
        idx += 1;
        idx += indent;

        // block indicator
        assert_eq!(input.as_bytes()[idx], b'-', "missing '-'");
        idx += 1;

        // inner indent
        for idx in idx..idx + inner_indent {
            assert_eq!(input.as_bytes()[idx], b' ', "invalid inner indent");
        }
        idx += inner_indent;
        dbg!(&input[idx..]);

        idx += input[idx..]
            .as_bytes()
            .iter()
            .take_while(|&b| *b == b' ')
            .count();
        if let Ok((len, value)) = parse_value(&input[idx..], indent + 1 + inner_indent) {
            sequences.push(value);
            dbg!(&input[idx..]);
            idx += len;
        }
        dbg!(format!("loop {}", _i));
    }
    Err("recursion limit")
}

#[test]
fn block_sequence_empty() {
    assert_eq!(parse("-"), Ok(Value::Sequence(vec![])));
    assert_eq!(parse("- "), Ok(Value::Sequence(vec![])));
}

#[test]
fn block_sequence_single() {
    assert_eq!(parse("- 1"), Ok(Value::Sequence(vec![Value::Scalar("1")])));
}

#[test]
fn block_sequence_single_negative() {
    assert_eq!(
        parse("- -1"),
        Ok(Value::Sequence(vec![Value::Scalar("-1")]))
    );
}

#[test]
fn block_sequence_multiple() {
    assert_eq!(
        parse("- 1\n- 2"),
        Ok(Value::Sequence(vec![
            Value::Scalar("1"),
            Value::Scalar("2")
        ]))
    );
}

#[test]
fn flow_in_block_sequence() {
    assert_eq!(
        parse("- [1]"),
        Ok(Value::Sequence(vec![Value::Sequence(vec![Value::Scalar(
            "1"
        )])]))
    );
    assert_eq!(
        parse("- [1]\n- [2]"),
        Ok(Value::Sequence(vec![
            Value::Sequence(vec![Value::Scalar("1")]),
            Value::Sequence(vec![Value::Scalar("2")])
        ]))
    );
    assert_eq!(
        parse("- {k: v}"),
        Ok(Value::Sequence(vec![Value::Mapping(vec![Entry {
            key: Value::Scalar("k"),
            value: Value::Scalar("v")
        }])]))
    );
}

#[test]
fn block_in_block_sequence() {
    assert_eq!(
        parse("- - hello\n  - world"),
        Ok(Value::Sequence(vec![Value::Sequence(vec![
            Value::Scalar("hello"),
            Value::Scalar("world")
        ])]))
    );
    assert_eq!(
        parse("- - hello\n  - world\n- test"),
        Ok(Value::Sequence(vec![
            Value::Sequence(vec![Value::Scalar("hello"), Value::Scalar("world")]),
            Value::Scalar("test")
        ]))
    );
}

#[test]
fn block_in_block_in_block_sequence() {
    assert_eq!(
        parse("- - - 1\n  - 2\n- 3"),
        Ok(Value::Sequence(vec![
            Value::Sequence(vec![
                Value::Sequence(vec![Value::Scalar("1")]),
                Value::Scalar("2")
            ]),
            Value::Scalar("3")
        ]))
    );
}

/// input: "{..."
fn parse_flow_mapping<'a>(
    input: &'a str,
    _indent: usize,
) -> Result<(usize, Value<'a>), &'static str> {
    let mut mappings = Vec::new();
    let mut idx = 1;

    for _i in 1..128 {
        idx += input[idx..]
            .as_bytes()
            .iter()
            .take_while(|&b| *b == b' ')
            .count();
        if let Ok((len, key)) = parse_value(&input[idx..], 0) {
            idx += len;

            idx += input[idx..]
                .as_bytes()
                .iter()
                .take_while(|&b| *b == b' ')
                .count();

            assert_eq!(input.as_bytes()[idx], b':', "missing ':'");
            idx += 1;

            idx += input[idx..]
                .as_bytes()
                .iter()
                .take_while(|&b| *b == b' ')
                .count();

            if let Ok((len, value)) = parse_value(&input[idx..], 0) {
                mappings.push(Entry { key, value });
                idx += len;
            }
        }
        dbg!(&input[idx..]);
        idx += input[idx..]
            .as_bytes()
            .iter()
            .take_while(|&b| *b == b' ')
            .count();

        match input.as_bytes()[idx] {
            b'}' => return Ok((idx + 1, Value::Mapping(mappings))),
            b',' => idx += 1,
            c => unimplemented!("{:?}", c as char),
        }
        dbg!(format!("loop {}", _i));
    }
    Err("recursion limit")
}

#[test]
fn flow_mapping_single() {
    assert_eq!(
        parse("{a:1}"),
        Ok(Value::Mapping(vec![Entry {
            key: Value::Scalar("a"),
            value: Value::Scalar("1"),
        }]))
    );
}

#[test]
fn flow_mapping_empty() {
    assert_eq!(parse("{}"), Ok(Value::Mapping(vec![])));
}

#[test]
fn flow_mapping_empty_spaces() {
    assert_eq!(parse(" {}"), Ok(Value::Mapping(vec![])));
    assert_eq!(parse("{} "), Ok(Value::Mapping(vec![])));
}

#[test]
fn flow_mapping_compact() {
    assert_eq!(
        parse("{a:1,b:2}"),
        Ok(Value::Mapping(vec![
            Entry {
                key: Value::Scalar("a"),
                value: Value::Scalar("1"),
            },
            Entry {
                key: Value::Scalar("b"),
                value: Value::Scalar("2"),
            }
        ]))
    );
    assert_eq!(
        parse("{a:1,b:2,c:3}"),
        Ok(Value::Mapping(vec![
            Entry {
                key: Value::Scalar("a"),
                value: Value::Scalar("1"),
            },
            Entry {
                key: Value::Scalar("b"),
                value: Value::Scalar("2"),
            },
            Entry {
                key: Value::Scalar("c"),
                value: Value::Scalar("3"),
            }
        ]))
    );
}

#[test]
fn flow_mapping_relax() {
    let output = Ok(Value::Mapping(vec![
        Entry {
            key: Value::Scalar("a"),
            value: Value::Scalar("1"),
        },
        Entry {
            key: Value::Scalar("b"),
            value: Value::Scalar("2"),
        },
    ]));
    assert_eq!(parse("{a:1, b:2}"), output);
    assert_eq!(parse("{ a:1, b:2 }"), output);
    assert_eq!(parse("{a: 1, b: 2}"), output);
    assert_eq!(parse("{a :1, b :2}"), output);
    assert_eq!(parse("{ a : 1 , b : 2 }"), output);
}

#[test]
fn flow_mapping_extra_comma() {
    let output = Ok(Value::Mapping(vec![
        Entry {
            key: Value::Scalar("a"),
            value: Value::Scalar("1"),
        },
        Entry {
            key: Value::Scalar("b"),
            value: Value::Scalar("2"),
        },
    ]));
    assert_eq!(parse("{a: 1, b: 2,}"), output);
    assert_eq!(parse("{a: 1, b: 2, }"), output);
}

/// input: "? ... [: ...]"
fn parse_block_mapping<'a>(
    input: &'a str,
    indent: usize,
) -> Result<(usize, Value<'a>), &'static str> {
    debug_assert_eq!(input.as_bytes()[0], b'?', "missing '?'");
    let mut mappings = Vec::new();
    let mut idx = 1;
    dbg!(&input[idx..]);
    dbg!(indent);

    // get inner indent on first run (- not counted)
    let inner_indent = blanks(input, idx);
    idx += inner_indent;

    // XXX: need to check to see if document ended?
    if let Ok((len, key)) = parse_value(&input[idx..], indent + 1 + inner_indent) {
        idx += len;

        // newline
        if idx == input.len() || input.as_bytes()[idx] != b'\n' {
            mappings.push(Entry {
                key,
                value: Value::Scalar(""),
            });
            return Ok((idx, Value::Mapping(mappings)));
        }

        // block indicator
        if input.as_bytes()[idx + 1] == b':' {
            idx += 1; // include previous newline
            idx += 1; // colon

            idx += blanks(input, idx);

            if let Ok((len, value)) = parse_value(&input[idx..], indent + 1 + inner_indent) {
                mappings.push(Entry { key, value });
                idx += len;
            }
            dbg!(&input[idx..]);
        } else {
            mappings.push(Entry {
                key,
                value: Value::Scalar(""),
            });
        }
    } else {
        return Ok((idx, Value::Mapping(mappings)));
    };

    for _i in 1..128 {
        // continue parsing if newline is avaliable
        if idx == input.len() || input.as_bytes()[idx] != b'\n' {
            return Ok((idx, Value::Mapping(mappings)));
        }
        idx += 1;

        // previous indent, fallback if not matched
        for i in idx..idx + indent {
            if input.as_bytes()[i] != b' ' {
                return Ok((idx, Value::Mapping(mappings)));
            }
        }
        idx += indent;

        // block indicator
        assert_eq!(input.as_bytes()[idx], b'?', "missing '?'");
        idx += 1;
        dbg!(&input[idx..]);

        // inner indent
        for idx in idx..idx + inner_indent {
            assert_eq!(input.as_bytes()[idx], b' ', "invalid inner indent");
        }
        idx += inner_indent;
        dbg!(&input[idx..]);

        if let Ok((len, key)) = parse_value(&input[idx..], indent + 1 + inner_indent) {
            idx += len;

            // newline
            if idx == input.len() || input.as_bytes()[idx] != b'\n' {
                mappings.push(Entry {
                    key,
                    value: Value::Scalar(""),
                });
                return Ok((idx, Value::Mapping(mappings)));
            }

            // block indicator
            if input.as_bytes()[idx + 1] == b':' {
                idx += 1; // include previous newline
                idx += 1; // colon

                idx += blanks(input, idx);

                if let Ok((len, value)) = parse_value(&input[idx..], indent + 1 + inner_indent) {
                    mappings.push(Entry { key, value });
                    idx += len;
                }
                dbg!(&input[idx..]);
            } else {
                mappings.push(Entry {
                    key,
                    value: Value::Scalar(""),
                });
            }
        } else {
            return Ok((idx, Value::Mapping(mappings)));
        };
    }

    Err("recursion limit")
}

#[test]
fn block_mapping_explicit_key_only() {
    assert_eq!(
        parse("? key"),
        Ok(Value::Mapping(vec![Entry {
            key: Value::Scalar("key"),
            value: Value::Scalar("")
        }]))
    );
}

#[test]
fn block_mapping_explicit_multiple_key_only() {
    assert_eq!(
        parse("? key1\n? key2"),
        Ok(Value::Mapping(vec![
            Entry {
                key: Value::Scalar("key1"),
                value: Value::Scalar("")
            },
            Entry {
                key: Value::Scalar("key2"),
                value: Value::Scalar("")
            }
        ]))
    );
}

#[test]
fn block_mapping_explicit_single_key_value() {
    assert_eq!(
        parse("? key\n: value"),
        Ok(Value::Mapping(vec![Entry {
            key: Value::Scalar("key"),
            value: Value::Scalar("value")
        }]))
    );
}

#[test]
fn block_mapping_explicit_multiple_key_value() {
    assert_eq!(
        parse("? key1\n: value1\n? key2\n: value2"),
        Ok(Value::Mapping(vec![
            Entry {
                key: Value::Scalar("key1"),
                value: Value::Scalar("value1")
            },
            Entry {
                key: Value::Scalar("key2"),
                value: Value::Scalar("value2")
            }
        ]))
    );
}

#[test]
fn block_mapping_explicit_with_block_sequence() {
    assert_eq!(
        parse("? - key1\n  - key2\n: - value1\n  - value2"),
        Ok(Value::Mapping(vec![
            Entry {
                key: Value::Sequence(vec![Value::Scalar("key1"), Value::Scalar("key2")]),
                value: Value::Sequence(vec![Value::Scalar("value1"), Value::Scalar("value2")])
            }
        ]))
    );
}
