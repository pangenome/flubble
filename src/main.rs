// use our lib
//extern crate flubble;
use flubble::{make_nonplanar_1, build_structure_tree};

fn main() {
    //let mut graph = make_example_a();
    //let mut graph = make_example_c();
    //let mut graph = make_example_fig1();
    let mut graph = make_nonplanar_1();
    //let mut graph = make_example_fig1_a();
    //let mut graph = make_example_diamond();
    let _tree = build_structure_tree(&mut graph);

}
