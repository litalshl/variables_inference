import Collections = require('typescript-collections');

'Input
let Type = { TypeVariable, ConcreteType }
let Constraint = { Left: Type, Right: Type }
let Constriants = List<Constriant>

'Helper functions
let ExtendsOrEquals = #(ConcreteType, ConcreteType) => Boolean
let Union = #(ConcreteType, ConcreteType) => ConcreteType | fail
let Intersection = #(ConcreteType, ConcreteType) => ConcreteType
let SubC = #(Type, Type) => List<Constriant>

'Structures:
let UpperBounds = Map<TypeVariable, Set<Type>>
let LowerBounds = Map<TypeVariable, Set<Type>>
let Reflexives = List<Constriant>


While Constriants is not empty, take a relation rel
  'Case1
  if (rel is (left: TypeVariable, right: TypeVariable) and
           Reflexives does not have an entry with (left, right)) {

    let found1 = false
    let found2 = false
    for (ab in Reflexives)
      // apply a >= b, b >= c then a >= c rule
      if (ab.right == rel.left)
        found1 = true
        add (ab.left, rel.right) to Reflexives
        union and set upper bounds of ab.left
          with upper bounds of rel.right

      if (ab.left == rel.right)
        found2 = true
        add (rel.left, ab.right) to Reflexives
        intersect and set lower bounds of ab.right
          with lower bounds of rel.left

    if !found1
        union and set upper bounds of rel.left
          with upper bounds of rel.right
    if !found2
        intersect and set lower bounds of rel.right
          with lower bounds of rel.left

    add Constriant(rel.left, rel.right) to Reflexives

    for each lb in LowerBounds of rel.left
      for each ub in UpperBounds of rel.right
        add all SubC(lb, ub) to Constriants
  }
  'Case2
  If rel is (left: TypeVariable, right: ConcreteType) and
      UpperBound of rel.left does not contain rel.right {
    found = false
    for each ab in Reflexives
      if (ab.right == rel.left)
        found = true
        union and set upper bounds of ab.left with rel.right
    if !found
        union the upper bounds of rel.left with rel.right
    for each lb in LowerBounds of rel.left
      add all SubC(lb, rel.right) to Constriants
  }
  'Case3
  If rel is (left: ConcreteType, right: TypeVariable) and
      LowerBound of rel.right does not contain rel.left {
    found = false;
    for each ab in Reflexives
      if (ab.left == rel.right)
         found = true;
         intersect and set lower bounds of ab.right with rel.left
    if !found
       intersect and set lower bounds of rel.right with rel.left
    for each ub in UpperBounds of rel.right
       add each SubC(rel.left, ub) to Constriants
  }
  'Case4
  if rel is (left: ConcreteType, Right: ConcreteType) and
      !ExtendsOrEquals(rel.left, rel.right)
  fail
}
