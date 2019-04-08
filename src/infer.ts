// ...
interface AstNode {
}

class Id implements AstNode {
    constructor(public name: string) { }
    toString() { return this.name }
}

class Lambda implements AstNode {
    constructor(public arg: Id, public body: AstNode) { }
    toString() { return `(fn ${this.arg} => ${this.body})` }
}

class Apply implements AstNode {
    constructor(public func: AstNode, public arg: AstNode) { }
    toString() { return `(${this.func} ${this.arg})` }
}

class Let implements AstNode {
    constructor(public variable: Id, public value: AstNode, public body: AstNode) { }
    toString() { return `(let ${this.variable} = ${this.value} in ${this.body})` }
}

class Letrec implements AstNode {
    constructor(public variable: Id, public value: AstNode, public body: AstNode) { }
    toString() { return `(letrec ${this.variable} = ${this.value} in ${this.body})` }
}

// ...
interface AstType {
}

class TypeVariable implements AstType {
    constructor() { }
    toString() {
        return this.instance ? this.instance.toString() : this.name
    }

    instance: AstType
    _name: string
    get name() {
        return this._name || (this._name = 't' + (TypeVariable.lastNameIndex ++))
    }

    static lastNameIndex = 0
}

class TypeOperator implements AstType {
    constructor(public name: string, public types: AstType[ ]) { }
    toString() {
        if (this.types.length === 0)
            return this.name
        else if (this.types.length === 2)
            return `(${this.types[0]} ${this.name} ${this.types[1]})`
        else
            return `${this.name} ${this.types.join(' ')}`
    }
}

const IntegerType = new TypeOperator('int', [ ])
const BoolType = new TypeOperator('bool', [ ])
const FunctionType = (from: AstType, to: AstType) => new TypeOperator('->', [from, to])

// ...
class TypeEnv {
    constructor(public map: { [name: string]: AstType } = { }) {
    }
    get(name: any, nonGenerics: Set<AstType>) {
        if (name in this.map)
            return fresh(this.map[name], nonGenerics)
        throw 'undefined symbol: ' + name
    }
    extend(name: any, val: AstType) {
        return new TypeEnv(Object.assign({ }, this.map, { [name]:val }))
    }
}

function analyse(node: AstNode, env: TypeEnv, nonGeneric: Set<AstType>) {
    if (node instanceof Id) {
        return env.get(node.name, nonGeneric)
    }
    else if (node instanceof Apply) {
        let funcType = analyse(node.func, env, nonGeneric),
            argType = analyse(node.arg, env, nonGeneric),
            retType = new TypeVariable()
        unify(FunctionType(argType, retType), funcType)
        return retType
    }
    else if (node instanceof Lambda) {
        let argType = new TypeVariable(),
            newEnv = env.extend(node.arg, argType),
            newGeneric = new Set(Array.from(nonGeneric).concat(argType)),
            retType = analyse(node.body, newEnv, newGeneric)
        return FunctionType(argType, retType)
    }
    else if (node instanceof Let) {
        let valType = analyse(node.value, env, nonGeneric),
            newEnv = env.extend(node.variable, valType)
        return analyse(node.body, newEnv, nonGeneric)
    }
    else if (node instanceof Letrec) {
        let newType = new TypeVariable(),
            newEnv = env.extend(node.variable, newType),
            newGeneric = new Set(Array.from(nonGeneric).concat(newType)),
            valType = analyse(node.value, newEnv, newGeneric)
            unify(newType, valType)
        return analyse(node.body, newEnv, nonGeneric)
    }
    else {
        throw 'unhandled syntax node ' + node
    }
}

function fresh(type: AstType, nonGeneric: Set<AstType>) {
    const mappings: WeakMap<AstType, AstType> = new WeakMap()

    function freshrec(type: AstType): AstType {
        type = prune(type)
        if (type instanceof TypeVariable) {
            if (isGeneric(type, nonGeneric)) {
                if (!mappings.has(type))
                    mappings.set(type, new TypeVariable())
                return mappings.get(type)
            }
            else {
                return type
            }
        }
        else if (type instanceof TypeOperator) {
            return new TypeOperator(type.name, type.types.map(freshrec))
        }
        else {
            throw 'unexpected type to fresh'
        }
    }

    return freshrec(type)
}

function unify(type1: AstType, type2: AstType) {
    let t1 = prune(type1),
        t2 = prune(type2)
    if (t1 instanceof TypeVariable) {
        if (t1 !== t2) {
            if (occursInType(t1, t2))
                throw 'recurive unification'
            t1.instance = t2
        }
    }
    else if (t1 instanceof TypeOperator && t2 instanceof TypeVariable) {
        return unify(t2, t1)
    }
    else if (t1 instanceof TypeOperator && t2 instanceof TypeOperator) {
        if (t1.name !== t2.name || t1.types.length !== t2.types.length)
            throw 'type mismatch: ' + t1 + ' != ' + t2
        t1.types.forEach((t, i) => unify(t1.types[i], t2.types[i]))
    }
    else {
        throw 'unexpected types to unify'
    }
}

function prune(type: AstType) {
    if (type instanceof TypeVariable && type.instance)
        return type.instance = prune(type.instance)
    return type
}

function isGeneric(type: TypeVariable, nonGenerics: Set<AstType>) {
    return !occursInTypes(type, Array.from(nonGenerics))
}

function occursInType(type: TypeVariable, typeIn: AstType) {
    typeIn = prune(typeIn)
    if (typeIn === type)
        return true
    else if (typeIn instanceof TypeOperator)
        return occursInTypes(type, typeIn.types)
    return false
}

function occursInTypes(type: TypeVariable, types: AstType[]) {
    return types.some(t => occursInType(type, t))
}

// ...

const type1 = new TypeVariable(),
    type2 = new TypeVariable(),
    type3 = new TypeVariable()

const env = new TypeEnv({
    pair: FunctionType(type1, FunctionType(type2, new TypeOperator('*', [type1, type2]))),
    cond: FunctionType(BoolType, FunctionType(type3, FunctionType(type3, type3))),
    zero: FunctionType(IntegerType, BoolType),
    pred: FunctionType(IntegerType, IntegerType),
    times: FunctionType(IntegerType, FunctionType(IntegerType, IntegerType)),
    0: IntegerType,
    true: BoolType,
})

function parse(node): AstNode {
    if (Array.isArray(node)) {
        var head = node[0]
        if (head === 'lambda' && node.length > 3)
            return new Lambda(new Id(node[1]), parse(['lambda'].concat(node.slice(2))))
        else if (head === 'lambda')
            return new Lambda(new Id(node[1]), parse(node[2]))
        else if (head === 'let')
            return new Let(new Id(node[1]), parse(node[2]), parse(node[3]))
        else if (head === 'letrec')
            return new Letrec(new Id(node[1]), parse(node[2]), parse(node[3]))
        else if (node.length > 2)
            return new Apply(parse(node.slice(0, -1)), parse(node.slice(-1)[0]))
        else
            return new Apply(parse(node[0]), parse(node[1]))
    }
    else {
        return new Id(node)
    }
}

;[
    ['letrec', 'factorial',
        ['lambda', 'n',
            ['cond', ['zero', 'n'],
                0,
                ['times',
                    'n',
                    ['factorial', ['pred', 'n']]
                ],
            ]
        ],
        ['factorial', 0],
    ],
    ['lambda', 'x', ['pair', ['x', 0], ['x', true]]],
    ['pair', ['f', 0], ['f', true]],
    ['let', 'f',
        ['lambda', 'x', 'x'],
        ['pair', ['f', 0], ['f', true]],
    ],
    ['lambda', 'f', ['f', 'f']],
    ['let', 'g',
        ['lambda', 'f', 0],
        ['g', 'g'],
    ],
    ['lambda', 'g',
        ['let', 'f',
            ['lambda', 'x', 'g'],
            ['pair', ['f', 0], ['f', true]],
        ],
    ],
    ['lambda', 'f', 'g', 'a',
        ['g', ['f', 'a']],
    ],
].forEach(tree => {
    let exp = parse(tree)
    try {
        console.log(exp + ' :: ' + analyse(exp, env, new Set()))
    }
    catch (e) {
        console.log(exp + ' :: ' + (e.message || e))
    }
})
