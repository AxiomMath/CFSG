module

public import CFSG.LieType.Multipliers.U62Data
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Fischer.T46SimpleCert
public import CFSG.LieType.Multipliers.CoverWords

@[expose] public section

namespace CFSG.LieType.Multipliers.U62

open CFSG.Fischer CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable
  CFSG.Fischer.Classification.Recognition CFSG.Sporadic.Fi22.Native

def expand (v : List (Fin 5 × Bool)) : List ℤ :=
  v.flatMap fun l => if l.2 then genWord l.1 else (genWord l.1).reverse

def relWords : List (List (Fin 5 × Bool)) :=
  rels ++ (List.finRange 5).map fun i => commWords (coverPairs i) ++ [(i, false)]

def bridgeCheck : Bool :=
  relWords.all (fun r => t46FixAll (wordT 693 t46Gen (expand r))) &&
    t46TblEq (wordT 693 t46Gen (expand xWord)) t46XT &&
    t46TblEq (wordT 693 t46Gen (expand yWord)) t46YT &&
    allIn 0 46 (fun k => t46FixAll (compT 693 (t46Gen ((k : ℤ) + 1)) (t46Gen ((k : ℤ) + 1))))

abbrev rels₁ := restrictWords (subsetOf _ [0, 1, 2, 3]) rels

abbrev rels₂ := restrictWords (subsetOf _ [0, 1, 2]) rels₁

abbrev rels₃ := restrictWords (subsetOf _ [0, 1]) rels₂

end CFSG.LieType.Multipliers.U62
