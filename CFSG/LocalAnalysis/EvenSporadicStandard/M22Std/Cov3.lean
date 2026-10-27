module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.M22CoverCheck

public section

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.QuasithinUnique.Ch1.M22Cover CFSG.QuasithinUnique.Ch1.TitsCover
open CFSG.Monster.B.Co2.Native

@[expose] def eqns0 (d : CovData) : List Eqn :=
  let T := d.tab
  let edges : List (ℕ × Fin 3) :=
    (List.range d.nV).flatMap fun v => (List.finRange 3).map fun i => (v, i)
  let isTree : ℕ × Fin 3 → Bool := fun p => T.word (T.tgt p.1 p.2) == T.word p.1 ++ [p.2]
  (edges.filter isTree).map (fun p => Eqn.tree p.1 p.2) ++
    (edges.filter (fun p => !isTree p)).flatMap (fun p =>
      (List.finRange 3).map fun j => Eqn.trans
        (posW (T.word p.1) ++ [(p.2, true)] ++ invW (T.word (T.tgt p.1 p.2))) 0 (T.tgt 0 j)) ++
    ((List.range d.blocks.length).flatMap fun b =>
      ((d.blocks[b]!).rhos).map fun ρ => Eqn.fus b ρ)

theorem eqns_eq_eqns0_append (d : CovData) : d.eqns = eqns0 d ++ d.free.map Eqn.free := rfl

@[expose] def forms0 (d : CovData) : List ℕ := (eqns0 d).map (Eqn.form d)

@[expose] def sqWalk (d : CovData) (v₁ v₂ : ℕ) : List Letter :=
  posW (d.tab.word v₁) ++ posW (d.tab.word v₁) ++ invW (d.tab.word v₂) ++ invW (d.tab.word v₂)

@[expose] def sqCheck (d : CovData) (v₁ v₂ : ℕ) : Bool :=
  (d.tab.walkEnd 0 (sqWalk d v₁ v₂) == 0) &&
    (reduceF (gePivots (d.M + 5) d.M (forms0 d)) (d.M + 5)
      (formOf (d.tab.walkEdges 0 (sqWalk d v₁ v₂)) ^^^ 2 ^ 189) == 0) &&
    decide (v₁ < d.nV) &&
    eqA 22 (compA 22 (compA 22 d.elaTab[v₁]! d.elaTab[v₁]!)
      (compA 22 d.elaTab[v₁]! d.elaTab[v₁]!)) (idA 22) &&
    !eqA 22 (compA 22 d.elaTab[v₁]! d.elaTab[v₁]!) (idA 22)

end CFSG.EvenSporadicStandard.M22Std
