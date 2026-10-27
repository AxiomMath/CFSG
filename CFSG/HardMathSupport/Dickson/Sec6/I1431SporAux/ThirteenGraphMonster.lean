module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.ThirteenGraph
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.ThirteenKerTwo
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.ThirteenShapes
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.ThirteenBExports
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Fi23PinThirteen
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.ThThirteen

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Subgroup CFSG.Blueprint CFSG.Monster.Existence CFSG.Monster.GMS

section Existence


theorem thirteenGraphData_of_existence {G : Type} [Group G] {a z : G} (ha : orderOf a = 2)
    (hA : ∀ α, IsConj a α → IsTwoACentralizer α) (hgraph : IsTwoAGraphData a z) :
    ∃ c : Fin 9 → G, ThirteenGraphData (fun s : NativeSporadic.B => BabyInv 0 s) a c := by
  obtain ⟨htrans, c, -, -, -, -, hord, hcov, -, hshape, -⟩ := hgraph
  refine ⟨c, ?_⟩
  exact
    { trans := htrans
      ord := hord
      cov := hcov
      shape := hshape
      kerTwo := fun u hu => exists_kerTwo_of_isTwoACentralizer
        ((orderOf_eq_of_isConj_thirteen hu).symm.trans ha) (hA u hu)
      s19 := fun H h => nineteen_dvd_of_twoPointShape_one h
      s13 := fun H i hi h => not_dvd_thirteen_of_twoPointShape hi h
      fi := fun H h => by
        obtain ⟨e⟩ := h
        have h1 := fi23_thirteen_card
        have e1 := @card_orderOf_thirteen_congr H NativeSporadic.Fi23 _ _ e
        have e2 := Nat.card_congr e.toEquiv
        rw [e1, e2]
        exact h1
      th := fun H h => by
        obtain ⟨e⟩ := h
        have h1 := th_thirteen_card
        have e1 := @card_orderOf_thirteen_congr H NativeSporadic.Th _ _ e
        have e2 := Nat.card_congr e.toEquiv
        rw [e1, e2]
        exact h1
      b13 := fun y hy => b13_exports hy
      b19 := fun f hf h19 => babyInv_zero_of_nineteen_dvd hf h19 }

theorem ncard_invComm_le_of_existence {G : Type} [Group G] [Finite G] {a z : G}
    (ha : orderOf a = 2) (hA : ∀ α, IsConj a α → IsTwoACentralizer α)
    (hgraph : IsTwoAGraphData a z) {x : G} (hx : orderOf x = 13)
    (hA1 : ∀ u : G, u * u = 1 → u ≠ 1 → u * x = x * u → IsConj a u) :
    (invComm x).ncard ≤ 451 := by
  obtain ⟨c, D⟩ := thirteenGraphData_of_existence ha hA hgraph
  exact ncard_invComm_le D hx hA1

end Existence

end CFSG.HardMathSupport.Dickson.Sec6.I1431
