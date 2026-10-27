module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24D4
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24Shape

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Fi24 (J lvl)

set_option linter.unusedSectionVars false


namespace TabFi24

theorem shapeRkAt_s0 : ShapeRkAt 3 (LeafType 3) (fun _ _ => True) s0 := by
  haveI : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  obtain ⟨hcard, hsimple, hnab, hleaf⟩ := fiN_facts
  refine shapeRkAt_of_simple_pindex Nat.prime_three
    (fun _ _ _ _ e h => LeafType.of_equiv e h) (fun _ _ _ _ _ h => h) fiN
    (fiN_le_lvl_two.trans lvl_two_le_cent0) hsimple hnab (k := 2) ?_ ?_ ?_ hleaf trivial
  · rw [hcard]
    norm_num
  · rw [card_cent0, hcard]
    norm_num
  · rw [card_cent0]
    decide

theorem shapeRkAt_fi24Rep3_zero :
    ShapeRkAt 3 (LeafType 3) (fun _ _ => True) (fi24Rep3 0) := by
  haveI : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  obtain ⟨c, hc⟩ := isConj_iff.1 isConj_rep0_s0
  have h := ShapeRkAt.of_equiv Nat.prime_three (fun _ _ _ _ e h => LeafType.of_equiv e h)
    (fun _ _ _ _ _ h => h) (MulAut.conj c⁻¹) shapeRkAt_s0
  have hk : (MulAut.conj c⁻¹) s0 = fi24Rep3 0 := by
    rw [← hc, MulAut.conj_apply]
    show c⁻¹ * (c * wordElt [18] * c⁻¹) * c⁻¹⁻¹ = wordElt [18]
    group
  rw [hk] at h
  exact h

end TabFi24

end CFSG.HardMathSupport.Dickson.I271
