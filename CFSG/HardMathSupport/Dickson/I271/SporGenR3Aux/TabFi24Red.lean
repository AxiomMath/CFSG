module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24ThreeClasses
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SimpleLeaf
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Pair

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Fi24 (J)

section Reduction


theorem centShapeRk_J_of_reps (hcl : Fi24ThreeClasses)
    (hrep : ∀ i : Fin 5, ShapeRkAt 3 (LeafType 3) (fun _ _ => True) (fi24Rep3 i)) :
    CentShapeRk 3 (LeafType 3) (fun _ _ => True) ↥J := by
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → LeafType 3 T → LeafType 3 T' :=
    fun _ _ _ _ e h => LeafType.of_equiv e h
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  intro k hk1 hkp
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  have hord : orderOf k = 3 := orderOf_eq_prime hkp hk1
  obtain ⟨i, hconj⟩ := hcl k hord
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have h := ShapeRkAt.of_equiv Nat.prime_three hGood hRk (MulAut.conj c⁻¹) (hrep i)
  have hk : (MulAut.conj c⁻¹) (fi24Rep3 i) = k := by
    rw [← hc, MulAut.conj_apply]
    group
  rw [hk] at h
  exact h

theorem leafShape_Fi24_of_reps (hcl : Fi24ThreeClasses)
    (hrep : ∀ i : Fin 5, ShapeRkAt 3 (LeafType 3) (fun _ _ => True) (fi24Rep3 i)) :
    LeafShape .Fi24Prime 3 := by
  haveI : Finite ↥J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  have hJ := centShapeRk_J_of_reps hcl hrep
  have hC : CentShapeRk 3 (LeafType 3) (fun _ _ => True)
      (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime) := by
    haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime) :=
      Finite.of_equiv ↥J CFSG.Sporadic.Fi24.fi24EquivJ.symm.toEquiv
    exact CentShapeRk.of_equiv (Q := ↥J) (Q' := CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime)
      Nat.prime_three (fun _ _ _ _ e h => LeafType.of_equiv e h) (fun _ _ _ _ _ h => h)
      CFSG.Sporadic.Fi24.fi24EquivJ.symm hJ
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime) :=
    Finite.of_equiv ↥J CFSG.Sporadic.Fi24.fi24EquivJ.symm.toEquiv
  exact CentShape.of_centShapeRk hC

end Reduction

end CFSG.HardMathSupport.Dickson.I271
