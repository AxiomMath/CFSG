module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23ThreeA

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271.TabFi23

open CFSG.Open CFSG.Sporadic.Fi23 CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23

section Assembly


theorem shapeRkAt_t3 (hC : PConstrainedShape 3 (Subgroup.centralizer ({t3 2} : Set J)))
    (i : Fin 4) : ShapeRkAt 3 (LeafType 3) (fun _ _ => True) (t3 i) := by
  fin_cases i
  · exact shapeRkAt_t3_zero
  · exact Or.inl pConstrained_t3_one
  · exact Or.inl hC
  · exact Or.inl pConstrained_t3_three


theorem centShapeRk_J23 (hC : PConstrainedShape 3 (Subgroup.centralizer ({t3 2} : Set J))) :
    CentShapeRk 3 (LeafType 3) (fun _ _ => True) J := by
  haveI := finite_J23
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → LeafType 3 T → LeafType 3 T' :=
    fun _ _ _ _ e h => LeafType.of_equiv e h
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  intro k hk1 hk3
  have hord : orderOf k = 3 := orderOf_eq_prime hk3 hk1
  obtain ⟨i, hconj⟩ := fi23_three_classes k hord
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have h := @ShapeRkAt.of_equiv ↥J ↥J _ finite_J23 inferInstance 3 Nat.prime_three
    (LeafType 3) (fun _ _ => True) hGood hRk finite_J23 (MulAut.conj c⁻¹) (t3 i)
    (shapeRkAt_t3 hC i)
  have hk : (MulAut.conj c⁻¹) (t3 i) = k := by
    rw [MulAut.conj_apply, ← hc]
    group
  rw [hk] at h
  exact h

theorem leafShape_Fi23_of (hC : PConstrainedShape 3 (Subgroup.centralizer ({t3 2} : Set J))) :
    LeafShape .Fi23 3 := by
  haveI := finite_J23
  haveI : Finite CFSG.Blueprint.NativeSporadic.Fi23 :=
    Finite.of_equiv J (fi23EquivJ.symm.toEquiv)
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → LeafType 3 T → LeafType 3 T' :=
    fun _ _ _ _ e h => LeafType.of_equiv e h
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  exact CentShape.of_centShapeRk (@CentShapeRk.of_equiv ↥J CFSG.Blueprint.NativeSporadic.Fi23
    inferInstance finite_J23 inferInstance 3 Nat.prime_three (LeafType 3) (fun _ _ => True)
    hGood hRk inferInstance fi23EquivJ.symm (centShapeRk_J23 hC))

end Assembly

end CFSG.HardMathSupport.Dickson.I271.TabFi23
