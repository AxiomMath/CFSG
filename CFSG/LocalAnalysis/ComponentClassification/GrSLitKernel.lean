module

public import CFSG.Sporadic.HeldB.AlmostSimple
public import CFSG.Sporadic.Schreier.PairHePairs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrIsolatedFourEscape
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.GSLit

theorem exists_mem_of_index_le_two {X : Type*} [Group X] [Finite X] {F : Subgroup X} [F.Normal]
    (hF : F.index ≤ 2) {A : Subgroup X}
    (hA : Nonempty (A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    ∃ t ∈ A, t ≠ 1 ∧ t ∈ F := by
  obtain ⟨e⟩ := hA
  have hA4 : Nat.card A = 4 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card]
    rfl
  have hdvd : F.relIndex A ∣ F.index := relIndex_dvd_index_of_normal F A
  have hpos : 0 < F.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have hrel : F.relIndex A ≤ 2 := (Nat.le_of_dvd hpos hdvd).trans hF
  have hmul := Subgroup.card_mul_index (F.subgroupOf A)
  rw [← Subgroup.relIndex, hA4] at hmul
  have hcard : 1 < Nat.card (F.subgroupOf A) := by
    by_contra hle
    have hle' : Nat.card (F.subgroupOf A) ≤ 1 := by omega
    have : Nat.card (F.subgroupOf A) * F.relIndex A ≤ 1 * 2 := Nat.mul_le_mul hle' hrel
    omega
  have : Nontrivial (F.subgroupOf A) := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨⟨⟨t, htA⟩, htF⟩, ht1⟩ := exists_ne (1 : F.subgroupOf A)
  refine ⟨t, htA, fun h => ht1 ?_, htF⟩
  ext
  exact h

theorem deltaCore_eq_bot_of_index_le_two {X : Type*} [Group X] [Finite X] {F : Subgroup X}
    [F.Normal]
    (hF : F.index ≤ 2)
    (hcore : ∀ t ∈ F, orderOf t = 2 → pPrimeCore 2 (centralizer ({t} : Set X)) = ⊥)
    {A : Subgroup X} (hA : Nonempty (A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    (⨅ (a : X) (_ : a ∈ A) (_ : a ≠ 1),
      (pPrimeCore 2 (centralizer ({a} : Set X))).map (centralizer ({a} : Set X)).subtype) = ⊥ := by
  obtain ⟨t, htA, ht1, htF⟩ := exists_mem_of_index_le_two hF hA
  obtain ⟨e⟩ := hA
  have ht2 : orderOf t = 2 := by
    have hm : ∀ y : Multiplicative (ZMod 2), y * y = 1 := by decide
    have hsq : ∀ y : A, y * y = 1 := fun y => by
      apply e.injective
      rw [map_mul, map_one]
      exact Prod.ext (hm (e y).1) (hm (e y).2)
    have h := hsq ⟨t, htA⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact congrArg Subtype.val h) ht1
  rw [eq_bot_iff]
  intro g hg
  have hg' := mem_iInf.mp (mem_iInf.mp (mem_iInf.mp hg t) htA) ht1
  rw [hcore t htF ht2, Subgroup.map_bot] at hg'
  exact hg'

theorem deltaCore_eq_bot_of_held {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (hiso : Nonempty (GeneralizedFitting.subgroup X ≃* Blueprint.NativeSporadic.He))
    {A : Subgroup X} (hA : Nonempty (A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    (⨅ (a : X) (_ : a ∈ A) (_ : a ≠ 1),
      (pPrimeCore 2 (centralizer ({a} : Set X))).map (centralizer ({a} : Set X)).subtype) = ⊥ := by
  obtain ⟨hidx, hcore, -⟩ :=
    Sporadic.HeldB.Held_almost_simple_inner_involution_exclusion_of_outer
        CFSG.Sporadic.Schreier.AT_He_Schreier.1 hsimple hnab hiso
  have : (GeneralizedFitting.subgroup X).Normal := GeneralizedFitting.normal X
  exact deltaCore_eq_bot_of_index_le_two hidx hcore hA

end CFSG.ComponentClassification.GrSLit
