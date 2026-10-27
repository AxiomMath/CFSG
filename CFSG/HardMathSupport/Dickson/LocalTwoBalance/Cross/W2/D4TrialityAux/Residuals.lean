module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.GraphA
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.GraphFieldA
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.FieldA
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.GraphFaithful

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent

section Residuals


theorem d4FieldStdNormalCop_holds :
    ∀ (ℓ e : ℕ) [Fact ℓ.Prime], ℓ ≠ 3 → 1 ≤ e → ∀ (K : Type) [Field K] [Finite K] [CharP K ℓ],
      Nat.card K = ℓ ^ (e * 3) → ∀ T : K ≃+* K, (∀ c, T c = c ^ (ℓ ^ e)) →
        NoNormalCop 3 (fixSub (twistedEntrywiseAut TwistTag.D4 0 T)) := by
  intro ℓ e _ hℓ3 he K _ _ _ hK T hT
  exact noNormalCop_fixSub_entrywise hℓ3 he hK T hT

theorem d4GraphFieldStdFaithful_holds :
    ∀ (ℓ e : ℕ) [Fact ℓ.Prime], ℓ ≠ 3 → 1 ≤ e → ∀ (K : Type) [Field K] [Finite K] [CharP K ℓ],
      Nat.card K = ℓ ^ (e * 3) → ∀ T : K ≃+* K, (∀ c, T c = c ^ (ℓ ^ e)) →
        ∀ j : ℤ, (j % 3 = 1 ∨ j % 3 = 2) → FaithfulAt 3 (twistedEntrywiseAut TwistTag.D4 j T) := by
  intro ℓ e _ hℓ3 he K _ _ _ hK T hT j hj
  have hK' : Nat.card K = (ℓ ^ e) ^ 3 := by rw [hK, ← pow_mul]
  have hT3 : ∀ c, T (T (T c)) = c := fun c => ringEquiv_cube_apply_eq hK' hT c
  exact faithfulAt_x4 T hT3 j hj

theorem d4FieldStdFaithful_holds (ℓ e : ℕ) [Fact ℓ.Prime] (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (hK : Nat.card K = ℓ ^ (e * 3)) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e)) :
    FaithfulAt 3 (twistedEntrywiseAut TwistTag.D4 0 T) := by
  have hK' : Nat.card K = (ℓ ^ e) ^ 3 := by rw [hK, ← pow_mul]
  have hT3 : ∀ c, T (T (T c)) = c := fun c => ringEquiv_cube_apply_eq hK' hT c
  have hT3' : T ^ 3 = 1 := RingEquiv.ext fun c => by simpa [pow_succ, RingAut.mul_apply] using hT3 c
  have e0 : twistedEntrywiseAut TwistTag.D4 0 T = entrywiseAdjointAut Tag.D4 T := by
    unfold twistedEntrywiseAut
    rw [zpow_zero, one_mul]
    rfl
  rw [e0]
  exact faithfulAt_entrywise T hT3'

theorem d4GraphFaithful_holds :
    ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K →
      ∀ (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ), (ε = 1 ∨ ε = 2) →
        (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) ^ 3 = 1 →
          FaithfulAt 3 (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) := by
  intro K _ _ hK3 g a ε hε hα
  rcases hε with rfl | rfl
  · exact faithfulAt_graphOne hK3 g a hα
  · obtain ⟨g', a', hinv⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.graphType_inv_normalForm g a
    have hα' : (MulAut.conj g' * (exactNormalAut Tag.D4 K a' 1 0 * d4Graph K 1)) ^ 3 = 1 := by
      rw [← hinv, inv_pow, hα, inv_one]
    have h1 := faithfulAt_graphOne hK3 g' a' hα'
    rw [← hinv] at h1
    have h2 := h1.inv
    rwa [inv_inv] at h2

theorem d4GraphCoreFree_holds : D4GraphCoreFree := by
  intro K _ _ hK3 g a ε hε hα
  exact coreFreeAt_of_parts (noNormalCop_fixSub_graphType trialityThreeRest_holds hK3 g a hε hα)
    (d4GraphFaithful_holds K hK3 g a ε hε hα)

theorem d4GraphFieldStdCoreFree_holds : D4GraphFieldStdCoreFree := by
  intro ℓ e _ hℓ3 he K _ _ _ hK T hT j hj
  exact coreFreeAt_of_parts (noNormalCop_fixSub_twistedEntrywise hℓ3 he hK T hT j hj)
    (d4GraphFieldStdFaithful_holds ℓ e hℓ3 he K hK T hT j hj)

theorem d4FieldStdCoreFree_holds : D4FieldStdCoreFree := by
  intro ℓ e _ hℓ3 he K _ _ _ hK T hT
  exact coreFreeAt_of_parts (d4FieldStdNormalCop_holds ℓ e hℓ3 he K hK T hT)
    (d4FieldStdFaithful_holds ℓ e K hK T hT)

theorem d4TrialityCoreFree_holds : D4TrialityCoreFree :=
  d4TrialityCoreFree_of_outerCoreFree
    (d4OuterCoreFree_of_classes d4GraphCoreFree_holds d4GraphFieldStdCoreFree_holds
      d4FieldStdCoreFree_holds)

end Residuals

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
