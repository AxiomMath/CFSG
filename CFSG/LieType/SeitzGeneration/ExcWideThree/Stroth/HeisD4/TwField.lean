module

public import CFSG.CharacterTheory.Semidihedral.FixedFieldData

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4

open CFSG.Semidihedral.FixedFieldData

theorem exists_fixedField_data {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀) (_ : Algebra K₀ (AlgebraicClosure K)),
      IsAlgClosure K₀ (AlgebraicClosure K) ∧ Nat.card K₀ = ℓ ^ f ∧ ringChar K₀ = ℓ := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hKc : Fintype.card K = ℓ ^ (2 * f) := by
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm]
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow hKc
  have hq2 : 2 ≤ ℓ ^ f := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  have hKc' : Fintype.card K = (ℓ ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have hσ2 : σ ^ 2 = 1 := by
    refine RingEquiv.ext fun c => ?_
    change σ (σ c) = c
    rw [hσ, hσ, ← pow_mul, ← sq, ← hKc']
    exact FiniteField.pow_card c
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hall : ∀ c : K, c ^ (ℓ ^ f) = c := fun c => by
      rw [← hσ, h1]
      rfl
    have hdeg : (Polynomial.X ^ (ℓ ^ f) - Polynomial.X : Polynomial K).natDegree = ℓ ^ f :=
      FiniteField.X_pow_card_sub_X_natDegree_eq K hq2
    have hne : (Polynomial.X ^ (ℓ ^ f) - Polynomial.X : Polynomial K) ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero K hq2
    have hsub : (Finset.univ : Finset K).val ⊆
        (Polynomial.X ^ (ℓ ^ f) - Polynomial.X : Polynomial K).roots := by
      intro c _
      rw [Polynomial.mem_roots hne]
      simp [Polynomial.IsRoot, hall c]
    have hle := Polynomial.card_le_degree_of_subset_roots hsub
    rw [hdeg, Finset.card_univ, hKc'] at hle
    nlinarith
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf σ = 2 := orderOf_eq_prime hσ2 hσ1
  set A : Subgroup (K ≃+* K) := Subgroup.zpowers σ with hA
  have hcardK : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hcard : Nat.card (FixedPoints.subfield A K) = ℓ ^ f := by
    have h := fixedSubfield_card ℓ (2 * f) K hcardK A
    rw [hA, Nat.card_zpowers, hord, Nat.mul_div_cancel_left f (by norm_num : 0 < 2)] at h
    exact h
  haveI : Algebra.IsAlgebraic (FixedPoints.subfield A K) K := Algebra.IsAlgebraic.of_finite _ _
  haveI : CharP (FixedPoints.subfield A K) ℓ :=
    RingHom.charP (algebraMap (FixedPoints.subfield A K) K)
      (algebraMap (FixedPoints.subfield A K) K).injective ℓ
  exact ⟨↥(FixedPoints.subfield A K), inferInstance, inferInstance, inferInstance,
    IsAlgClosure.ofAlgebraic (FixedPoints.subfield A K) K (AlgebraicClosure K), hcard,
    ringChar.eq _ ℓ⟩

end CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4
