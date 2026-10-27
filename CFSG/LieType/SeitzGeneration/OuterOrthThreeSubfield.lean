module

public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldBY

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix QuadraticMap CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.ClassicalGroups.Orthogonal (ringChar_eq_of_card_eq)
open CFSG.LieType.Universal.Spin (quadOdd quadPlus quadMinus coe_quadOdd coe_quadPlus coe_quadMinus)
open CFSG.RankThree.PartOne.KCOrthogonalAut
  (matrixProjectiveImage_eq_top_odd matrixProjectiveImage_eq_top_plus
    matrixProjectiveImage_eq_top_minus)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)

theorem orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd
    (c : StatedLieTag) (hc : c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus)
    (n ℓ e p : ℕ) :
    StatedLieAdmissible c n ℓ e → p.Prime → p ≠ 2 → p ≠ ℓ →
    match c with
    | .POmegaOdd => ∀ (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = ℓ ^ e →
        Nat.card K = ℓ ^ (e * p) → ∀ σ : K ≃+* K, orderOf σ = p → (∀ x, x ∈ k ↔ σ x = x) →
          StatedClassicalModel (matrixProjectiveDerived (coordinateQuadOdd n K)) .POmegaOdd n ℓ
            (e * p) ∧
          SubfieldConclusion k (coordinateQuadOdd n k) (coordinateQuadOdd n K) σ p
            (coordinateQuadOdd_isExtension k n) (coordinateQuadOdd_fieldAut n σ)
    | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = ℓ ^ e →
        Nat.card K = ℓ ^ (e * p) → ∀ σ : K ≃+* K, orderOf σ = p → (∀ x, x ∈ k ↔ σ x = x) →
          StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus n K)) .POmegaPlus n ℓ
            (e * p) ∧
          SubfieldConclusion k (coordinateQuadPlus n k) (coordinateQuadPlus n K) σ p
            (coordinateQuadPlus_isExtension k n) (coordinateQuadPlus_fieldAut n σ)
    | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K] (k : Subfield K),
        Nat.card k = ℓ ^ e → Nat.card K = ℓ ^ (e * p) → ∀ σ : K ≃+* K, orderOf σ = p →
          ∀ hσk : (∀ x, x ∈ k ↔ σ x = x), ∀ b c' : k, (∀ s : k, s ^ 2 + b * s + c' ≠ 0) →
            StatedClassicalModel
              (matrixProjectiveDerived (coordinateQuadMinus n K hn (b : K) (c' : K))) .POmegaMinus n
              ℓ (e * p) ∧
            SubfieldConclusion k (coordinateQuadMinus n k hn b c')
              (coordinateQuadMinus n K hn (b : K) (c' : K)) σ p
              (coordinateQuadMinus_isExtension k n hn b c')
              (coordinateQuadMinus_fieldAut k n hn hσk b c')
    | _ => False := by
  intro hadm hp hp2 hpℓ
  rcases hc with rfl | rfl | rfl
  ·
    intro K _ _ k hk hK σ hσ hσk
    obtain ⟨hℓ, he, hn3, hℓ2⟩ := hadm
    have hf : 1 ≤ e * p := Nat.mul_pos he hp.pos
    have h2K : ringChar K ≠ 2 := by
      rw [ringChar_eq_of_card_eq hℓ hf hK]
      exact hℓ2
    have S := subfieldSetup_odd k hσk hp hp2 hσ hn3 (Ring.two_ne_zero h2K)
    refine ⟨⟨⟨hℓ, hf, hn3, hℓ2⟩, K, inferInstance, inferInstance, hK, ⟨(statedProjectiveReindexEquiv
      (oddIndexEquiv n) (quadOdd n K) (coe_quadOdd n K)).symm⟩⟩,
      subfield_conclusion orthogonal_high_Witt_subfield_pointwise_centralizer S ?_⟩
    intro β _
    rw [matrixProjectiveImage_eq_top_odd K n hn3 h2K]
    exact Subgroup.mem_top β
  ·
    intro K _ _ k hk hK σ hσ hσk
    obtain ⟨hℓ, he, hn4⟩ := hadm
    have hf : 1 ≤ e * p := Nat.mul_pos he hp.pos
    have S := subfieldSetup_plus k hσk hp hp2 hσ (by omega : 3 ≤ n)
    have hmodel : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus n K))
        .POmegaPlus n ℓ (e * p) :=
      ⟨⟨hℓ, hf, hn4⟩, K, inferInstance, inferInstance, hK, ⟨(statedProjectiveReindexEquiv
        (plusIndexEquiv n) (quadPlus n K) (coe_quadPlus n K)).symm⟩⟩
    refine ⟨hmodel, subfield_conclusion orthogonal_high_Witt_subfield_pointwise_centralizer S ?_⟩
    by_cases hn : n = 4
    · subst hn
      intro β hβ
      exact mem_matrixProjectiveImage_plus_four k hK hmodel (statedProjectiveReindexEquiv
        (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).symm S.hext S.hnd₀ S.hT₀ β hβ
    · intro β _
      rw [matrixProjectiveImage_eq_top_plus K n (by omega)]
      exact Subgroup.mem_top β
  ·
    intro hn K _ _ k hk hK σ hσ hσk b c' hirr
    obtain ⟨hℓ, he, hn4⟩ := hadm
    have hf : 1 ≤ e * p := Nat.mul_pos he hp.pos
    have hdeg := finrank_subfield_eq k hℓ he hk hK
    have hirrK := rootFree_of_odd_degree k hp hp2 hdeg b c' hirr
    have S := subfieldSetup_minus k hσk hp hp2 hσ hn4 hdeg b c' hirr
    refine ⟨⟨⟨hℓ, hf, hn4⟩, K, inferInstance, inferInstance, hK, (b : K), (c' : K), hirrK,
      ⟨(statedProjectiveReindexEquiv (minusIndexEquiv n hn) (quadMinus n K (b : K) (c' : K))
        (coe_quadMinus n K (b : K) (c' : K))).symm⟩⟩,
      subfield_conclusion orthogonal_high_Witt_subfield_pointwise_centralizer S ?_⟩
    intro β _
    rw [matrixProjectiveImage_eq_top_minus K n hn4 (b : K) (c' : K) hirrK]
    exact Subgroup.mem_top β

end CFSG.LieType.SeitzGeneration
