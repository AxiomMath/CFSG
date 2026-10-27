module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleBasic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearGraphFieldDescent

public section

namespace CFSG.ComponentClassification.RankTwoHypIIL3

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoHypIIY

variable {K : Type} [Field K]

theorem rigidInvolution_of_not_mem [Finite K] {m : ℕ} (hm : 3 ≤ m) (hK : Nat.card K = 2 ^ m)
    {t : MulAut (projectiveSL 3 K)}
    (htX : t ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range)
    (ht2 : t ^ 2 = 1) :
    RigidInvolution (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range t := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  set X := (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range with hXdef
  have hXn : X.Normal := (autModel_mulAut (center_projectiveSL_three_eq_bot K)).normal
  have hconj : ∀ {t' w t₀ : MulAut (projectiveSL 3 K)}, t' ∉ X → t' ^ 2 = 1 →
      t' = w * t₀ * w⁻¹ → t₀ ∉ X ∧ t₀ ^ 2 = 1 := by
    intro t' w t₀ h1 h2 h
    subst h
    refine ⟨fun h0 => h1 (hXn.conj_mem t₀ h0 w), ?_⟩
    rwa [conj_pow, conj_eq_one_iff] at h2
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 t
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  ·
    rw [pow_zero, mul_one] at htX ht2 ⊢
    by_cases hσ : σ = 1
    ·
      exfalso
      subst hσ
      rw [map_one, mul_one] at htX ht2
      by_cases h1 : conjAut 3 K A = 1
      · exact htX (h1 ▸ X.one_mem)
      · obtain ⟨s, -, hs⟩ := OutcomeLocal.exists_involution_eq_conjAut le_rfl A ht2 h1
        exact htX ⟨s, hs.symm⟩
    ·
      obtain ⟨-, -, H, hH⟩ :=
        even_linear_field_involution_descent (n := 3) (by omega) hK le_rfl A σ hσ ht2
      obtain ⟨h0X, h02⟩ := hconj htX ht2 hH
      rw [hH]
      exact (rigidInvolution_fieldAut σ h0X h02).conj hXn _
  ·
    rw [pow_one] at htX ht2 ⊢
    by_cases hσ : σ = 1
    ·
      subst hσ
      rw [map_one, mul_one] at htX ht2 ⊢
      obtain ⟨-, ⟨H, C, -, hH, hC⟩, -⟩ :=
        UnitaryHigher.even_linear_pure_graph_involution_normal_forms (n := 3) (by omega) hK
          le_rfl A ht2
      have hC1 : C = 1 := by
        rcases hC with ⟨hC1, -⟩ | ⟨r, hr, -⟩
        · exact Units.ext hC1
        · omega
      subst hC1
      rw [map_one, one_mul] at hH
      obtain ⟨h0X, -⟩ := hconj htX ht2 hH
      rw [hH]
      exact (rigidInvolution_dualAut (by omega) hK h0X).conj hXn _
    ·
      obtain ⟨⟨e, he⟩, hσx, H, hH⟩ :=
        UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two (by omega) hK le_rfl
          A σ hσ ht2
      have hud : UnitaryFieldData 2 e K := ⟨Nat.prime_two, by omega, by rw [hK, he, two_mul]⟩
      have hσbar : ∀ x, σ x = hud.bar x := fun x => by
        rw [hσx, UnitaryFieldData.bar_apply, show m / 2 = e by omega]
      obtain ⟨h0X, h02⟩ := hconj htX ht2 hH
      rw [hH]
      exact (rigidInvolution_graphField hud (by omega) σ hσbar h0X h02).conj hXn _

theorem hypII_of_projectiveSL_three [Finite K] {m : ℕ} (hm : 3 ≤ m) (hK : Nat.card K = 2 ^ m)
    {A : Type*} [Group A] (hA : commutator A = ⊤) (e : A ⧸ center A ≃* projectiveSL 3 K) :
    AS76b.HypII A := by
  have : Finite (MulAut (projectiveSL 3 K)) := finite_mulAut_projectiveSL
  exact hypII_of_rigidInvolution (autModel_mulAut (center_projectiveSL_three_eq_bot K))
    (fun _ htX ht2 => rigidInvolution_of_not_mem hm hK htX ht2) hA e

theorem hypII_L3 {A : Type} [Group A] (hA : commutator A = ⊤) {m : ℕ} (hm : 3 ≤ m)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel (A ⧸ center A) .PSL 3 2 m) :
    AS76b.HypII A := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact hypII_of_projectiveSL_three hm hK hA
    (e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)))

end CFSG.ComponentClassification.RankTwoHypIIL3
