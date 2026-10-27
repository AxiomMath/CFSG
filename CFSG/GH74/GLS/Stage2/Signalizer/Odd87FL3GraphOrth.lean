module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3GraphThree
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Orth3Mod

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.KGroups.L3Eps
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F]

theorem fl3g_ringEquiv_eq_one_of_sq {σ : F ≃+* F} (h2 : (2 : F) ≠ 0)
    (h : ∀ t : F, σ (t ^ 2 - 1) = t ^ 2 - 1) : σ = 1 := by
  have hsq : ∀ t : F, σ (t ^ 2) = t ^ 2 := by
    intro t
    have := h t
    rw [map_sub, map_one] at this
    linear_combination this
  have hone : ∀ y : F, σ y = y := by
    intro y
    have h1 : σ y ^ 2 = y ^ 2 := by rw [← map_pow]; exact hsq y
    have h1' : σ (1 + y) ^ 2 = (1 + y) ^ 2 := by rw [← map_pow]; exact hsq (1 + y)
    rw [map_add, map_one] at h1'
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h3 | h3
    · exact h3
    · rw [h3] at h1'
      have h4 : 4 * y = 0 := by linear_combination -h1'
      have h5 : (4 : F) ≠ 0 := by
        have : (4 : F) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero h2 h2
      have hy : y = 0 := (mul_eq_zero.1 h4).resolve_left h5
      rw [hy, map_zero]
  ext y
  exact hone y

theorem fl3g_two_ne_zero [Finite F] (hodd : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  have : Fintype F := Fintype.ofFinite F
  have hF2 : ringChar F ≠ 2 := fun h2 => by
    have h' := (FiniteField.even_card_iff_char_two (F := F)).1 h2
    rw [Nat.card_eq_fintype_card] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega
  exact Ring.two_ne_zero hF2

theorem fl3GraphOrth_of_omega3 [Finite F] (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (R : GL (Fin 3) F) (hR : (R : Matrix (Fin 3) (Fin 3) F)ᵀ = R) :
    FL3GraphOrth R (omega3 R) where
  isometry := omega3_le_isometrySL R
  perfect := omega3_perfect hodd h5 R hR
  irred := fun W hW => omega3_irreducible hodd h5 R hR W hW
  comm := fun T hT => omega3_commutant hodd h5 R hR T hT
  traces := fun σ hσ => by
    refine fl3g_ringEquiv_eq_one_of_sq (fl3g_two_ne_zero hodd) fun t => ?_
    obtain ⟨g, hg, hgt⟩ := omega3_trace_exists hodd h5 R hR t
    have := hσ g hg
    rwa [hgt] at this
  sl2 := exists_sl2_hom hodd h5 R hR

theorem fl3_graph_false_of_five_le {A : Type} [Group A] [Finite A] {K : Subgroup A} [K.Normal]
    [Finite F] (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (e : ↥K ≃* projectiveSL 3 F)
    (φ : MulAut ↥K) (Asym : GL (Fin 3) F) (hAsym : (Asym : Matrix (Fin 3) (Fin 3) F)ᵀ = Asym)
    (hφ : ∀ k, e (φ k) = (conjAut 3 F Asym * dualAut 3 F) (e k))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Subgroup A} (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥)
    (hfaith : X ⊓ centralizer (K : Set A) = ⊥)
    (hJ : ∀ j : ↥K, φ j = j → (j : A) ∈ normalizer (X : Set A)) : False :=
  fl3_graph_false_ge5 e hodd h5 hφ hp2 hX hX1 hfaith hJ
    (fl3GraphOrth_of_omega3 hodd h5 Asym⁻¹ (transpose_inv_of_symm Asym hAsym))


theorem fl3g_twelve_dvd_card_range [Finite F] (hF3 : Nat.card F = 3) (ι : SL(2, F) →* SL(3, F))
    (hker : ∀ S, ι S = 1 → S = 1 ∨ S = -1) : 12 ∣ Nat.card ι.range := by
  have h24 := card_sl_two_of_card_three hF3
  have hmul : Nat.card ι.range * Nat.card ι.ker = 24 := by
    rw [← h24, Nat.card_congr (QuotientGroup.quotientKerEquivRange ι).toEquiv.symm]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup ι.ker).symm
  have hkerle : ι.ker ≤ Subgroup.zpowers (-1 : SL(2, F)) := by
    intro S hS
    rcases hker S hS with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers _
  have hk2 : Nat.card ι.ker ≤ 2 := by
    refine (Subgroup.card_le_of_le hkerle).trans ?_
    rw [Nat.card_zpowers]
    refine Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ?_)
    simp
  have hk1 : 1 ≤ Nat.card ι.ker := Nat.card_pos
  interval_cases hk : Nat.card ι.ker
  · omega
  · omega

theorem fl3GraphThree_of_ad_hom3 [Finite F] (hF3 : Nat.card F = 3) (R : GL (Fin 3) F)
    (hR : (R : Matrix (Fin 3) (Fin 3) F)ᵀ = R) : ∃ Ω : Subgroup SL(3, F), FL3GraphThree R Ω := by
  have hodd : Odd (Nat.card F) := by rw [hF3]; decide
  obtain ⟨ι, hiso, hirr, hcomm, hker⟩ := exists_ad_hom3 hodd R hR
  refine ⟨ι.range, ⟨?_, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨S, rfl⟩
    exact hiso S
  · intro W hW
    exact hirr W fun S v hv => hW (ι S) ⟨S, rfl⟩ v hv
  · intro T hT
    exact hcomm T fun S => hT (ι S) ⟨S, rfl⟩
  · exact fl3g_twelve_dvd_card_range hF3 ι hker

theorem fl3_graph_false {A : Type} [Group A] [Finite A] {K : Subgroup A} [K.Normal] [Finite F]
    (hodd : Odd (Nat.card F)) (h3 : 3 ≤ Nat.card F) (e : ↥K ≃* projectiveSL 3 F)
    (φ : MulAut ↥K) (Asym : GL (Fin 3) F) (hAsym : (Asym : Matrix (Fin 3) (Fin 3) F)ᵀ = Asym)
    (hφ : ∀ k, e (φ k) = (conjAut 3 F Asym * dualAut 3 F) (e k))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Subgroup A} (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥)
    (hfaith : X ⊓ centralizer (K : Set A) = ⊥)
    (hJ : ∀ j : ↥K, φ j = j → (j : A) ∈ normalizer (X : Set A)) : False := by
  by_cases h5 : 5 ≤ Nat.card F
  · exact fl3_graph_false_of_five_le hodd h5 e φ Asym hAsym hφ hp2 hX hX1 hfaith hJ
  · have hF3 : Nat.card F = 3 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    obtain ⟨Ω, hΩ⟩ := fl3GraphThree_of_ad_hom3 hF3 Asym⁻¹ (transpose_inv_of_symm Asym hAsym)
    exact fl3_graph_false_three e hF3 hφ hp2 hX hX1 hfaith hJ hΩ

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
