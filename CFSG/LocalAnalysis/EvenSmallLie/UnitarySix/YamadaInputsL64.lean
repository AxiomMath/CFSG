module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsL64Gen
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndDefs
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsKinds

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaInputs

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ABGLocalTools
open scoped MatrixGroups

theorem card_SL_six_two : Nat.card SL(6, ZMod 2) = YamadaEnd.orderSL62 := by
  rw [card_SL_eq (by norm_num), Nat.card_eq_fintype_card, ZMod.card]
  decide

theorem commutator_top_SL_six_two :
    ⁅(⊤ : Subgroup SL(6, ZMod 2)), (⊤ : Subgroup SL(6, ZMod 2))⁆ = ⊤ := by
  have := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := ZMod 2)
    (n := 6) (by norm_num)
  have h := this.commutator_eq_top
  rwa [commutator_def] at h

theorem l64CentralizerInput : YamadaEnd.L64CentralizerInput := by
  intro G _ _ F _ _ hF K ψ hψ hker t ht htN h17
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨A, σ, ε, hε, hA, hcases⟩ := exists_cases (by norm_num) hF ψ hψ hker htN htt
  have hsmall : ∀ Q ≤ K ⊓ centralizer ({t} : Set G), IsPGroup 2 Q →
      Nat.card Q < Nat.card F ^ (3 * 3) := fun Q hQ h2 => by
    have := h17 Q hQ h2
    rw [hF]
    omega
  have hσ1 : σ ≠ 1 := field_ne_one_of_small hF (Or.inr rfl) rfl ψ hker htt hε hA hsmall
  have : CharP F 2 := charP_two_of_card_four hF
  rcases hcases with ⟨hσ, -⟩ | ⟨-, hσ, H, hH⟩
  · exact absurd hσ hσ1
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  ·
    obtain ⟨θ, hθ, hrange⟩ := exists_field_centralizer (by norm_num) ψ hψ hker hσ hH
    have hcard : Nat.card (K ⊓ centralizer ({t} : Set G) : Subgroup G) = YamadaEnd.orderSL62 := by
      rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hθ).toEquiv, card_SL_six_two]
    refine ⟨?_, Or.inl hcard, fun hne => absurd hcard hne⟩
    rw [← hrange, MonoidHom.range_eq_map]
    exact commutator_map_eq_of_perfect θ commutator_top_SL_six_two
  ·
    obtain ⟨φ, hφ, hφker, hact⟩ := exists_std_graphField hF ψ hψ hker hσ hH
    have hker' : φ.ker ≤ center SL(6, F) := hφker ▸ hker
    have hC := centralizer_eq_slUnitary hF (by norm_num) φ hφ hker' hσ hact
    have hσ' : ∀ c, (σ : F →+* F) c = c ^ 2 := hσ
    refine ⟨?_, ?_, fun _ S₀ P₀ hS₀ hP₀ hSP =>
      eq_sup_normalizer_of_graphField hF φ hφ hker' hσ hact hS₀ hP₀ hSP⟩
    · rw [hC]
      exact commutator_map_eq_of_perfect _ (commutator_slUnitary_six hF hσ')
    · have h1 := card_map_mul_card_ker' φ
        (hker'.trans (center_le_slUnitary hF hσ' (revGL 6 F : Matrix (Fin 6) (Fin 6) F)))
      rw [← hC, card_slUnitary_six hF hσ'] at h1
      have h3 := card_ker_dvd_three hF (by norm_num) φ hker'
      rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
      · rw [h, mul_one] at h1
        exact Or.inr (Or.inl h1)
      · rw [h] at h1
        refine Or.inr (Or.inr ?_)
        change _ = 9196830720
        omega

end CFSG.EvenSmallLie.UnitarySix.YamadaInputs
