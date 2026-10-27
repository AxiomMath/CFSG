module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Hyp
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Natural

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

namespace P614I

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell
open scoped commutatorElement

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem not_isC134Case5 (h : CampbellHyp X K R P) :
    ¬ CFSG.Quasithin.IsC134Case5 X (pCoreOf 2 P) K := by
  rintro ⟨-, h5⟩
  obtain ⟨hZ, -⟩ := h5 R ⟨h.R_le, h.R_two, h.R_sylow⟩ h.pCore_P_le_R
  rw [omegaOneCenterOf_eq_omegaCenter] at hZ
  have hXP : X ≤ P := fun g hg => h.cent_le ⟨hg, mem_centralizer_iff.2 fun z hz =>
    ((mem_centralizer_iff.1 (mem_inf.1 (hZ hz)).2) g hg).symm⟩
  have h7 := h.P_index
  rw [subgroupOf_eq_top.2 hXP, index_top] at h7
  omega

theorem blockConclusion_of_natural (h : CampbellHyp X K R P)
    (hN : HasNatSection K (CFSG.Quasithin.c134Q X K) ⊥) :
    ∃ A₀ B₀ : Subgroup A, A₀ ≤ B₀ ∧ B₀ ≤ omegaCenter (K ⊓ pCoreOf 2 X) ∧
      X ≤ normalizer (A₀ : Set A) ∧ X ≤ normalizer (B₀ : Set A) ∧
      K ≤ centralizer (A₀ : Set A) ∧
      (∀ w ∈ K ⊓ pCoreOf 2 X, ∀ k ∈ K, w * k * w⁻¹ * k⁻¹ ∈ B₀) ∧
      A₀.relIndex B₀ = 8 ∧
      ∀ g ∈ X, (∀ u ∈ B₀, g * u * g⁻¹ * u⁻¹ ∈ A₀) → g ∈ pCoreOf 2 X := by
  set Q := CFSG.Quasithin.c134Q X K
  set B₀ := ⁅omegaCenter (K ⊓ pCoreOf 2 X), K⁆
  obtain ⟨hbotK, hbotX⟩ := bot_conditions X K
  obtain ⟨-, b, -, -, hbker, -, -, hbB₀⟩ := h.natData_B0 (D := Q) (C₀ := ⊥) inf_le_left hbotK hN
  have hQB : Q ≤ B₀ := by
    intro q hq
    obtain ⟨u, hu, huv⟩ := hbB₀ (Multiplicative.toAdd (b ⟨q, hq⟩))
    have hb : b u = b ⟨q, hq⟩ := Multiplicative.toAdd.injective huv
    have h1 : u * (⟨q, hq⟩ : ↥Q)⁻¹ ∈ b.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hb]
      exact mul_inv_cancel _
    rw [hbker, mem_subgroupOf, mem_bot] at h1
    have h2 : (u : A) = q := by simpa [mul_inv_eq_one] using h1
    exact h2 ▸ hu
  refine ⟨B₀ ⊓ ⊥, B₀, inf_le_left, h.commutator_W_le,
    normalizer_inf_of_normalizes h.normalizer_B0 hbotX, h.normalizer_B0, ?_, ?_,
    h.relIndex_eight_of_hasNatSection inf_le_left hbotK hN,
    h.faithful_of_hasNatSection inf_le_left hbotK hbotX hN⟩
  · intro k hk
    rw [mem_centralizer_iff]
    intro a ha
    exact (mem_centralizer_iff.1 (hbotK hk)) a ha.2
  · intro w hw k hk
    have hc : ⁅w, k⁆ ∈ Q := commutator_mem_commutator (mem_inf.1 hw).2 hk
    rw [commutatorElement_def] at hc
    exact hQB hc

end P614I

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
