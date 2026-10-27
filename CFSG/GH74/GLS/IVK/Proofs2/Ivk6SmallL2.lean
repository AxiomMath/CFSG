module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6Main
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6Cent

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

section Small

theorem exists_l2Field_of_hasL2Model_small {K : Type} [Group K]
    (h : HasL2Model K (fun r => r = 5 ∨ r = 7 ∨ r = 9)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : K ≃* L2 F), L2Field F ∧
      (Nat.card F = 5 ∨ Nat.card F = 7 ∨ Nat.card F = 9) := by
  obtain ⟨p, f, hp, hf, hqe, hL⟩ := h
  rcases hL with ⟨-, hadm, F, hF, hFin, hcard, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · refine ⟨F, hF, hFin, e, ⟨?_, ?_⟩, by rw [hcard]; exact hqe⟩
    · rw [hcard]
      rcases hqe with h | h | h <;> rw [h] <;> decide
    · rw [hcard]
      rcases hqe with h | h | h <;> omega
  all_goals exact absurd h0 (by norm_num)

theorem b_ivk_6_small_L2
    {K : Type} [Group K] [Finite K] (W : Subgroup (MulAut K))
    (hL : HasL2Model K (fun r => r = 5 ∨ r = 7 ∨ r = 9)) (hW2 : IsPGroup 2 ↥W)
    (hWr : 2 ≤ CFSG.pRank 2 ↥W) (hΓ : CFSG.GH74.GLS.C3.Layer1.Bk.gammaAut K W ≠ ⊤) :
    (CFSG.IsElementaryAbelian 2 ↥W ∧ Nat.card ↥W = 4) ∧
      W ≤ (MulAut.conj : K →* MulAut K).range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, e0, hF, hq⟩ := exists_l2Field_of_hasL2Model_small hL
  have hWr' : 2 ≤ CFSG.Open.pRank 2 W := (TwoThin.pRank_two_subgroup_eq_open W) ▸ hWr
  obtain ⟨E, hEW, hEab, hE4⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 2) hWr'
  have hel : CFSG.IsElementaryAbelian 2 ↥E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).2 hEab
  have hE4' : Nat.card ↥E = 4 := by rw [hE4]; norm_num
  have hEsq : ∀ a ∈ E, a ^ 2 = 1 := fun a ha =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
  have hfour : IsFourSubgroup E := ⟨hel, hE4'⟩
  obtain ⟨T, hWT⟩ := hW2.exists_le_sylow
  obtain ⟨e, N, -⟩ := ivk_1_2a_exists F hF K e0 T
  have hEinn : E ≤ innAut K := klein_le_innAut hF hq e N hEW hE4' hEsq hΓ
  obtain ⟨e', ⟨N'⟩, hC⟩ := exists_notation_cent hF hq e hW2 hEW hfour hEinn
  have hWE : W = E := eq_of_gammaAut_ne_top hF hq e' N' hEW hW2 hfour hEinn hC hΓ
  rw [hWE]
  exact ⟨⟨hel, hE4'⟩, hEinn⟩

end Small

end CFSG.GH74.GLS.IVK.Proofs2
