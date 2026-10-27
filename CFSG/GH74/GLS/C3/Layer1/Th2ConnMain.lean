module

public import CFSG.GH74.GLS.C3.Layer1.Th2ConnRows

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.Th2

theorem b_thm2_conn_of (hL34 : B_gen4_noL34_elem)
    (h3b : B_thm2_A7_3b) : B_thm2_conn := by
  intro G _ _ hG x y K T S M ρ B h2
  have hstd := h2.std
  have hrow := h2.row
  have hmem := h2.mem
  have hnr : ∀ (ρ : Th2Row) (X : Subgroup G),
      (∀ A : Subgroup G, IsE 3 X A → Th2.RConnN 3 4 X A B) → ρ.level.r = 3 → ρ.level.n = 4 →
        (∀ A : Subgroup G, IsE ρ.level.r X A → Th2.RConnN ρ.level.r ρ.level.n X A B) ∧
          (∀ A : Subgroup G, IsE ρ.level.n X A → Th2.RConnN ρ.level.r ρ.level.n X A B) := by
    intro ρ X h hr hn
    rw [hr, hn]
    exact ⟨h, fun A hA => h A (isE_mono_rank hA (by norm_num))⟩
  cases ρ with
  | r1a =>
    obtain ⟨hL2, -, h3⟩ := hrow
    have hPr : ∀ q : ℕ, (Odd q ∧ ¬ IsFM9 q) → Odd q := fun q hq => hq.1
    exact (false_of_three_le_rank_Q hG hstd (centerlessBar_of_hasL2Model hPr hL2)
      (rankTwoShape_sylow_L2 hstd.sylow_P (TwoThin.isQuasisimple_hat hstd.comp) hPr hL2) h3).elim
  | r1b =>
    obtain ⟨hL2, -⟩ := hrow
    have hPr : ∀ q : ℕ, (Odd q ∧ ¬ IsFM9 q) → Odd q := fun q hq => hq.1
    refine ⟨fun _ _ A hA => conn_L2 hstd hPr hL2 hmem hA, fun A hA => ?_⟩
    exact conn_L2 hstd hPr hL2 hmem (isE_mono_rank hA (by decide))
  | r2 =>
    have hPr : ∀ q : ℕ, (Odd q ∧ IsFM9 q ∧ q ≠ 5) → Odd q := fun q hq => hq.1
    refine ⟨fun _ _ A hA => conn_L2 hstd hPr hrow hmem hA, fun A hA => ?_⟩
    exact conn_L2 hstd hPr hrow hmem (isE_mono_rank hA (by decide))
  | r3a =>
    obtain ⟨h7, -, h3⟩ := hrow
    exact (false_of_three_le_rank_Q hG hstd (centerlessBar_of_A7 h7)
      (rankTwoShape_sylow_A7 hstd.sylow_P h7) h3).elim
  | r3b =>
    obtain ⟨h7, hQ4, hTS⟩ := hrow
    refine ⟨fun _ _ A hA => conn_A7_3b hG h3b hstd h7 hQ4 hTS hmem hA, fun A hA => ?_⟩
    exact conn_A7_3b hG h3b hstd h7 hQ4 hTS hmem (isE_mono_rank hA (by decide))
  | r3c =>
    obtain ⟨h7, -⟩ := hrow
    refine ⟨fun _ _ A hA => conn_A7_3c hstd h7 hmem hA, fun A hA => ?_⟩
    exact conn_A7_3c hstd h7 hmem (isE_mono_rank hA (by decide))
  | r4a =>
    obtain ⟨hL2, h3⟩ := hrow
    have hPr : ∀ q : ℕ, q = 5 → Odd q := by rintro q rfl; decide
    exact (false_of_three_le_rank_Q hG hstd (centerlessBar_of_hasL2Model hPr hL2)
      (rankTwoShape_sylow_L2 hstd.sylow_P (TwoThin.isQuasisimple_hat hstd.comp) hPr hL2) h3).elim
  | r4b =>
    obtain ⟨hL2, -⟩ := hrow
    exact ⟨fun h _ => absurd rfl h, fun A hA => conn_L2_five hG hstd hL2 hmem hA⟩
  | r4c =>
    obtain ⟨hL2, -⟩ := hrow
    refine ⟨fun _ h => absurd rfl h, fun A hA => ?_⟩
    exact RConnN.mono_r (r := 2) (r' := 3) (by decide) (conn_L2_five hG hstd hL2 hmem hA)
  | r5 =>
    obtain ⟨hL34', hel, hcard⟩ := hrow
    exact (hL34 G hG.gen4 x K hstd.orderOf_x hstd.comp ⟨hL34', hel, hcard⟩).elim

end CFSG.GH74.GLS
