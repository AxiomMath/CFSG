module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTRkSm
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L2Card

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.RkSm

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem not_isL2_of_card {Y : Type} [Group Y] {N a : ℕ} (hY : Nat.card Y = N)
    (h1 : a * (a ^ 2 - 1) < 2 * N) (h2 : 2 * N < (a + 1) * ((a + 1) ^ 2 - 1)) :
    ¬ IVK.IsL2 Y (fun r => Odd r ∧ 5 ≤ r) := by
  rintro ⟨F, _, _, ⟨hodd, -⟩, ⟨e⟩⟩
  have hc := card_L2_mul_two_of_odd (F := F) hodd
  rw [← Nat.card_congr e.toEquiv, hY] at hc
  rcases le_or_gt (Nat.card F) a with hr | hr
  · have := Nat.mul_le_mul hr (Nat.sub_le_sub_right (Nat.pow_le_pow_left hr 2) 1)
    generalize Nat.card F * (Nat.card F ^ 2 - 1) = X at hc this
    generalize a * (a ^ 2 - 1) = B at h1 this
    omega
  · have hr' : a + 1 ≤ Nat.card F := hr
    have := Nat.mul_le_mul hr' (Nat.sub_le_sub_right (Nat.pow_le_pow_left hr' 2) 1)
    generalize Nat.card F * (Nat.card F ^ 2 - 1) = X at hc this
    generalize (a + 1) * ((a + 1) ^ 2 - 1) = B at h2 this
    omega

theorem not_isSection_of_not_dvd {Y : Type} [Group Y] {N : ℕ} (hY : Nat.card Y = N)
    (hN : ¬ N ∣ 2520) : ¬ IsSection Y (alternatingGroup (Fin 7)) := fun h =>
  hN (hY ▸ card_alt7 ▸ h.card_dvd)

theorem not_isSection_alt7_of_card {Y : Type} [Group Y] (hY : Nat.card Y = 504) :
    ¬ IsSection Y (alternatingGroup (Fin 7)) := by
  rintro ⟨U, φ, hφ⟩
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hU : Nat.card U = 504 * Nat.card φ.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv, hY]
  have hk : 0 < Nat.card φ.ker := Nat.card_pos
  have hidx := U.card_mul_index
  rw [card_alt7] at hidx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal U.normalCore with h | h
  · have hcore := U.index_normalCore_dvd_factorial_index
    rw [h, index_bot, card_alt7] at hcore
    have hi5 : U.index ≤ 5 := by
      by_contra h6
      have := Nat.mul_le_mul (show 504 ≤ Nat.card U by rw [hU]; omega) (not_le.mp h6)
      omega
    have h1 := Nat.le_of_dvd (Nat.factorial_pos _) hcore
    have h2 : Nat.factorial U.index ≤ 120 := (Nat.factorial_le hi5).trans (by decide)
    omega
  · have hUtop : U = ⊤ := top_le_iff.mp (h ▸ U.normalCore_le)
    have hUc : Nat.card U = 2520 := by rw [hUtop, card_top, card_alt7]
    have : IsSimpleGroup U := ((MulEquiv.subgroupCongr hUtop).trans topEquiv).isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hb | hb
    · rw [hb, card_bot] at hU
      omega
    · rw [hb, card_top] at hU
      omega

theorem not_kindFactorAll {k : Stage12.Kind} (hk : Local.IsClassicalKind k) {Y : Type}
    [Group Y] {N a : ℕ} (hY : Nat.card Y = N) (h1 : a * (a ^ 2 - 1) < 2 * N)
    (h2 : 2 * N < (a + 1) * ((a + 1) ^ 2 - 1))
    (hS : ¬ IsSection Y (alternatingGroup (Fin 7))) : ¬ KindFactorAll k Y := by
  rcases hk with rfl | ⟨ε, rfl⟩
  · exact not_isL2_of_card hY h1 h2
  · rintro (h | h)
    · exact not_isL2_of_card hY h1 h2 h
    · exact hS h

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.RkSm
