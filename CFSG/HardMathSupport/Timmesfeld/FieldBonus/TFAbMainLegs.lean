module

public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.TFAbRankW
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.TFAbCover

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open CFSG.Models CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (glaTwoLocalRank_congr)
open CFSG.Open (GriessAllModelsStatement)

theorem three_dvd_two_pow_add_one_iff {f : ℕ} : 3 ∣ 2 ^ f + 1 ↔ Odd f := by
  refine ⟨fun h => ?_, three_dvd_two_pow_add_one⟩
  by_contra hf
  obtain ⟨k, rfl⟩ := Nat.not_odd_iff_even.1 hf
  have h1 : 2 ^ (k + k) % 3 = 1 := by
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  omega

theorem even_card_iff_neg_one_eq_one {K : Type} [Field K] [Finite K] :
    Even (Nat.card K) ↔ (-1 : K) = 1 := by
  have := Fintype.ofFinite K
  rw [neg_one_eq_one_iff, FiniteField.even_card_iff_char_two, Nat.card_eq_fintype_card,
    Nat.even_iff]

theorem charP_two_of_neg_one_eq_one {K : Type} [Field K] (h : (-1 : K) = 1) : CharP K 2 := by
  have h2 : ringChar K = 2 := (neg_one_eq_one_iff).1 h
  rw [← h2]
  exact ringChar.charP K

theorem psl_three_leg (hGA : GriessAllModelsStatement) {L : Type} [Group L] [Finite L]
    (hperf : Group.IsPerfect L) (hZ : Nat.card (Subgroup.center L) = 3)
    (hw : CFSG.Open.GLATwoLocalRank 3 L = 1) {X : Type} [Group X]
    (e : L ⧸ Subgroup.center L ≃* X) {p f : ℕ} (hm : LieModel X .PSL 3 p f)
    (h3 : 3 ∣ p ^ f - 1) : False := by
  obtain ⟨hadm, hcl | ⟨h0, -⟩⟩ := hm
  swap
  · exact absurd h0 (by norm_num)
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hcl
  obtain ⟨φ⟩ := mulEquiv_statedSL_of_three_cover hGA hadm.1 hadm.2.1 hK h3 hperf hZ (e.trans e')
  have hK3 : 3 ∣ Nat.card K - 1 := by rw [hK]; exact h3
  have hcong := glaTwoLocalRank_congr (p := 3) (by norm_num) φ
  have h2 : 2 ≤ CFSG.Open.GLATwoLocalRank 3 ↥(StatedSL 3 K) := by
    by_cases h1 : (-1 : K) = 1
    · have := charP_two_of_neg_one_eq_one h1
      exact wGeTwoSL3Even hK3
    · exact wGeTwoSL3Odd h1 hK3
  omega

theorem psu_three_leg (hGA : GriessAllModelsStatement) {L : Type} [Group L] [Finite L]
    (hperf : Group.IsPerfect L) (hZ : Nat.card (Subgroup.center L) = 3)
    (hw : CFSG.Open.GLATwoLocalRank 3 L = 1) {X : Type} [Group X]
    (e : L ⧸ Subgroup.center L ≃* X) {p f : ℕ} (hm : LieModel X .PSU 3 p f)
    (h3 : 3 ∣ p ^ f + 1) :
    ∃ (f' : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Odd f' ∧ 3 ≤ f' ∧
      Nat.card K = (2 ^ f') ^ 2 ∧ Nonempty (L ≃* ↥(StatedSU 3 (2 ^ f') K)) := by
  obtain ⟨hadm, hcl | ⟨h0, -⟩⟩ := hm
  swap
  · exact absurd h0 (by norm_num)
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hcl
  have hq2 : p ^ f ≠ 2 := fun h => hadm.2.2.2 (by rw [h])
  obtain ⟨φ⟩ := mulEquiv_statedSU_of_three_cover hGA hadm.1 hadm.2.1 hK h3 hq2 hperf hZ
    (e.trans e')
  have hcong := glaTwoLocalRank_congr (p := 3) (by norm_num) φ
  by_cases h1 : (-1 : K) = 1
  · have hev : Even (Nat.card K) := even_card_iff_neg_one_eq_one.2 h1
    rw [hK] at hev
    have hev' : Even (p ^ f) := (Nat.even_pow.1 hev).1
    have hp2 : p = 2 := by
      have : Even p := (Nat.even_pow.1 hev').1
      exact ((Nat.Prime.even_iff hadm.1).1 this)
    subst hp2
    have hfo : Odd f := three_dvd_two_pow_add_one_iff.1 h3
    have hf3 : 3 ≤ f := by
      obtain ⟨k, rfl⟩ := hfo
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact absurd (by norm_num) hq2
      · omega
    exact ⟨f, K, inferInstance, inferInstance, hfo, hf3, hK, ⟨φ⟩⟩
  · exfalso
    have hodd : Odd (Nat.card K) := by
      rcases Nat.even_or_odd (Nat.card K) with h | h
      · exact absurd (even_card_iff_neg_one_eq_one.1 h) h1
      · exact h
    rw [hK] at hodd
    have hq : Odd (p ^ f) := by
      by_contra h
      exact (Nat.not_even_iff_odd.2 hodd) (Even.pow_of_ne_zero (Nat.not_odd_iff_even.1 h) (by norm_num))
    have h2 : 2 ≤ CFSG.Open.GLATwoLocalRank 3 L := (wGeTwoSU3Odd hq hK h3).trans_eq hcong
    omega

end CFSG.HardMathSupport.Timmesfeld.FieldBonus
