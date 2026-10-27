module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeRank
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSylowE8Five
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoRank
public import Mathlib.FieldTheory.Finite.Extension

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType CFSG.StandardType.TableBExc CFSG.StandardType.TableBExc.Three
open CFSG.Timmesfeld.ExceptionalOrders (geomSum)

section Torus

variable {K : Type} [Field K]

theorem rootDiagUnit_mem_torusGroup_E7_of_pow_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (a : Fin Tag.E7.rank → Kˣ) (ha : ∀ i, a i ^ p = 1) :
    rootDiagUnit .E7 a ∈ torusGroup .E7 K := by
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  refine rootDiagUnit_mem_torusGroup_of_pow_eq
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_mul_cartan_E7.choose_spec a
    (fun l => a l ^ k) fun l => ?_
  rw [← pow_mul, mul_comm k 2, ← Nat.div_add_mod (2 * k) p, hk, pow_add, pow_mul, ha l, one_pow,
    one_mul, pow_one]

theorem card_torusPow_E7_of_dvd [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) : Nat.card (torusPow .E7 K p) = p ^ 7 :=
  card_torusPow_of_fullp (rootDiagUnit_mem_torusGroup_E7_of_pow_eq_one hp hp2) hp hpq

end Torus

section T

variable {K : Type} [Field K]

theorem ggExcToralRankInput_E7_five_of_dvd [Finite K] (h5 : 5 ∣ Nat.card K - 1) :
    GGExcToralRankInput .E7 K 5 := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hG := geomSum_five_mod (mod_eq_one_of_dvd_sub_one (by norm_num) hq h5)
  have hq1 : (Nat.card K : ZMod 5) = 1 := cast_eq_one_of_dvd_sub_one hq h5
  have hm1 := cast_div_eq (p := 5) (c := 1) (by norm_num) (by norm_num) hG
  have hGm : geomSum 5 1 (Nat.card K) = 5 * (geomSum 5 1 (Nat.card K) / 5) := by omega
  refine ggExcToralRankInput_of_cyclic Nat.prime_five h5
    (isUnit_det_cartan_of_eq Nat.prime_five det_cartan_E7 (by norm_num))
    (card_torusPow_E7_of_dvd Nat.prime_five (by norm_num) h5) wordE7Five orderOf_wordE7Five
    (M := Nat.card K ^ 63 * (geomSum 2 1 (Nat.card K) * geomSum 3 1 (Nat.card K) *
      geomSum 4 1 (Nat.card K) * (geomSum 5 1 (Nat.card K) / 5) *
      (geomSum 2 3 (Nat.card K) * geomSum 8 1 (Nat.card K)) *
      (geomSum 9 1 (Nat.card K) * geomSum 3 4 (Nat.card K)) *
      (geomSum 2 5 (Nat.card K) * geomSum 2 9 (Nat.card K) * geomSum 14 1 (Nat.card K))))
    ?_ ?_ ?_
  · rw [card_adjointGroup_E7_eq_torus_mul, prodE7]
    nth_rewrite 1 [hGm]
    ring
  · apply not_dvd_of_cast_ne_zero
    push_cast
    simp only [hq1, hm1, geomSum_cast hq1, one_pow, Nat.cast_one]
    decide
  · calc 5 * Nat.card {x : Fin Tag.E7.rank → ZMod 5 // torusWord .E7 5 wordE7Five x = x}
        ≤ 5 * 5 ^ (7 - 2) := Nat.mul_le_mul_left _ card_fix_wordE7Five
      _ < 5 ^ Tag.E7.rank := by decide

theorem ggExcToralRankInput_E7_seven_of_dvd [Finite K] (h7 : 7 ∣ Nat.card K - 1) :
    GGExcToralRankInput .E7 K 7 := by
  have hp7 : Nat.Prime 7 := by norm_num
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hG := geomSum_fourteen_mod (mod_eq_one_of_dvd_sub_one (by norm_num) hq h7)
  have hq1 : (Nat.card K : ZMod 7) = 1 := cast_eq_one_of_dvd_sub_one hq h7
  have hm2 := cast_div_eq (p := 7) (c := 2) (by norm_num) (by norm_num) hG
  have hGm : geomSum 14 1 (Nat.card K) = 7 * (geomSum 14 1 (Nat.card K) / 7) := by omega
  refine ggExcToralRankInput_of_cyclic hp7 h7
    (isUnit_det_cartan_of_eq hp7 det_cartan_E7 (by norm_num))
    (card_torusPow_E7_of_dvd hp7 (by norm_num) h7) wordE7Seven orderOf_wordE7Seven
    (M := Nat.card K ^ 63 * (geomSum 2 1 (Nat.card K) * geomSum 3 1 (Nat.card K) *
      geomSum 4 1 (Nat.card K) * geomSum 5 1 (Nat.card K) *
      (geomSum 2 3 (Nat.card K) * geomSum 8 1 (Nat.card K)) *
      (geomSum 9 1 (Nat.card K) * geomSum 3 4 (Nat.card K)) *
      (geomSum 2 5 (Nat.card K) * geomSum 2 9 (Nat.card K) * (geomSum 14 1 (Nat.card K) / 7))))
    ?_ ?_ ?_
  · rw [card_adjointGroup_E7_eq_torus_mul, prodE7]
    nth_rewrite 1 [hGm]
    ring
  · apply not_dvd_of_cast_ne_zero
    push_cast
    simp only [hq1, hm2, geomSum_cast hq1, one_pow]
    decide
  · calc 7 * Nat.card {x : Fin Tag.E7.rank → ZMod 7 // torusWord .E7 7 wordE7Seven x = x}
        ≤ 7 * 7 ^ (7 - 2) := Nat.mul_le_mul_left _ card_fix_wordE7Seven
      _ < 7 ^ Tag.E7.rank := by decide

theorem ggExcToralRankInput_E8_seven_of_dvd [Finite K] (h7 : 7 ∣ Nat.card K - 1) :
    GGExcToralRankInput .E8 K 7 := by
  have hp7 : Nat.Prime 7 := by norm_num
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hG := geomSum_fourteen_mod (mod_eq_one_of_dvd_sub_one (by norm_num) hq h7)
  have hq1 : (Nat.card K : ZMod 7) = 1 := cast_eq_one_of_dvd_sub_one hq h7
  have hm2 := cast_div_eq (p := 7) (c := 2) (by norm_num) (by norm_num) hG
  have hGm : geomSum 14 1 (Nat.card K) = 7 * (geomSum 14 1 (Nat.card K) / 7) := by omega
  refine ggExcToralRankInput_of_cyclic hp7 h7
    (isUnit_det_cartan_of_eq hp7 det_cartan_E8 (by norm_num))
    (card_torusPow_E8_of_dvd hp7 h7) wordE8Seven orderOf_wordE8Seven
    (M := Nat.card K ^ 120 * (geomSum 2 1 (Nat.card K) * geomSum 3 1 (Nat.card K) *
      geomSum 4 1 (Nat.card K) * geomSum 5 1 (Nat.card K) *
      (geomSum 2 3 (Nat.card K) * geomSum 8 1 (Nat.card K)) *
      (geomSum 9 1 (Nat.card K) * geomSum 3 4 (Nat.card K)) *
      (geomSum 2 5 (Nat.card K) * geomSum 2 9 (Nat.card K) * (geomSum 14 1 (Nat.card K) / 7)) *
      (geomSum 24 1 (Nat.card K) * geomSum 2 10 (Nat.card K) * geomSum 5 6 (Nat.card K))))
    ?_ ?_ ?_
  · rw [card_adjointGroup_E8_eq, prodE8]
    nth_rewrite 1 [hGm]
    ring
  · apply not_dvd_of_cast_ne_zero
    push_cast
    simp only [hq1, hm2, geomSum_cast hq1, one_pow]
    decide
  · calc 7 * Nat.card {x : Fin Tag.E8.rank → ZMod 7 // torusWord .E8 7 wordE8Seven x = x}
        ≤ 7 * 7 ^ (8 - 2) := Nat.mul_le_mul_left _ card_fix_wordE8Seven
      _ < 7 ^ Tag.E8.rank := by decide

theorem ggExcToralRankInput_E8_five_of_dvd [Finite K] (h5 : 5 ∣ Nat.card K - 1) :
    GGExcToralRankInput .E8 K 5 := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hq5 := mod_eq_one_of_dvd_sub_one (by norm_num) hq h5
  have hG1 := geomSum_five_mod hq5
  have hG6 := geomSum_five_six_mod hq5
  have hq1 : (Nat.card K : ZMod 5) = 1 := cast_eq_one_of_dvd_sub_one hq h5
  have hm1 := cast_div_eq (p := 5) (c := 1) (by norm_num) (by norm_num) hG1
  have hm6 := cast_div_eq (p := 5) (c := 1) (by norm_num) (by norm_num) hG6
  have hGm1 : geomSum 5 1 (Nat.card K) = 5 * (geomSum 5 1 (Nat.card K) / 5) := by omega
  have hGm6 : geomSum 5 6 (Nat.card K) = 5 * (geomSum 5 6 (Nat.card K) / 5) := by omega
  set M := Nat.card K ^ 120 * (geomSum 2 1 (Nat.card K) * geomSum 3 1 (Nat.card K) *
      geomSum 4 1 (Nat.card K) * (geomSum 5 1 (Nat.card K) / 5) *
      (geomSum 2 3 (Nat.card K) * geomSum 8 1 (Nat.card K)) *
      (geomSum 9 1 (Nat.card K) * geomSum 3 4 (Nat.card K)) *
      (geomSum 2 5 (Nat.card K) * geomSum 2 9 (Nat.card K) * geomSum 14 1 (Nat.card K)) *
      (geomSum 24 1 (Nat.card K) * geomSum 2 10 (Nat.card K) * (geomSum 5 6 (Nat.card K) / 5)))
    with hM
  have hC : Nat.card (adjointGroup .E8 K) =
      Nat.card weylE8S * Nat.card (torusGroup .E8 K) * M := by
    rw [card_adjointGroup_E8_eq, prodE8, card_weylE8S, hM]
    nth_rewrite 1 [hGm1]
    nth_rewrite 1 [hGm6]
    ring
  have hMp : ¬ 5 ∣ M := by
    apply not_dvd_of_cast_ne_zero
    rw [hM]
    push_cast
    simp only [hq1, hm1, hm6, geomSum_cast hq1, one_pow, Nat.cast_one]
    decide
  refine ggExcToralRankInput_of_weylX Nat.prime_five h5
    (isUnit_det_cartan_of_eq Nat.prime_five det_cartan_E8 (by norm_num))
    (card_torusPow_E8_of_dvd Nat.prime_five h5) (S := weylE8S)
    (by rw [index_weylX_eq hC]; exact hMp) fun s hs hs1 => ?_
  obtain ⟨k, hk | ⟨c, hc, hk⟩⟩ := exists_pow_eq_rep hs hs1
  · refine ⟨k, wordE8B, hk.symm, ?_⟩
    rw [card_weylE8S]
    calc 25 * Nat.card {x : Fin Tag.E8.rank → ZMod 5 // torusWord .E8 5 wordE8B x = x}
        ≤ 25 * 5 ^ (8 - 3) := Nat.mul_le_mul_left _ card_fix_wordE8B
      _ < 5 ^ Tag.E8.rank := by decide
  · refine ⟨k, wordE8AB c, by rw [wordProd_wordE8AB, hk], ?_⟩
    rw [card_weylE8S]
    calc 25 * Nat.card {x : Fin Tag.E8.rank → ZMod 5 // torusWord .E8 5 (wordE8AB c) x = x}
        ≤ 25 * 5 ^ (8 - 3) := Nat.mul_le_mul_left _ (card_fix_wordE8AB hc)
      _ < 5 ^ Tag.E8.rank := by decide

theorem not_dvd_index_torusGroup_E7_of_dvd [Finite K] {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (hpq : p ∣ Nat.card K - 1) :
    ¬ p ∣ ((torusGroup .E7 K).subgroupOf (adjointGroup .E7 K)).index := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  rw [index_torusGroup_eq card_adjointGroup_E7_eq_torus_mul]
  have hq1 := cast_eq_one_of_dvd_sub_one hq hpq
  have hW := not_dvd_smooth hp hp11 10 4 1 1
  rw [← ZMod.natCast_eq_zero_iff] at hW ⊢
  intro h
  apply hW
  rw [← h, prodE7]
  push_cast
  simp only [geomSum_cast hq1, hq1, one_pow]
  norm_num

theorem ggExcToralRankInput_of_odd_dvd {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) [Finite K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) : GGExcToralRankInput τ K p := by
  rcases hτ with rfl | rfl
  · by_cases h11 : 11 ≤ p
    · exact ggExcToralRankInput_of_not_dvd_index hp
        (not_dvd_index_torusGroup_E7_of_dvd hp h11 hpq) (card_torusPow_E7_of_dvd hp hp2 hpq)
    · rcases eq_three_or_five_or_seven hp hp2 (by omega) with rfl | rfl | rfl
      · exact ggExcToralRankInput_E7_three_of_dvd hpq
      · exact ggExcToralRankInput_E7_five_of_dvd hpq
      · exact ggExcToralRankInput_E7_seven_of_dvd hpq
  · by_cases h11 : 11 ≤ p
    · exact ggExcToralRankInput_of_not_dvd_index hp
        (not_dvd_index_torusGroup_E8 hp h11 hpq) (card_torusPow_E8_of_dvd hp hpq)
    · rcases eq_three_or_five_or_seven hp hp2 (by omega) with rfl | rfl | rfl
      · exact ggExcToralRankInput_E8_three_of_dvd hpq
      · exact ggExcToralRankInput_E8_five_of_dvd hpq
      · exact ggExcToralRankInput_E8_seven_of_dvd hpq

theorem card_le_pow_rank_of_E7_or_E8 {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) [Finite K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) {F : Subgroup (adjointGroup τ K)}
    (hF : IsElemAbelian p F) : Nat.card F ≤ p ^ τ.rank := by
  refine (ggExcToralRankInput_of_odd_dvd hτ hp hp2 hpq).card_le ?_ hF
  rcases hτ with rfl | rfl
  · exact card_torusPow_E7_of_dvd hp hp2 hpq
  · exact card_torusPow_E8_of_dvd hp hpq

theorem card_le_pow_rank_of_E7_or_E8_of_dvd_sq {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) [Finite K]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K ^ 2 - 1)
    {F : Subgroup (adjointGroup τ K)} (hF : IsElemAbelian p F) : Nat.card F ≤ p ^ τ.rank := by
  have : CharP K (ringChar K) := ringChar.charP K
  have : Fact (ringChar K).Prime :=
    ⟨(CharP.char_is_prime_or_zero K (ringChar K)).resolve_right
      (CharP.ringChar_ne_zero_of_finite K)⟩
  have hL : Nat.card (FiniteField.Extension K (ringChar K) 2) = Nat.card K ^ 2 :=
    FiniteField.natCard_extension K (ringChar K) 2
  have h := card_le_pow_rank_of_E7_or_E8 hτ (K := FiniteField.Extension K (ringChar K) 2) hp hp2
    (by rw [hL]; exact hpq)
    (TableB.isElemAbelian_map hF
      (TableBExcTwo.adjointMap τ (algebraMap K (FiniteField.Extension K (ringChar K) 2))))
  rwa [Subgroup.card_map_of_injective (TableBExcTwo.adjointMap_injective _)] at h

end T

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc
