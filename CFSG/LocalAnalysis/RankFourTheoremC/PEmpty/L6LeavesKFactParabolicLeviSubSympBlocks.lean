module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubSympRank
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympHas

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} {I : Set ℕ}

theorem gcd_two_card_sub_one : Nat.gcd 2 (Nat.card K - 1) = 1 := by
  obtain ⟨f, hf, hq⟩ := spFlag_card_eq_two_pow (K := K)
  rw [hq]
  have : 2 ≤ 2 ^ f := le_self_pow₀ (by norm_num) (by omega)
  obtain ⟨c, hc⟩ : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  exact Nat.coprime_two_left.mpr ⟨c - 1, by omega⟩

theorem ordBC_eq (m : ℕ) :
    ordBC m (Nat.card K) =
      Nat.card K ^ (m * m) * ∏ i ∈ Finset.Icc 1 m, (Nat.card K ^ (2 * i) - 1) := by
  rw [ordBC, gcd_two_card_sub_one (K := K), Nat.div_one]

theorem dvd_ordBC {m i p : ℕ} (hi1 : 1 ≤ i) (him : i ≤ m) (hpi : p ∣ Nat.card K ^ (2 * i) - 1) :
    p ∣ ordBC m (Nat.card K) := by
  rw [ordBC_eq]
  exact Dvd.dvd.mul_left (hpi.trans (Finset.dvd_prod_of_mem (fun i => Nat.card K ^ (2 * i) - 1)
    (Finset.mem_Icc.2 ⟨hi1, him⟩))) _

theorem sp_res_block_data (hI : ∀ i ∈ I, i ≤ r) (t : ℕ) {j : Fin (r + 1)} (hj0 : (j : ℕ) = 0)
    {p i : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hi1 : 1 ≤ i) (him : i ≤ r - t)
    (hpi : p ∣ Nat.card K ^ (2 * i) - 1) :
    CFSG.Open.IsQuasisimple ↥(spFlagLeviBlock (K := K) hI t j) ∧
      ¬ p ∣ Nat.card (Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j)) ∧
      p ∣ Nat.card (↥(spFlagLeviBlock (K := K) hI t j) ⧸
        Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j)) ∧
      (∀ f : ℕ, f ∣ Nat.card K - 1 → f ∣ Nat.card (↥(spFlagLeviBlock (K := K) hI t j) ⧸
        Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j))) ∧
      (Nat.card K = 2 → 3 ∣ Nat.card (↥(spFlagLeviBlock (K := K) hI t j) ⧸
        Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j))) := by
  have hK := spFlag_card_eq_two_or_four_le (K := K)
  let e := spFlagLeviBlockZeroEquiv (K := K) hI t hj0
  rcases spFlag_res_cases (r - t) K with hs | h2 | hq' | hbad
  · exfalso
    rcases hs with hm0 | ⟨hm1, hK2⟩
    · omega
    · have : i = 1 := by omega
      subst this
      rw [hK2] at hpi
      have h3 : p ∣ 3 := by simpa using hpi
      have := Nat.le_of_dvd (by norm_num) h3
      omega
  · obtain ⟨hm, hK2⟩ := h2
    have hQS : CFSG.Open.IsQuasisimple ↥(spFlagLeviBlock (K := K) hI t j) := by
      have h := (spFlag_spFour_comm (K := K) hK2).1
      rw [← hm] at h
      exact isQuasisimple_of_mulEquiv e.symm h
    have hN := (spFlag_spFour_comm (K := K) hK2).2
    rw [← hm] at hN
    have hNj : Nat.card (↥(spFlagLeviBlock (K := K) hI t j) ⧸
        Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j)) = 360 := by
      rw [spFlag_card_center_congr e]
      exact hN
    refine ⟨hQS, ?_, ?_, ?_, ?_⟩
    ·
      intro hpZ
      have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j))
      rw [hNj] at hmul
      have hS0 : Nat.card ↥(spFlagLeviBlock (K := K) hI t j) ∣ Nat.card (StatedSp (r - t) K) := by
        rw [Nat.card_congr e.toEquiv]
        exact Subgroup.card_subgroup_dvd_card _
      rw [hmul, hm, SymplecticFlag.card_statedSp_two, hK2] at hS0
      have h720 : (2 : ℕ) ^ 4 * ((2 ^ 2 - 1) * (2 ^ 4 - 1)) = 360 * 2 := by norm_num
      rw [h720] at hS0
      have hZ2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 360) hS0
      have := Nat.le_of_dvd (by norm_num) (hpZ.trans hZ2)
      omega
    · rw [hNj]
      have hi2 : i = 1 ∨ i = 2 := by omega
      rcases hi2 with rfl | rfl
      · rw [hK2] at hpi
        have h3 : p ∣ 3 := by simpa using hpi
        have := Nat.le_of_dvd (by norm_num) h3
        omega
      · rw [hK2] at hpi
        exact hpi.trans (by norm_num)
    · intro f hf
      rw [hK2] at hf
      have : f = 1 := Nat.dvd_one.1 (by simpa using hf)
      rw [this]
      exact one_dvd _
    · intro _
      rw [hNj]
      norm_num
  ·
    have hq'' := spFlag_isQuasisimple_Sp (K := K) hq'.1 hq'.2
    let e' := e.trans ((MulEquiv.subgroupCongr hq''.1).trans Subgroup.topEquiv)
    have hQS : CFSG.Open.IsQuasisimple ↥(spFlagLeviBlock (K := K) hI t j) :=
      isQuasisimple_of_mulEquiv e'.symm hq''
    have hN : Nat.card (↥(spFlagLeviBlock (K := K) hI t j) ⧸
        Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j)) = ordBC (r - t) (Nat.card K) := by
      rw [spFlag_card_center_congr e', spFlag_card_Sp_center]
    have hZ1 : Nat.card (Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j)) = 1 := by
      have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j))
      have hcard : Nat.card ↥(spFlagLeviBlock (K := K) hI t j) = ordBC (r - t) (Nat.card K) := by
        rw [Nat.card_congr e'.toEquiv, SymplecticFlag.card_statedSp, ordBC_eq]
        ring
      rw [hcard, hN] at hmul
      have hpos : 0 < ordBC (r - t) (Nat.card K) := by
        rw [← hN]
        exact Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_one]; exact hmul.symm)
    refine ⟨hQS, by rw [hZ1]; exact fun h => hp.one_lt.ne' (Nat.dvd_one.1 h), ?_, ?_, ?_⟩
    · rw [hN]
      exact dvd_ordBC hi1 him hpi
    · intro f hf
      rw [hN]
      have h1 : f ∣ Nat.card K ^ (2 * 1) - 1 := by
        rw [mul_one]
        exact hf.trans (Nat.sub_one_dvd_pow_sub_one (Nat.card K) 2)
      exact dvd_ordBC le_rfl hq'.1 h1
    · intro hq2
      rw [hN]
      have h3 : 3 ∣ Nat.card K ^ (2 * 1) - 1 := by rw [hq2]; norm_num
      exact dvd_ordBC le_rfl hq'.1 h3
  · omega

theorem sp_mem_block_data (hI : ∀ i ∈ I, i ≤ r) (t : ℕ) {j : Fin (r + 1)} (hj0 : (j : ℕ) ≠ 0)
    (hj : (j : ℕ) ∈ I) {p i : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hi2 : 2 ≤ i)
    (hik : i ≤ (j : ℕ) - spFlagPrev I j) (hpi : p ∣ Nat.card K ^ i - 1)
    (hnd : ¬ p ∣ Nat.card K - 1) :
    CFSG.Open.IsQuasisimple ↥(spFlagLeviBlock (K := K) hI t j) ∧
      ¬ p ∣ Nat.card (Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j)) ∧
      p ∣ Nat.card (↥(spFlagLeviBlock (K := K) hI t j) ⧸
        Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j)) ∧
      (∀ f : ℕ, f ∣ Nat.card K - 1 → f ∣ Nat.card (↥(spFlagLeviBlock (K := K) hI t j) ⧸
        Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j))) ∧
      (Nat.card K = 2 → 3 ∣ Nat.card (↥(spFlagLeviBlock (K := K) hI t j) ⧸
        Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j))) := by
  have hK := spFlag_card_eq_two_or_four_le (K := K)
  let e := spFlagLeviBlockMemEquiv (K := K) hI t hj0 hj
  have hk2 : 2 ≤ (j : ℕ) - spFlagPrev I j := by omega
  have hq3 : 3 ≤ (j : ℕ) - spFlagPrev I j ∨ 4 ≤ Nat.card K := by
    by_contra h
    push Not at h
    have hK2 : Nat.card K = 2 := by omega
    have hi : i = 2 := by omega
    rw [hi, hK2] at hpi
    have h3 : p ∣ 3 := by simpa using hpi
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hQS : CFSG.Open.IsQuasisimple ↥(spFlagLeviBlock (K := K) hI t j) :=
    isQuasisimple_of_mulEquiv e.symm (spFlag_isQuasisimple_SL hk2 hq3)
  have hZ : Nat.card (Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j)) =
      Nat.card (Subgroup.center (SpecialLinearGroup (Fin ((j : ℕ) - spFlagPrev I j)) K)) := by
    have h := map_center_mulEquiv e
    rw [← h, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  refine ⟨hQS, ?_, ?_, ?_, ?_⟩
  · rw [hZ]
    exact fun h => hnd (h.trans (card_center_SL_dvd (by omega)))
  · rw [spFlag_card_center_congr e]
    exact dvd_card_slQuot hk2 hp hi2 hik hpi hnd
  · intro f hf
    rw [spFlag_card_center_congr e]
    exact dvd_card_slQuot_of_dvd_sub_one hk2 hf
  · intro hq2
    rw [spFlag_card_center_congr e]
    exact three_dvd_card_slQuot hk2 hq2

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
