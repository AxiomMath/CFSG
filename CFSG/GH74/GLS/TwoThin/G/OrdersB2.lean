module

public import CFSG.GH74.GLS.TwoThin.G.Section
public import CFSG.GH74.Orders.LieType
public import CFSG.GH74.Orders.Sporadic

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint Assembly.LowTwoRank
open CFSG.Open (ordA ordSuzuki)

theorem card_statedSL_two (F : Type) [Field F] [Finite F] :
    Nat.card (StatedSL 2 F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two F

theorem three_dvd_mul_sq_sub_one (q : ℕ) : 3 ∣ q * (q ^ 2 - 1) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have h : (m + 1) ^ 2 - 1 = m * (m + 2) := by
    have : (m + 1) ^ 2 = m * (m + 2) + 1 := by ring
    omega
  rw [h]
  have h3 : 3 ∣ m ∨ 3 ∣ m + 1 ∨ 3 ∣ m + 2 := by omega
  rcases h3 with h3 | h3 | h3
  · exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h3 _) _
  · exact Dvd.dvd.mul_right h3 _
  · exact Dvd.dvd.mul_left (Dvd.dvd.mul_left h3 _) _

theorem ordA_two_four : ordA 2 4 = 20160 := by
  decide +kernel

theorem inB2_card_cases
    {K : Type} [Group K] [Finite K] (h : InB2 K) :
    3 ∣ Nat.card K ∧ ((7 ∣ Nat.card K ∧ 5040 ≤ Nat.card K) ∨
      ∃ q : ℕ, Odd q ∧ Nat.card K = q * (q ^ 2 - 1)) := by
  rcases inB2_cases h with ⟨F, _, _, hodd, ⟨e⟩⟩ | ⟨n, hn7, -, hq, hc2, ⟨e⟩⟩ | ⟨hL34, -⟩
  · have hK : Nat.card K = Nat.card F * (Nat.card F ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_two]
    exact ⟨hK ▸ three_dvd_mul_sq_sub_one _, Or.inr ⟨Nat.card F, hodd, hK⟩⟩
  · have hcard : Nat.card K = Nat.factorial n := by
      have h1 : Nat.card K = Nat.card (K ⧸ center K) * Nat.card ↥(center K) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
      have h2 : Nat.card (K ⧸ center K) = Nat.card (alternatingGroup (Fin n)) :=
        Nat.card_congr e.toEquiv
      have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
      have h3 : Nat.card (alternatingGroup (Fin n)) = Nat.factorial n / 2 := by
        rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      rw [h1, h2, h3, hc2, Nat.div_mul_cancel]
      exact Nat.dvd_trans (by norm_num) (Nat.factorial_dvd_factorial (by omega : 2 ≤ n))
    rw [hcard]
    exact ⟨Nat.dvd_factorial (by norm_num) (by omega),
      Or.inl ⟨Nat.dvd_factorial (by norm_num) hn7, by
        calc 5040 = Nat.factorial 7 := by decide +kernel
          _ ≤ Nat.factorial n := Nat.factorial_le hn7⟩⟩
  · have hcard : 20160 ∣ Nat.card K := by
      have h1 : Nat.card K = Nat.card (K ⧸ center K) * Nat.card ↥(center K) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
      have h2 : Nat.card (K ⧸ center K) = 20160 := by
        rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) hL34]
        exact ordA_two_four
      rw [h1, h2]
      exact Dvd.intro _ rfl
    exact ⟨Nat.dvd_trans (by norm_num) hcard, Or.inl ⟨Nat.dvd_trans (by norm_num) hcard,
      le_trans (by norm_num) (Nat.le_of_dvd Nat.card_pos hcard)⟩⟩

theorem inB2_three_dvd_card
    {K : Type} [Group K] [Finite K] (h : InB2 K) : 3 ∣ Nat.card K :=
  (inB2_card_cases h).1

theorem not_inB2_of_card_two_Sz8
    {K : Type} [Group K] [Finite K]
    (hc : Nat.card (center K) = 2)
    (hS : LieModel (K ⧸ center K) .twistedB2 0 2 3) : ¬ InB2 K := by
  intro h
  have h3 := inB2_three_dvd_card h
  have h1 : Nat.card K = Nat.card (K ⧸ center K) * Nat.card ↥(center K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
  rw [h1, hc, CFSG.GH74.card_of_lieModel_twistedB2 hS] at h3
  revert h3
  decide +kernel

theorem not_inB2_of_card_two_M12
    {K : Type} [Group K] [Finite K]
    (hc : Nat.card (center K) = 2) (hS : NativeSporadic.IsSporadic (K ⧸ center K) .M12) :
    ¬ InB2 K := by
  intro h
  have h1 : Nat.card K = 190080 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center K), hc,
      CFSG.GH74.card_of_isSporadic_M12 hS]
    norm_num
  obtain ⟨-, ⟨h7, -⟩ | ⟨q, -, hq⟩⟩ := inB2_card_cases h
  · rw [h1] at h7
    revert h7
    decide +kernel
  · rw [h1] at hq
    rcases Nat.lt_or_ge q 58 with hlt | hge
    · have : q * (q ^ 2 - 1) ≤ 57 * (57 ^ 2 - 1) := by
        apply Nat.mul_le_mul (by omega)
        apply Nat.sub_le_sub_right
        exact Nat.pow_le_pow_left (by omega) 2
      omega
    · have : 58 * (58 ^ 2 - 1) ≤ q * (q ^ 2 - 1) := by
        apply Nat.mul_le_mul hge
        apply Nat.sub_le_sub_right
        exact Nat.pow_le_pow_left hge 2
      omega

theorem not_inB2_dvd_504
    {K : Type} [Group K] [Finite K] (h : InB2 K) (hd : Nat.card K ∣ 504) :
    False := by
  have h120 := card_ge_of_inB2 h
  have hle := Nat.le_of_dvd (by norm_num) hd
  obtain ⟨-, ⟨-, h5040⟩ | ⟨q, hodd, hq⟩⟩ := inB2_card_cases h
  · omega
  · obtain ⟨k, hk⟩ := hodd
    rw [hq] at hd hle h120
    have hq8 : q ≤ 8 := by
      by_contra hcon
      have : 9 * (9 ^ 2 - 1) ≤ q * (q ^ 2 - 1) := by
        apply Nat.mul_le_mul (by omega)
        apply Nat.sub_le_sub_right
        exact Nat.pow_le_pow_left (by omega) 2
      omega
    interval_cases q <;> omega

theorem not_inB2_dvd_5616
    {K : Type} [Group K] [Finite K] (h : InB2 K) (hd : Nat.card K ∣ 5616) :
    False := by
  have h120 := card_ge_of_inB2 h
  have hle := Nat.le_of_dvd (by norm_num) hd
  obtain ⟨-, ⟨h7, -⟩ | ⟨q, hodd, hq⟩⟩ := inB2_card_cases h
  · have := Nat.dvd_trans h7 hd
    revert this
    decide +kernel
  · obtain ⟨k, hk⟩ := hodd
    rw [hq] at hd hle h120
    have hq18 : q ≤ 18 := by
      by_contra hcon
      have : 19 * (19 ^ 2 - 1) ≤ q * (q ^ 2 - 1) := by
        apply Nat.mul_le_mul (by omega)
        apply Nat.sub_le_sub_right
        exact Nat.pow_le_pow_left (by omega) 2
      omega
    interval_cases q <;> omega

end CFSG.GH74.GLS.TwoThin
