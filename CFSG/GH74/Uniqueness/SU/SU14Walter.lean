module

public import CFSG.Milestones.CL_LIT_Walter_abelian_Sylow_two_simple

public section

namespace CFSG.GH74.Uniqueness.SU.SU14

open Subgroup
open scoped MatrixGroups

theorem ree_not_dvd_five (m : ℕ) :
    ¬ 5 ∣ (3 ^ (2 * m + 1)) ^ 3 * ((3 ^ (2 * m + 1)) ^ 3 + 1) * (3 ^ (2 * m + 1) - 1) := by
  have hmod : ∀ m : ℕ, 3 ^ (2 * m + 1) % 5 = 3 ∨ 3 ^ (2 * m + 1) % 5 = 2 := by
    intro m
    induction m with
    | zero => left; norm_num
    | succ k ih =>
      have : 3 ^ (2 * (k + 1) + 1) = 3 ^ (2 * k + 1) * 9 := by ring
      rw [this, Nat.mul_mod]
      rcases ih with h | h <;> rw [h] <;> norm_num
  intro h
  have hq := hmod m
  have hpos : 1 ≤ 3 ^ (2 * m + 1) := Nat.one_le_pow _ _ (by norm_num)
  set q := 3 ^ (2 * m + 1) with hqdef
  have h5 := (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h
  rcases h5 with h5 | h5
  · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h5 with h6 | h6
    · have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h6)
      omega
    · have h7 : (q ^ 3 + 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd h6
      rcases hq with h8 | h8
      · have : q ^ 3 % 5 = 2 := by rw [Nat.pow_mod, h8]
        omega
      · have : q ^ 3 % 5 = 3 := by rw [Nat.pow_mod, h8]
        omega
  · have h7 : (q - 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd h5
    omega

theorem odd_psl_not_dvd_eight (q : ℕ) (h : q % 8 = 3 ∨ q % 8 = 5) :
    ¬ 8 ∣ q * (q ^ 2 - 1) / 2 := by
  intro hd
  have hq1 : 1 ≤ q := by omega
  have h16 : q ^ 2 % 16 = 9 := by
    have : q % 16 = 3 ∨ q % 16 = 5 ∨ q % 16 = 11 ∨ q % 16 = 13 := by omega
    rcases this with h | h | h | h <;> simp [pow_two, Nat.mul_mod, h]
  obtain ⟨k, hk⟩ : ∃ k, q ^ 2 - 1 = 16 * k + 8 := ⟨q ^ 2 / 16 - 0, by omega⟩
  have hq2 : Odd q := by rw [Nat.odd_iff]; omega
  have hmul : q * (q ^ 2 - 1) / 2 = 4 * (q * (2 * k + 1)) := by
    rw [hk]
    have : q * (16 * k + 8) = 2 * (4 * (q * (2 * k + 1))) := by ring
    rw [this]; simp
  rw [hmul] at hd
  have h2 : 2 ∣ q * (2 * k + 1) := by
    have : 4 * 2 ∣ 4 * (q * (2 * k + 1)) := by simpa using hd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have hodd : Odd (q * (2 * k + 1)) := hq2.mul (by simp)
  have := (Nat.odd_iff.mp hodd)
  omega

theorem even_case_f (f idx : ℕ) (hf : 2 ≤ f) (hidx : idx % 2 = 1)
    (h : 2 ^ f * ((2 ^ f) ^ 2 - 1) = 8 * idx) : f = 3 ∧ idx = 63 := by
  by_cases hf4 : 4 ≤ f
  · exfalso
    have h16 : 2 ^ 4 ∣ 2 ^ f := Nat.pow_dvd_pow 2 hf4
    have : 16 ∣ 8 * idx := by
      rw [← h]
      exact Dvd.dvd.mul_right (by simpa using h16) _
    omega
  · have hf3 : f ≤ 3 := by omega
    interval_cases f
    · norm_num at h
      omega
    · norm_num at h
      omega

theorem isSporadic_J1_of_abelian_sylow
    {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G) (hSab : IsMulCommutative (S : Subgroup G))
    (hS8 : Nat.card (S : Subgroup G) = 8) (h5 : 5 ∣ Nat.card G) :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .J1 := by
  have hidx : (S : Subgroup G).index % 2 = 1 := by
    have h2 : ¬ 2 ∣ (S : Subgroup G).index := S.not_dvd_index
    omega
  have hcard : Nat.card G = 8 * (S : Subgroup G).index := by
    rw [← Subgroup.card_mul_index (S : Subgroup G), hS8]
  rcases CFSG.Milestones.cl_lit_walter_abelian_sylow_two_simple G hn S hSab with
    ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpodd, hf0, h5le, hmod, ⟨e⟩⟩ | ⟨m, hm, hree⟩ | hJ
  ·
    exfalso
    have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    have hcenter := CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
      (K := GaloisField 2 f) (CharTwo.neg_eq 1)
    have hpsl := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center (K := GaloisField 2 f)
    rw [hK, hcenter, mul_one] at hpsl
    have hG : Nat.card G = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv]
      exact hpsl
    obtain ⟨-, hidx63⟩ := even_case_f f _ hf hidx (hG.symm.trans hcard)
    rw [hcard, hidx63] at h5
    omega
  ·
    exfalso
    have hcardK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
    have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p f)) :=
      ⟨p, f, hp.out, hpodd, hf0, hcardK⟩
    have hG : Nat.card G = p ^ f * ((p ^ f) ^ 2 - 1) / 2 := by
      rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.psl2_card_formula _ hodd, hcardK]
    have h8 : 8 ∣ Nat.card G := ⟨(S : Subgroup G).index, hcard⟩
    rw [hG] at h8
    exact odd_psl_not_dvd_eight (p ^ f) hmod h8
  ·
    exfalso
    rw [hree] at h5
    exact ree_not_dvd_five m h5
  · obtain ⟨e⟩ := hJ
    exact CFSG.Walter.isSporadic_J1_of_mulEquiv e

end CFSG.GH74.Uniqueness.SU.SU14
