module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Setting
public import CFSG.Open.WalterAbelianSylowTwoMilestoneDefs
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
import CFSG.Walter.J1Props.Elt
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSporadicStandard.J1Std

open Subgroup CFSG.Open
open scoped MatrixGroups

@[expose] def WalterAbelian : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ P : Sylow 2 G, IsMulCommutative (P : Subgroup G) →
    (∃ f : ℕ, 2 ≤ f ∧ Nonempty (G ≃* PSL(2, GaloisField 2 f))) ∨
    (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (G ≃* PSL(2, GaloisField p f))) ∨
    (∃ m : ℕ, 1 ≤ m ∧ Nat.card G = ordRee (3 ^ (2 * m + 1))) ∨
    Nonempty (G ≃* CFSG.Open.walterJ1)

namespace WalterArith

theorem card_psl2_two_pow {f : ℕ} (hf : f ≠ 0) :
    Nat.card PSL(2, GaloisField 2 f) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have hcenter := CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (K := GaloisField 2 f) (CharTwo.neg_eq 1)
  have h := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center (K := GaloisField 2 f)
  rwa [hcenter, mul_one, GaloisField.card 2 f hf] at h

theorem card_psl2_odd_mul_two {p f : ℕ} [Fact p.Prime] (hp : Odd p) (hf : f ≠ 0) :
    Nat.card PSL(2, GaloisField p f) * 2 = p ^ f * ((p ^ f) ^ 2 - 1) := by
  have hne : (-1 : GaloisField p f) ≠ 1 := by
    refine Ring.neg_one_ne_one_of_char_ne_two ?_
    rw [ringChar.eq (GaloisField p f) p]
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hp) even_two
  have hcenter := CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_ne_one hne
  have h := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center (K := GaloisField p f)
  rwa [hcenter, GaloisField.card p f hf] at h

theorem exists_eight_mul_odd {q : ℕ} (hq : q % 8 = 3 ∨ q % 8 = 5) :
    ∃ r : ℕ, Odd r ∧ q * (q ^ 2 - 1) = 8 * r := by
  rcases hq with hq | hq
  · obtain ⟨k, rfl⟩ : ∃ k, q = 8 * k + 3 := ⟨q / 8, by omega⟩
    refine ⟨(8 * k + 3) * (8 * k ^ 2 + 6 * k + 1), Nat.odd_mul.mpr ⟨⟨4 * k + 1, by ring⟩,
      ⟨4 * k ^ 2 + 3 * k, by ring⟩⟩, ?_⟩
    rw [show (8 * k + 3) ^ 2 - 1 = 8 * (8 * k ^ 2 + 6 * k + 1) from
      Nat.sub_eq_of_eq_add (by ring)]
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, q = 8 * k + 5 := ⟨q / 8, by omega⟩
    refine ⟨(8 * k + 5) * (8 * k ^ 2 + 10 * k + 3), Nat.odd_mul.mpr ⟨⟨4 * k + 2, by ring⟩,
      ⟨4 * k ^ 2 + 5 * k + 1, by ring⟩⟩, ?_⟩
    rw [show (8 * k + 5) ^ 2 - 1 = 8 * (8 * k ^ 2 + 10 * k + 3) from
      Nat.sub_eq_of_eq_add (by ring)]
    ring

theorem three_pow_odd_mod_eight (m : ℕ) : 3 ^ (2 * m + 1) % 8 = 3 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, pow_add, Nat.mul_mod, ih]
    norm_num

theorem not_sixteen_dvd_ordRee (m : ℕ) : ¬ 16 ∣ ordRee (3 ^ (2 * m + 1)) := by
  have h8 := three_pow_odd_mod_eight m
  generalize 3 ^ (2 * m + 1) = q at h8 ⊢
  have hQ8 : q ^ 3 % 8 = 3 := by rw [Nat.pow_mod, h8]
  rw [ordRee]
  generalize q ^ 3 = Q at hQ8 ⊢
  obtain ⟨a, ha, ha2⟩ : ∃ a, Q + 1 = 4 * a ∧ a % 2 = 1 := ⟨(Q + 1) / 4, by omega, by omega⟩
  obtain ⟨b, hb, hb2⟩ : ∃ b, q - 1 = 2 * b ∧ b % 2 = 1 := ⟨(q - 1) / 2, by omega, by omega⟩
  have hodd : Q * a * b % 2 = 1 := by
    rw [Nat.mul_mod, Nat.mul_mod Q, ha2, hb2, show Q % 2 = 1 by omega]
  have hprod : Q * (Q + 1) * (q - 1) = 8 * (Q * a * b) := by
    rw [ha, hb]
    ring
  rw [hprod]
  generalize Q * a * b = c at hodd
  omega

theorem false_of_card_psl2_two_pow {f m : ℕ} (hf : 2 ≤ f) (hm : m % 2 = 1) (h7 : 7 ∣ 16 * m)
    (h : 2 ^ f * ((2 ^ f) ^ 2 - 1) = 16 * m) : False := by
  by_cases hf5 : 5 ≤ f
  · have h32 : 2 ^ 5 ∣ 2 ^ f := Nat.pow_dvd_pow 2 hf5
    have : 32 ∣ 16 * m := by
      rw [← h]
      exact Dvd.dvd.mul_right (by simpa using h32) _
    omega
  · have hf4 : f ≤ 4 := by omega
    interval_cases f <;> omega

end WalterArith

open WalterArith

theorem base_not_sylow {G : Type} [Group G] [Finite G] (hW : WalterAbelian) (H : Setting G) :
    2 ∣ H.V.index := by
  by_contra hidx
  have := H.simple
  have hVp : IsPGroup 2 H.V := IsPGroup.of_card (n := 4) (by rw [H.card_V]; norm_num)
  have hcomm : IsMulCommutative (hVp.toSylow hidx : Subgroup G) :=
    ⟨⟨fun a b => Subtype.ext (H.V_comm a.2 b.2)⟩⟩
  have hcard : Nat.card G = 16 * H.V.index := by
    rw [← Subgroup.card_mul_index H.V, H.card_V]
  have h7 : 7 ∣ Nat.card G := by
    have h168 : Nat.card (normalizer (H.E : Set G) ⊓ H.L : Subgroup G) ∣ Nat.card G :=
      Subgroup.card_subgroup_dvd_card _
    rw [H.card_normalizer_E] at h168
    exact (show 7 ∣ 168 by norm_num).trans h168
  rcases hW G H.nonabelian (hVp.toSylow hidx) hcomm with ⟨f, hf, ⟨e⟩⟩ |
      ⟨p, f, hp, hpodd, hf0, -, hmod, ⟨e⟩⟩ | ⟨m, -, hree⟩ | hJ
  · refine false_of_card_psl2_two_pow hf (by omega) (hcard ▸ h7) ?_
    rw [← hcard, Nat.card_congr e.toEquiv, card_psl2_two_pow (by omega)]
  · obtain ⟨r, hr, hqr⟩ := exists_eight_mul_odd hmod
    have h := card_psl2_odd_mul_two hpodd (by omega : f ≠ 0)
    rw [← Nat.card_congr e.toEquiv, hcard, hqr] at h
    obtain ⟨j, rfl⟩ := hr
    omega
  · exact not_sixteen_dvd_ordRee m ⟨H.V.index, hree.symm.trans hcard⟩
  · obtain ⟨e⟩ := hJ
    have : Nat.card G = 175560 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Walter.J1Props.card_walterJ1
    omega

end CFSG.EvenSporadicStandard.J1Std
