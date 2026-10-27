module

public import CFSG.GH74.Generic.S1.KL5Ord
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4ExOrd
public import CFSG.GH74.Generic.S1.TQ3BarGeom

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74
open scoped MatrixGroups

namespace CFSG.GH74.Generic.S1

theorem kl3_dvd_card {S : Type} [Group S] [Finite S] {F : Type} [Field F] [Finite F]
    (hF3 : Nat.card F = 3) {Pb : Subgroup S} (e : ↥Pb ≃* SL(3, F)) : 5616 ∣ Nat.card S := by
  have h := Subgroup.card_subgroup_dvd_card Pb
  rwa [Nat.card_congr e.toEquiv, card_sl3_three hF3] at h

theorem kl3_false_of_card {S : Type} [Group S] {N : ℕ} (hS : Nat.card S = N)
    (hN : ¬ 5616 ∣ N) (h : 5616 ∣ Nat.card S) : False := hN (hS ▸ h)

theorem kl3_false_alt {S : Type} [Group S] {n : ℕ} (hn7 : 7 ≤ n) (hn11 : n ≤ 11)
    (e : S ≃* alternatingGroup (Fin n)) (h : 5616 ∣ Nat.card S) : False := by
  have hcard : Nat.card S = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv]
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [hcard] at h
  interval_cases n <;> revert h <;> decide

theorem kl3_false_sporadic
    {S : Type} [Group S]
    (hS : NativeSporadic.IsSporadic S .M11 ∨ NativeSporadic.IsSporadic S .M12 ∨
      NativeSporadic.IsSporadic S .M22 ∨ NativeSporadic.IsSporadic S .M23 ∨
      NativeSporadic.IsSporadic S .J1 ∨ NativeSporadic.IsSporadic S .J2 ∨
      NativeSporadic.IsSporadic S .J3 ∨ NativeSporadic.IsSporadic S .McL ∨
      NativeSporadic.IsSporadic S .Ly)
    (h : 5616 ∣ Nat.card S) : False := by
  rcases hS with hS | hS | hS | hS | hS | hS | hS | hS | hS
  · exact kl3_false_of_card (N := 7920)
      (card_eq_of_isSporadic (s := .M11) CFSG.Sporadic.Mathieu.card_M11 hS) (by decide) h
  · exact kl3_false_of_card (N := 95040) ((card_of_isSporadic_M12 hS).trans (by norm_num))
      (by decide) h
  · exact kl3_false_of_card (N := 443520) ((card_of_isSporadic_M22 hS).trans (by norm_num))
      (by decide) h
  · exact kl3_false_of_card (N := 10200960) ((card_of_isSporadic_M23 hS).trans (by norm_num))
      (by decide) h
  · exact kl3_false_of_card (N := 175560) ((card_of_isSporadic_J1 hS).trans (by norm_num))
      (by decide) h
  · exact kl3_false_of_card (N := 604800) ((card_of_isSporadic_J2 hS).trans (by norm_num))
      (by decide) h
  · exact kl3_false_of_card (N := 50232960) ((card_of_isSporadic_J3 hS).trans (by norm_num))
      (by decide) h
  · exact kl3_false_of_card (N := 898128000) ((card_of_isSporadic_McL hS).trans (by norm_num))
      (by decide) h
  · exact kl3_false_of_card (N := 2 ^ 8 * 3 ^ 7 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67)
      (card_of_isSporadic_Ly hS) (by decide) h

theorem kl3_false_small {S : Type} [Group S]
    (hS : LieModel S .PSL 2 2 3 ∨ LieModel S .PSL 2 2 4 ∨ LieModel S .PSL 3 2 2 ∨
      LieModel S .PSU 3 2 2 ∨ LieModel S .twistedB2 0 2 3) (h : 5616 ∣ Nat.card S) : False := by
  rcases hS with hS | hS | hS | hS | hS
  · exact kl3_false_of_card (N := 504) ((card_of_lieModel_PSL (n := 2) (by norm_num) hS).trans
      (by decide)) (by decide) h
  · exact kl3_false_of_card (N := 4080) ((card_of_lieModel_PSL (n := 2) (by norm_num) hS).trans
      (by decide)) (by decide) h
  · exact kl3_false_of_card (N := 20160) ((card_of_lieModel_PSL (n := 3) (by norm_num) hS).trans
      (by decide)) (by decide) h
  · have hc := kl5_card_mul_gcd_psu_three (statedClassicalModel_of_lieModel (by norm_num) hS)
    norm_num at hc
    exact kl3_false_of_card (N := 62400) hc (by decide) h
  · exact kl3_false_of_card (N := 29120) ((card_of_lieModel_twistedB2 hS).trans
      (by decide)) (by decide) h

theorem kl3_false_ree
    {S : Type} [Group S] {f' : ℕ}
    (hS : LieModel S .twistedG2 0 3 f') (h : 5616 ∣ Nat.card S) : False := by
  obtain ⟨k, -, hcard⟩ := card_of_lieModel_twistedG2 hS
  have h16 : 16 ∣ Nat.card S := (by norm_num : 16 ∣ 5616).trans h
  rw [hcard] at h16
  have := CFSG.GH74.GLS.IVK.Proofs2.Ivk94.ordRee_pow_three_mod k
  omega

end CFSG.GH74.Generic.S1
