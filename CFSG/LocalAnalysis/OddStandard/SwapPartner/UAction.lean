module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34SuzOuter

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

theorem card_mulAut_alternatingGroup (n : ℕ) (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    Nat.card (MulAut (alternatingGroup (Fin n))) = n.factorial := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6
  have hcard : Nat.card (MulAut (alternatingGroup (Fin n))) = Nat.card (Equiv.Perm (Fin n)) :=
    Nat.card_congr
      (Equiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n))) hbij).symm
  rw [hcard, Nat.card_perm, Nat.card_fin]

theorem padicValNat_two_factorial_eight : padicValNat 2 (Nat.factorial 8) = 7 := by
  have h : Nat.factorial 8 = 2 ^ 7 * 315 := by decide
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]

theorem padicValNat_two_factorial_ten : padicValNat 2 (Nat.factorial 10) = 8 := by
  have h : Nat.factorial 10 = 2 ^ 8 * 14175 := by decide
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 14175)]

theorem card_dvd_card_centralizer_mul_factorial {X : Type*} [Group X] [Finite X]
    (D : Subgroup X) [D.Normal] [Group.IsPerfect D] {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : (↥D ⧸ center ↥D) ≃* alternatingGroup (Fin n)) :
    Nat.card X ∣ Nat.card (centralizer (D : Set X)) * n.factorial := by
  have h := CFSG.SeitzReduction.SporadicRefine.card_dvd_card_centralizer_mul_card_mulAut
    (H := X) (D := D)
  rw [Nat.card_congr (MulAut.congr e).toEquiv,
    card_mulAut_alternatingGroup n hn hn6] at h
  exact h

theorem false_of_alternating_action {X : Type*} [Group X] [Finite X]
    (D : Subgroup X) [D.Normal] [Group.IsPerfect D] {n b k : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : (↥D ⧸ center ↥D) ≃* alternatingGroup (Fin n))
    (hC : ∀ U : Subgroup X, IsPGroup 2 U → U ≤ centralizer (D : Set X) → Nat.card U ≤ 2 ^ b)
    (hX : 2 ^ k ∣ Nat.card X) (hk : padicValNat 2 n.factorial + b < k) : False := by
  let C : Subgroup X := centralizer (D : Set X)
  have hneC : Nat.card C ≠ 0 := by
    haveI : Nonempty C := ⟨1⟩
    exact (Nat.card_pos (α := C)).ne'
  have hdvdC : 2 ^ padicValNat 2 (Nat.card C) ∣ Nat.card C :=
    (padicValNat_dvd_iff_le (p := 2) (a := Nat.card C)
      (n := padicValNat 2 (Nat.card C)) hneC).mpr le_rfl
  obtain ⟨S, hScard⟩ := Sylow.exists_subgroup_card_pow_prime (G := C) 2 hdvdC
  have hUcard : Nat.card (S.map C.subtype) = 2 ^ padicValNat 2 (Nat.card C) := by
    rw [Subgroup.card_subtype C S, hScard]
  have hUgrp : IsPGroup 2 (S.map C.subtype) :=
    IsPGroup.of_card (n := padicValNat 2 (Nat.card C)) hUcard
  have hUle : S.map C.subtype ≤ C := Subgroup.map_subtype_le S
  have hpow : 2 ^ padicValNat 2 (Nat.card C) ≤ 2 ^ b := by
    have h := hC (S.map C.subtype) hUgrp hUle
    rwa [hUcard] at h
  have hab : padicValNat 2 (Nat.card C) ≤ b :=
    (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp hpow
  have hdiv : Nat.card X ∣ Nat.card C * Nat.factorial n :=
    card_dvd_card_centralizer_mul_factorial D hn hn6 e
  have h2k : 2 ^ k ∣ Nat.card C * Nat.factorial n := dvd_trans hX hdiv
  have hnf : Nat.factorial n ≠ 0 := Nat.factorial_ne_zero n
  have hkle : k ≤ padicValNat 2 (Nat.card C) + padicValNat 2 (Nat.factorial n) := by
    have h := (padicValNat_dvd_iff_le (p := 2) (a := Nat.card C * Nat.factorial n)
      (n := k) (mul_ne_zero hneC hnf)).mp h2k
    rwa [padicValNat.mul hneC hnf] at h
  omega

end CFSG.OddStandard.AltStdSec.SwapPartner
