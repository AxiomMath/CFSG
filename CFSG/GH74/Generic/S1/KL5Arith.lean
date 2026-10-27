module

public import CFSG.GH74.Generic.S1.KL5Ord
public import CFSG.GH74.Orders.LieType
public import CFSG.GH74.Orders.Sporadic
public import CFSG.Sporadic.Mathieu.M11

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

namespace CFSG.GH74.Generic.S1

theorem kl5_not_pow_dvd {N M : ℕ} (hN : 0 < N) (hM : N < M ^ 4) (h3 : ¬ 3 ^ 8 ∣ N)
    (hr : ∀ r < M, r.Prime → 5 ≤ r → ¬ r ^ 4 ∣ N) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) : ¬ p ^ (4 * f) ∣ N := by
  intro hd
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h5
  have h4 : p ^ 4 ∣ N := (pow_dvd_pow p (by omega : 4 ≤ 4 * f)).trans hd
  have hpM : p < M := by
    by_contra hge
    have h1 : M ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left (not_lt.1 hge) 4
    have h2 := Nat.le_of_dvd hN h4
    omega
  by_cases hp3 : p = 3
  · subst hp3
    have hf2 : 2 ≤ f := by
      by_contra hlt
      have : f = 1 := by omega
      subst this
      simp at h5
    exact h3 ((pow_dvd_pow 3 (by omega : 8 ≤ 4 * f)).trans hd)
  · have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h | h
      · exact absurd h hp2
      · exact absurd h hp3
      · subst h
        norm_num at hp
      · exact h
    exact hr p hpM hp hp5 h4

theorem kl5_false_of_card {S : Type} [Group S] [Finite S] {A B : Subgroup S} {p f : ℕ}
    (h : KL5Cfg A B p f) {N M : ℕ} (hS : Nat.card S = N) (hN : 0 < N) (hM : N < M ^ 4)
    (h3 : ¬ 3 ^ 8 ∣ N) (hr : ∀ r < M, r.Prime → 5 ≤ r → ¬ r ^ 4 ∣ N) : False := by
  have hd := kl5_dvd_card h
  rw [hS] at hd
  obtain ⟨-, -, -, hp, hp2, h5, -⟩ := h
  exact kl5_not_pow_dvd hN hM h3 hr hp hp2 h5 hd

theorem kl5_false_alt {S : Type} [Group S] [Finite S] {n : ℕ} (hn7 : 7 ≤ n) (hn11 : n ≤ 11)
    (e : S ≃* alternatingGroup (Fin n)) {A B : Subgroup S} {p f : ℕ} (h : KL5Cfg A B p f) :
    False := by
  have hcard : Nat.card S = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv]
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  interval_cases n
  · exact kl5_false_of_card h (N := 2520) (M := 8) (by rw [hcard]; decide) (by norm_num)
      (by norm_num) (by decide) (by decide +kernel)
  · exact kl5_false_of_card h (N := 20160) (M := 12) (by rw [hcard]; decide) (by norm_num)
      (by norm_num) (by decide) (by decide +kernel)
  · exact kl5_false_of_card h (N := 181440) (M := 21) (by rw [hcard]; decide) (by norm_num)
      (by norm_num) (by decide) (by decide +kernel)
  · exact kl5_false_of_card h (N := 1814400) (M := 37) (by rw [hcard]; decide) (by norm_num)
      (by norm_num) (by decide) (by decide +kernel)
  · exact kl5_false_of_card h (N := 19958400) (M := 67) (by rw [hcard]; decide) (by norm_num)
      (by norm_num) (by decide) (by decide +kernel)

theorem kl5_false_M11 {S : Type} [Group S] [Finite S]
    (hS : NativeSporadic.IsSporadic S .M11) {A B : Subgroup S} {p f : ℕ}
    (h : KL5Cfg A B p f) : False :=
  kl5_false_of_card h (N := 7920) (M := 10)
    (CFSG.GH74.card_eq_of_isSporadic (s := .M11) CFSG.Sporadic.Mathieu.card_M11 hS)
    (by norm_num) (by norm_num) (by decide) (by decide +kernel)

theorem kl5_false_M12 {S : Type} [Group S] [Finite S]
    (hS : NativeSporadic.IsSporadic S .M12) {A B : Subgroup S} {p f : ℕ}
    (h : KL5Cfg A B p f) : False :=
  kl5_false_of_card h (N := 95040) (M := 18)
    ((CFSG.GH74.card_of_isSporadic_M12 hS).trans (by norm_num))
    (by norm_num) (by norm_num) (by decide) (by decide +kernel)

theorem kl5_false_M22 {S : Type} [Group S] [Finite S]
    (hS : NativeSporadic.IsSporadic S .M22) {A B : Subgroup S} {p f : ℕ}
    (h : KL5Cfg A B p f) : False :=
  kl5_false_of_card h (N := 443520) (M := 26)
    ((CFSG.GH74.card_of_isSporadic_M22 hS).trans (by norm_num))
    (by norm_num) (by norm_num) (by decide) (by decide +kernel)

theorem kl5_false_M23
    {S : Type} [Group S] [Finite S] (hS : NativeSporadic.IsSporadic S .M23)
    {A B : Subgroup S} {p f : ℕ} (h : KL5Cfg A B p f) : False :=
  kl5_false_of_card h (N := 10200960) (M := 57)
    ((CFSG.GH74.card_of_isSporadic_M23 hS).trans (by norm_num))
    (by norm_num) (by norm_num) (by decide) (by decide +kernel)

theorem kl5_false_J1 {S : Type} [Group S] [Finite S]
    (hS : NativeSporadic.IsSporadic S .J1) {A B : Subgroup S} {p f : ℕ}
    (h : KL5Cfg A B p f) : False :=
  kl5_false_of_card h (N := 175560) (M := 21)
    ((CFSG.GH74.card_of_isSporadic_J1 hS).trans (by norm_num))
    (by norm_num) (by norm_num) (by decide) (by decide +kernel)

theorem kl5_false_J2 {S : Type} [Group S] [Finite S]
    (hS : NativeSporadic.IsSporadic S .J2) {A B : Subgroup S} {p f : ℕ}
    (h : KL5Cfg A B p f) : False :=
  kl5_false_of_card h (N := 604800) (M := 28)
    ((CFSG.GH74.card_of_isSporadic_J2 hS).trans (by norm_num))
    (by norm_num) (by norm_num) (by decide) (by decide +kernel)

theorem kl5_false_J3 {S : Type} [Group S] [Finite S]
    (hS : NativeSporadic.IsSporadic S .J3) {A B : Subgroup S} {p f : ℕ}
    (h : KL5Cfg A B p f) : False :=
  kl5_false_of_card h (N := 50232960) (M := 85)
    ((CFSG.GH74.card_of_isSporadic_J3 hS).trans (by norm_num))
    (by norm_num) (by norm_num) (by decide) (by decide +kernel)

theorem kl5_false_McL {S : Type} [Group S] [Finite S]
    (hS : NativeSporadic.IsSporadic S .McL) {A B : Subgroup S} {p f : ℕ}
    (h : KL5Cfg A B p f) : False :=
  kl5_false_of_card h (N := 898128000) (M := 175)
    ((CFSG.GH74.card_of_isSporadic_McL hS).trans (by norm_num))
    (by norm_num) (by norm_num) (by decide) (by decide +kernel)

theorem kl5_false_sporadic
    {S : Type} [Group S] [Finite S]
    (hS : NativeSporadic.IsSporadic S .M11 ∨ NativeSporadic.IsSporadic S .M12 ∨
      NativeSporadic.IsSporadic S .M22 ∨ NativeSporadic.IsSporadic S .M23 ∨
      NativeSporadic.IsSporadic S .J1 ∨ NativeSporadic.IsSporadic S .J2 ∨
      NativeSporadic.IsSporadic S .J3 ∨ NativeSporadic.IsSporadic S .McL)
    {A B : Subgroup S} {p f : ℕ} (h : KL5Cfg A B p f) : False := by
  rcases hS with hS | hS | hS | hS | hS | hS | hS | hS
  · exact kl5_false_M11 hS h
  · exact kl5_false_M12 hS h
  · exact kl5_false_M22 hS h
  · exact kl5_false_M23 hS h
  · exact kl5_false_J1 hS h
  · exact kl5_false_J2 hS h
  · exact kl5_false_J3 hS h
  · exact kl5_false_McL hS h

theorem kl5_false_small {S : Type} [Group S] [Finite S]
    (hS : LieModel S .PSL 2 2 3 ∨ LieModel S .PSL 2 2 4 ∨ LieModel S .PSL 3 2 2 ∨
      LieModel S .PSU 3 2 2 ∨ LieModel S .twistedB2 0 2 3)
    {A B : Subgroup S} {p f : ℕ} (h : KL5Cfg A B p f) : False := by
  rcases hS with hS | hS | hS | hS | hS
  · have hc := CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hS
    exact kl5_false_of_card h (N := 504) (M := 5) (hc.trans (by decide)) (by norm_num)
      (by norm_num) (by decide) (by decide +kernel)
  · have hc := CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hS
    exact kl5_false_of_card h (N := 4080) (M := 8) (hc.trans (by decide)) (by norm_num)
      (by norm_num) (by decide) (by decide +kernel)
  · have hc := CFSG.GH74.card_of_lieModel_PSL (n := 3) (by norm_num) hS
    exact kl5_false_of_card h (N := 20160) (M := 12) (hc.trans (by decide)) (by norm_num)
      (by norm_num) (by decide) (by decide +kernel)
  · have hc := kl5_card_mul_gcd_psu_three (CFSG.GH74.statedClassicalModel_of_lieModel
      (by norm_num) hS)
    exact kl5_false_of_card h (N := 62400) (M := 16) (by norm_num at hc; exact hc)
      (by norm_num) (by norm_num) (by decide) (by decide +kernel)
  · have hc := CFSG.GH74.card_of_lieModel_twistedB2 hS
    exact kl5_false_of_card h (N := 29120) (M := 14) (hc.trans (by decide)) (by norm_num)
      (by norm_num) (by decide) (by decide +kernel)

end CFSG.GH74.Generic.S1
