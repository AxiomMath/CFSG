module

public import CFSG.CharacterTheory.Burnside
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.GH74.QTGen4

theorem eq_of_dvd_of_modEq {n d s : ℕ} (hn : n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 9)
    (hs : s = 5 ∨ s = 7) (hd : d ∣ n) (hmod : n ≡ d [MOD s]) (hpos : 0 < d) : d = n := by
  have hle : d ≤ 9 := by
    have := Nat.le_of_dvd (by omega) hd
    omega
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> rcases hs with rfl | rfl <;>
    interval_cases d <;> unfold Nat.ModEq at hmod <;> omega

theorem eq_one_of_pow_eq_one {R : Type*} [Group R] [Finite R] {g : MulAut R} {s : ℕ}
    (hR : Nat.card R = 1 ∨ Nat.card R = 3 ∨ Nat.card R = 5 ∨ Nat.card R = 7 ∨ Nat.card R = 9)
    (hs : s = 5 ∨ s = 7) (hg : g ^ s = 1) : g = 1 := by
  classical
  have : Fact (Nat.Prime s) := ⟨by rcases hs with rfl | rfl <;> norm_num⟩
  have : Fintype R := Fintype.ofFinite R
  let F : Subgroup R :=
    { carrier := {x | g x = x}
      mul_mem' := fun {a b} ha hb => by
        change g a = a at ha
        change g b = b at hb
        change g (a * b) = a * b
        rw [map_mul, ha, hb]
      one_mem' := by
        change g 1 = 1
        exact map_one g
      inv_mem' := fun {a} ha => by
        change g a = a at ha
        change g a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hFmem : ∀ x, x ∈ F ↔ g x = x := fun x => Iff.rfl
  have hσ : (MulAut.toPerm R g) ^ s = 1 := by
    rw [← map_pow, hg, map_one]
  have hf : (show Function.End R from ⇑(MulAut.toPerm R g)) ^ s = 1 := by
    show (⇑(MulAut.toPerm R g))^[s] = id
    rw [Equiv.Perm.iterate_eq_pow, hσ]
    rfl
  have hmod : Nat.card R ≡ Nat.card F [MOD s] := by
    have h := Equiv.Perm.card_fixedPoints_modEq (α := R)
      (f := show Function.End R from ⇑(MulAut.toPerm R g)) (p := s) (n := 1)
      (by rw [pow_one]; exact hf)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
    exact h
  have hdvd : Nat.card F ∣ Nat.card R := Subgroup.card_subgroup_dvd_card F
  have hpos : 0 < Nat.card F := Nat.card_pos
  have hcard : Nat.card F = Nat.card R :=
    eq_of_dvd_of_modEq hR hs hdvd hmod hpos
  have htop : F = ⊤ := Subgroup.eq_top_of_card_eq F hcard
  have hfix : ∀ x, g x = x := fun x => (hFmem x).1 (by rw [htop]; exact Subgroup.mem_top x)
  exact MulEquiv.ext fun x => by rw [MulAut.one_apply]; exact hfix x

theorem eq_one_of_perfect_of_card_dvd_20160 {Q R : Type*} [Group Q] [Finite Q] [Group R]
    [Finite R] (hperf : commutator Q = ⊤) (hQ : Nat.card Q ∣ 20160)
    (hR : Nat.card R = 1 ∨ Nat.card R = 3 ∨ Nat.card R = 5 ∨ Nat.card R = 7 ∨ Nat.card R = 9)
    (φ : Q →* MulAut R) : φ = 1 := by
  classical
  have : Group.IsPerfect Q := Group.isPerfect_def.mpr hperf
  have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have : Finite φ.range := Finite.of_surjective
    (fun q : Q => (⟨φ q, MonoidHom.mem_range.2 ⟨q, rfl⟩⟩ : φ.range)) (fun h => by
      obtain ⟨q, hq⟩ := MonoidHom.mem_range.1 h.2
      exact ⟨q, Subtype.ext hq⟩)
  have : Fintype φ.range := Fintype.ofFinite φ.range
  have hHdvd : Nat.card φ.range ∣ 20160 := (Subgroup.card_range_dvd φ).trans hQ
  have hnot : ∀ s : ℕ, (s = 5 ∨ s = 7) → ¬ s ∣ Nat.card φ.range := by
    intro s hs hdvd
    have : Fact (Nat.Prime s) := ⟨by rcases hs with rfl | rfl <;> norm_num⟩
    have hdvd' : s ∣ Fintype.card φ.range := by
      rw [← Nat.card_eq_fintype_card]
      exact hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card s hdvd'
    have hxs : x ^ s = 1 := by
      rw [← hx]
      exact pow_orderOf_eq_one x
    have hxs' : (x : MulAut R) ^ s = 1 := by
      have := congrArg Subtype.val hxs
      simpa using this
    have hx1 : (x : MulAut R) = 1 := eq_one_of_pow_eq_one hR hs hxs'
    have hx' : x = 1 := Subtype.ext (by simpa using hx1)
    rw [hx', orderOf_one] at hx
    omega
  have hc5 : Nat.Coprime 5 (Nat.card φ.range) :=
    (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 (hnot 5 (Or.inl rfl))
  have hc7 : Nat.Coprime 7 (Nat.card φ.range) :=
    (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 (hnot 7 (Or.inr rfl))
  have hc35 : Nat.Coprime (Nat.card φ.range) 35 := by
    rw [show (35 : ℕ) = 5 * 7 by norm_num]
    exact Nat.Coprime.mul_right hc5.symm hc7.symm
  have h576 : Nat.card φ.range ∣ 576 := by
    refine Nat.Coprime.dvd_of_dvd_mul_right hc35 ?_
    have h20160 : (20160 : ℕ) = 576 * 35 := by norm_num
    rw [← h20160]
    exact hHdvd
  have h576' : Nat.card φ.range ∣ 2 ^ 6 * 3 ^ 2 := by
    norm_num
    exact h576
  obtain ⟨k1, k2, hk1, hk2, hk⟩ := exists_dvd_and_dvd_of_dvd_mul h576'
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk1
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hk2
  have hcard : Fintype.card φ.range = 2 ^ a * 3 ^ b := by
    rw [← Nat.card_eq_fintype_card, hk, ha, hb]
  have hsol : Group.IsSolvable φ.range :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      Nat.prime_two Nat.prime_three (by norm_num) hcard
  have hsub : Subsingleton φ.range := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable φ.range hsol
  refine MonoidHom.ext fun q => ?_
  have h1 := Subsingleton.elim (⟨φ q, MonoidHom.mem_range.2 ⟨q, rfl⟩⟩ : φ.range) 1
  have h2 := congrArg Subtype.val h1
  simpa using h2

end CFSG.GH74.QTGen4
