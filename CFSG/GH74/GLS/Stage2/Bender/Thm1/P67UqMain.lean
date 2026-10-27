module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UqLift
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UqToral
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UqHeisCore

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.Classical

section Main

variable {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem false_of_u_inner_qp1 (hn : n = 4 ∨ n = 5) (hp2 : p ≠ 2) {r : ℕ} (hrp : r ≠ p)
    (hr1 : r ∣ p ^ f + 1)
    {V Z : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))}
    (hVD : V ≤ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (h2 : N2Cfg (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) r V Z)
    (h3 : N3Deriv (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) V Z) :
    False := by
  classical
  have : Finite K := h.finite
  obtain ⟨hr, hrodd, hVe, hVc, -, -, -, -, -⟩ := id h2
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact absurd hrodd (by decide)
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    omega
  have hn3 : 3 ≤ n := by omega
  have hrn : n < 2 * r := by omega
  have hq : ¬(n = 3 ∧ p ^ f = 2) := fun hh => by omega
  have h4 : 4 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by
      have := h.prime.two_le
      omega
    have h1 : p ≤ p ^ f := Nat.le_self_pow (by have := h.one_le; omega) p
    by_contra hlt
    have h3' : p ^ f = 3 := by omega
    rw [h3'] at hr1
    have : r ≤ 4 := Nat.le_of_dvd (by norm_num) hr1
    interval_cases r
    · norm_num at hr1
    · exact absurd hr (by norm_num)
  have hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => by
    have := hVe
    exact setLike_mul_comm hx hy
  have hVe' : ∀ v ∈ V, v ^ r = 1 := fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv
  have hs := isSimpleGroup_primeFormP_one h hn3 hq
  have hnab : ∃ a b : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact not_commute_primeFormP_one h hn3 hq hcon
  rcases uq_plane_classify h hn3 hrn hr hr2 hr1 V hVD hVc hVe' hVab with ⟨E, hE⟩ |
      ⟨hrdvd, a, b, u, hu, ha, hb, hab, -⟩
  · exact false_of_uq_toral_deriv h hn3 hp2 h4 hs hnab h2 h3 E hE
  · have hr5 : r = 5 ∧ n = 5 := by
      rcases hn with rfl | rfl
      · exfalso
        have h4' : r ∣ 2 ^ 2 := by simpa using hrdvd
        exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h4'))
      · exact ⟨(Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).1 hrdvd, rfl⟩
    obtain ⟨rfl, rfl⟩ := hr5
    exact false_of_uq5_heis h hp2 hr1 h2 h3 a b u hu ha hb hab

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm1
