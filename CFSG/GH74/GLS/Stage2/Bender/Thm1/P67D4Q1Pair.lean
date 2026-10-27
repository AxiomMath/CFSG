module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem plane_le_of_pair {Y : Type*} [Group Y] (E : Subgroup Y) (hcard : Nat.card E = 3 ^ 2)
    (hE3 : ∀ e ∈ E, e ^ 3 = 1) {v n : Y} (hv : v ∈ E) (hn : n ∈ E) (hv1 : v ≠ 1)
    (hnv : n ∉ Subgroup.zpowers v) (S : Subgroup Y) (hvS : v ∈ S) (hnS : n ∈ S) : E ≤ S := by
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  set C : Subgroup Y := E ⊓ S with hC
  have hCE : C ≤ E := inf_le_left
  have hvC : v ∈ C := Subgroup.mem_inf.2 ⟨hv, hvS⟩
  have hnC : n ∈ C := Subgroup.mem_inf.2 ⟨hn, hnS⟩
  have hzC : Subgroup.zpowers v ≤ C := (Subgroup.zpowers_le).2 hvC
  have hord : orderOf v = 3 := orderOf_eq_prime (hE3 v hv) hv1
  have hzcard : Nat.card (Subgroup.zpowers v) = 3 := by rw [Nat.card_zpowers, hord]
  have hdvd9 : Nat.card C ∣ 3 ^ 2 := hcard ▸ Subgroup.card_dvd_of_le hCE
  have hdvd3 : 3 ∣ Nat.card C := hzcard ▸ Subgroup.card_dvd_of_le hzC
  obtain ⟨i, hi, hCi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd9
  have hfinC : Finite C :=
    Finite.of_injective (Subgroup.inclusion hCE) (Subgroup.inclusion_injective hCE)
  have hCcard : Nat.card C = 3 ^ 2 := by
    interval_cases i
    · exfalso
      rw [pow_zero] at hCi
      rw [hCi] at hdvd3
      omega
    · exfalso
      have hCz : Nat.card C ≤ Nat.card (Subgroup.zpowers v) := by rw [hzcard, hCi]; norm_num
      exact hnv ((Subgroup.eq_of_le_of_card_ge hzC hCz) ▸ hnC)
    · exact hCi
  have hEC : C = E := Subgroup.eq_of_le_of_card_ge hCE (by rw [hcard, hCcard])
  rw [← hEC]
  exact inf_le_right

end CFSG.GH74.GLS.Stage2.Bender.Thm1
