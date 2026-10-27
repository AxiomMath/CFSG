module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentE16Core
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltFixedCard

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.EvenSporadicStandard.HSStd
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem e16_alt_arith (r m : ℕ) (hr : 1 ≤ r) : 2 ^ (r - 1) * r.factorial * m.factorial ≠ 60 := by
  intro h
  have hm : 0 < m.factorial := Nat.factorial_pos m
  rcases Nat.lt_or_ge r 4 with hr4 | hr4
  · interval_cases r
    · have h1 : m.factorial = 60 := by simpa using h
      have h5 : m < 5 := by
        by_contra hm5
        have := Nat.factorial_le (show 5 ≤ m by omega)
        simp [Nat.factorial] at this
        omega
      interval_cases m <;> simp [Nat.factorial] at h1
    · have h1 : 4 * m.factorial = 60 := by simpa [Nat.factorial] using h
      have h5 : m < 5 := by
        by_contra hm5
        have := Nat.factorial_le (show 5 ≤ m by omega)
        simp [Nat.factorial] at this
        omega
      interval_cases m <;> simp [Nat.factorial] at h1
    · have h1 : 24 * m.factorial = 60 := by simpa [Nat.factorial] using h
      omega
  · have h8 : 2 ^ 3 ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h24 : (4 : ℕ).factorial ≤ r.factorial := Nat.factorial_le hr4
    have h24' : 24 ≤ r.factorial := by simpa [Nat.factorial] using h24
    have : 8 * 24 ≤ 2 ^ (r - 1) * r.factorial := Nat.mul_le_mul (by simpa using h8) h24'
    nlinarith

theorem e16_false_alt {K : Type} [Group K] [Finite K] (D : CatE16Data K) {n : ℕ} (hn : 5 ≤ n)
    (hn6 : n ≠ 6) (θ : K ≃* alternatingGroup (Fin n)) : False := by
  rcases Nat.lt_or_ge n 7 with h7 | h7
  · have h5 : n = 5 := by omega
    subst h5
    apply D.card_ne_sixty
    rw [Nat.card_congr θ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  · obtain ⟨r, hr1, -, hcard⟩ := card_fixedSubgroup_alt h7 θ D.orderOf_τ
    have h60 : Nat.card (fixedSubgroup D.τ) = 60 := by
      rw [← autCentralizer_eq_fixedSubgroup]
      exact D.card_fixed
    rw [h60] at hcard
    exact e16_alt_arith r (n - 2 * r) hr1 hcard.symm

end CFSG.ComponentClassification.CatFC
