module

public import CFSG.CGT.PushingUpLit.BHSSym.Coxeter
public import Mathlib.GroupTheory.Perm.Cycle.Factors

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv Equiv.Perm

section Swaps

variable {α : Type*} [DecidableEq α]

theorem eq_swap_of_apply_ne {σ : Perm α} (hσ : σ.IsSwap) {x : α} (hx : σ x ≠ x) :
    σ = swap x (σ x) := by
  obtain ⟨a, b, hab, rfl⟩ := hσ
  by_cases h1 : x = a
  · subst h1
    simp
  · by_cases h2 : x = b
    · subst h2
      simp [swap_comm]
    · exact absurd (swap_apply_of_ne_of_ne h1 h2) hx

theorem apply_eq_of_commute_of_ne {σ τ : Perm α} (hσ : σ.IsSwap) (hτ : τ.IsSwap)
    (hcomm : σ * τ = τ * σ) (hne : σ ≠ τ) {x : α} (hx : σ x ≠ x) : τ x = x := by
  by_contra hτx
  have e1 := eq_swap_of_apply_ne hσ hx
  have e2 := eq_swap_of_apply_ne hτ hτx
  have hpq : σ x ≠ τ x := fun h => hne (by rw [e1, e2, h])
  have hcx : σ (τ x) = τ (σ x) := by
    have := congrArg (fun f : Perm α => f x) hcomm
    simpa using this
  generalize σ x = p at *
  generalize τ x = q at *
  subst e1 e2
  have h1 : swap x p q = q := swap_apply_of_ne_of_ne hτx (Ne.symm hpq)
  have h2 : swap x q p = p := swap_apply_of_ne_of_ne hx hpq
  rw [h1, h2] at hcx
  exact hpq hcx.symm

theorem exists_apply_ne_and_apply_eq {σ τ : Perm α} (hσ : σ.IsSwap) (hτ : τ.IsSwap)
    (hne : σ ≠ τ) : ∃ w, σ w ≠ w ∧ τ w = w := by
  obtain ⟨a, b, hab, rfl⟩ := hσ
  by_cases ha : τ a = a
  · exact ⟨a, by simpa using hab.symm, ha⟩
  · by_cases hb : τ b = b
    · exact ⟨b, by simpa using hab, hb⟩
    · exfalso
      apply hne
      have e := eq_swap_of_apply_ne hτ ha
      have hbτ : swap a (τ a) b ≠ b := by rw [← e]; exact hb
      have : b = τ a := by
        by_contra hbp
        exact hbτ (swap_apply_of_ne_of_ne (Ne.symm hab) hbp)
      rw [e, ← this]

theorem swap_mul_comm_of_fixes {τ : Perm α} {w a : α} (hw : τ w = w) (ha : τ a = a) :
    swap w a * τ = τ * swap w a := by
  have h := swap_apply_apply τ w a
  rw [hw, ha] at h
  calc swap w a * τ = (τ * swap w a * τ⁻¹) * τ := by rw [← h]
    _ = τ * swap w a := by group

theorem swap_mul_swap_pow_three {p q r : α} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (swap p q * swap q r) ^ 3 = 1 :=
  CFSG.CGT.PushingUpLit.BHSSym.pow_three_of_braid (swap_mul_self p q) (swap_mul_self q r)
    (CFSG.Permutation.SymmetricCoxeter.swap_braid hpq hpr hqr)

theorem eq_swap_of_apply_ne_of_apply_ne {σ : Perm α} (hσ : σ.IsSwap) {p q : α} (hpq : p ≠ q)
    (hp : σ p ≠ p) (hq : σ q ≠ q) : σ = swap p q := by
  have e := eq_swap_of_apply_ne hσ hp
  have : q = σ p := by
    by_contra hqp
    have hq' : swap p (σ p) q ≠ q := by rw [← e]; exact hq
    exact hq' (swap_apply_of_ne_of_ne (Ne.symm hpq) hqp)
  rw [e, ← this]

theorem exists_common_point {u v : Perm α} (hu : u.IsSwap) (hv : v.IsSwap) (hne : u ≠ v)
    (h3 : (u * v) ^ 3 = 1) : ∃ p, u p ≠ p ∧ v p ≠ p := by
  by_contra hno
  push Not at hno
  have hdisj : Disjoint u v := fun x => by
    by_cases hx : u x = x
    · exact Or.inl hx
    · exact Or.inr (hno x hx)
  have hcomm : Commute u v := hdisj.commute
  have hu2 : u * u = 1 := by
    obtain ⟨a, b, -, rfl⟩ := hu
    exact swap_mul_self a b
  have hv2 : v * v = 1 := by
    obtain ⟨a, b, -, rfl⟩ := hv
    exact swap_mul_self a b
  have h1 : (u * v) ^ 3 = u * v := by
    rw [hcomm.mul_pow]
    have hu3 : u ^ 3 = u := by rw [pow_succ, sq, hu2, one_mul]
    have hv3 : v ^ 3 = v := by rw [pow_succ, sq, hv2, one_mul]
    rw [hu3, hv3]
  have h2 : u * v = 1 := by rw [← h1]; exact h3
  apply hne
  calc u = u * (v * v) := by rw [hv2, mul_one]
    _ = (u * v) * v := by rw [mul_assoc]
    _ = v := by rw [h2, one_mul]

theorem exists_swap_completion {k : ℕ} (hk : 2 ≤ k) {t : ℕ → Perm α}
    (hsw : ∀ i < k, (t i).IsSwap)
    (hcomm : ∀ i j, i + 2 ≤ j → j < k → t i * t j = t j * t i)
    (hne : ∀ i j, i < k → j < k → i ≠ j → t i ≠ t j)
    {c : Perm α} (hc : c.IsSwap) (hcne : ∀ i < k, c ≠ t i)
    (hccomm : ∀ i < k, c * t i = t i * c) :
    ∃ d : Perm α, d.IsSwap ∧ (t (k - 1) * d) ^ 3 = 1 ∧ (d * c) ^ 3 = 1 ∧
      (∀ i, i + 2 ≤ k → d * t i = t i * d) ∧ (∀ i < k, d ≠ t i) ∧ d ≠ c := by
  have hv : (t (k - 1)).IsSwap := hsw (k - 1) (by omega)
  have hv' : (t (k - 2)).IsSwap := hsw (k - 2) (by omega)
  obtain ⟨w, hw1, hw2⟩ := exists_apply_ne_and_apply_eq hv hv'
    (hne _ _ (by omega) (by omega) (by omega))
  obtain ⟨a, b, hab, hcab⟩ := id hc
  have hca : c a ≠ a := by rw [hcab]; simpa using hab.symm
  have hcb : c b ≠ b := by rw [hcab]; simpa using hab
  have hfixa : ∀ i < k, t i a = a := fun i hi =>
    apply_eq_of_commute_of_ne hc (hsw i hi) (hccomm i hi) (hcne i hi) hca
  have hfixb : ∀ i < k, t i b = b := fun i hi =>
    apply_eq_of_commute_of_ne hc (hsw i hi) (hccomm i hi) (hcne i hi) hcb
  have hcw : c w = w :=
    apply_eq_of_commute_of_ne hv hc (hccomm (k - 1) (by omega)).symm
      (hcne (k - 1) (by omega)).symm hw1
  obtain ⟨w', hw'⟩ : ∃ w', w' = t (k - 1) w := ⟨_, rfl⟩
  have hvw : t (k - 1) = swap w w' := by
    rw [hw']
    exact eq_swap_of_apply_ne hv hw1
  have hw'w : w' ≠ w := by rw [hw']; exact hw1
  have hwa : w ≠ a := fun h => hw1 (by rw [h]; exact hfixa (k - 1) (by omega))
  have hwb : w ≠ b := fun h => hw1 (by rw [h]; exact hfixb (k - 1) (by omega))
  have hw'a : w' ≠ a := by
    intro h
    have h1 : t (k - 1) w' = w := by rw [hvw]; exact swap_apply_right w w'
    rw [h, hfixa (k - 1) (by omega)] at h1
    exact hwa h1.symm
  refine ⟨swap w a, ⟨w, a, hwa, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hvw, swap_comm w w']
    exact swap_mul_swap_pow_three hw'w hw'a hwa
  · rw [hcab]
    exact swap_mul_swap_pow_three hwa hwb hab
  · intro i hi
    refine swap_mul_comm_of_fixes ?_ (hfixa i (by omega))
    by_cases hik : i = k - 2
    · rw [hik]
      exact hw2
    · exact apply_eq_of_commute_of_ne hv (hsw i (by omega)) (hcomm i (k - 1) (by omega)
        (by omega)).symm (hne (k - 1) i (by omega) (by omega) (by omega)) hw1
  · intro i hi h
    have h1 := hfixa i hi
    rw [← h, swap_apply_right] at h1
    exact hwa h1
  · intro h
    have h1 := hcw
    rw [← h, swap_apply_left] at h1
    exact hwa h1.symm

theorem commute_of_chain_three {u v w s : Perm α} (hu : u.IsSwap) (hv : v.IsSwap)
    (hw : w.IsSwap) (hs : s.IsSwap) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h3uv : (u * v) ^ 3 = 1) (h3vw : (v * w) ^ 3 = 1) (hcuw : u * w = w * u)
    (hsu : s * u = u * s) (hsw : s * w = w * s) (hsune : s ≠ u) (hswne : s ≠ w) :
    s * v = v * s := by
  obtain ⟨p, hp1, hp2⟩ := exists_common_point hu hv huv h3uv
  obtain ⟨q, hq1, hq2⟩ := exists_common_point hv hw hvw h3vw
  have hpq : p ≠ q := by
    rintro rfl
    exact hq2 (apply_eq_of_commute_of_ne hu hw hcuw huw hp1)
  have hsp : s p = p := apply_eq_of_commute_of_ne hu hs hsu.symm hsune.symm hp1
  have hsq : s q = q := apply_eq_of_commute_of_ne hw hs hsw.symm hswne.symm hq2
  have hvpq : v = swap p q := eq_swap_of_apply_ne_of_apply_ne hv hpq hp2 hq1
  rw [hvpq]
  exact (swap_mul_comm_of_fixes hsp hsq).symm

end Swaps

section Involutions

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem mem_of_involution {B : Subgroup (Perm α)} {π : Perm α} (hπ : π * π = 1)
    (hB : ∀ s : Perm α, s.IsSwap → s * π = π * s → s ≠ π → s ∈ B) :
    π ∈ B ∨ π.IsSwap := by
  by_cases hsw : π.IsSwap
  · exact Or.inr hsw
  · left
    have key : ∀ c ∈ π.cycleFactorsFinset, c ∈ B := by
      intro c hc
      have hcyc := mem_cycleFactorsFinset_iff.1 hc
      have hcomm : Commute c π := self_mem_cycle_factors_commute hc
      have hc2 : c * c = 1 := by
        ext x
        by_cases hx : x ∈ c.support
        · have h1 : c x = π x := hcyc.2 x hx
          have hcx : c x ∈ c.support := apply_mem_support.2 hx
          have h2 : c (c x) = π (c x) := hcyc.2 _ hcx
          have h3 := congrArg (fun f : Perm α => f x) hπ
          simp only [Perm.mul_apply, Perm.one_apply] at h3 ⊢
          rw [h2, h1]
          exact h3
        · have : c x = x := notMem_support.1 hx
          simp [Perm.mul_apply, this]
      have hcsw : c.IsSwap := by
        have h1 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hc2)
        have hord : orderOf c = 2 := by
          rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
          · exact absurd (orderOf_eq_one_iff.1 h) hcyc.1.ne_one
          · exact h
        rw [← card_support_eq_two, ← hcyc.1.orderOf]
        exact hord
      refine hB c hcsw hcomm ?_
      rintro rfl
      exact hsw hcsw
    rw [← cycleFactorsFinset_noncommProd π]
    exact Subgroup.noncommProd_mem B _ key

end Involutions

end CFSG.OddStandard.AltStdSec
