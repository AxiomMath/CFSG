module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.CGT.T75P

open Subgroup

private theorem a8x_gen_aux {G : Type*} [Group G] (P : Subgroup G) [Finite P] (s₀ : Finset G)
    (h₀ : closure (s₀ : Set G) ≤ P) (a : ℕ) (ha : 2 ^ a ≤ Nat.card (closure (s₀ : Set G)))
    (j : ℕ) :
    ∃ s : Finset G, s.card ≤ s₀.card + j ∧ closure (s : Set G) ≤ P ∧
      min (Nat.card P) (2 ^ (a + j)) ≤ Nat.card (closure (s : Set G)) := by
  classical
  induction j with
  | zero => exact ⟨s₀, by simp, h₀, (min_le_right _ _).trans (by simpa using ha)⟩
  | succ j ih =>
    obtain ⟨s, hs, hsP, hmin⟩ := ih
    by_cases hP : closure (s : Set G) = P
    · exact ⟨s, by omega, hsP, by rw [hP]; exact min_le_left _ _⟩
    · obtain ⟨y, hyP, hys⟩ : ∃ y ∈ P, y ∉ closure (s : Set G) := by
        by_contra hcon
        push Not at hcon
        exact hP (le_antisymm hsP hcon)
      have hKP : closure ((insert y s : Finset G) : Set G) ≤ P := by
        rw [Finset.coe_insert, closure_le]
        intro x hx
        rcases Set.mem_insert_iff.1 hx with rfl | hx
        · exact hyP
        · exact hsP (subset_closure hx)
      have hle : closure (s : Set G) ≤ closure ((insert y s : Finset G) : Set G) :=
        closure_mono (by simp [Finset.coe_insert, Set.subset_insert])
      have hy' : y ∈ closure ((insert y s : Finset G) : Set G) :=
        subset_closure (by simp)
      have : Finite (closure ((insert y s : Finset G) : Set G)) :=
        Finite.of_injective (inclusion hKP) (inclusion_injective hKP)
      have : Finite (closure (s : Set G)) :=
        Finite.of_injective (inclusion hsP) (inclusion_injective hsP)
      have hpos : 0 < Nat.card (closure ((insert y s : Finset G) : Set G)) := Nat.card_pos
      have hpos0 : 0 < Nat.card (closure (s : Set G)) := Nat.card_pos
      have hne : Nat.card (closure (s : Set G)) ≠
          Nat.card (closure ((insert y s : Finset G) : Set G)) := by
        intro heq
        have := eq_of_le_of_card_ge hle heq.ge
        exact hys (by rw [this]; exact hy')
      obtain ⟨m, hm⟩ := card_dvd_of_le hle
      have hdouble : 2 * Nat.card (closure (s : Set G)) ≤
          Nat.card (closure ((insert y s : Finset G) : Set G)) := by
        rcases m with _ | _ | m
        · omega
        · omega
        · rw [hm]
          calc 2 * Nat.card (closure (s : Set G)) = Nat.card (closure (s : Set G)) * 2 := by ring
            _ ≤ Nat.card (closure (s : Set G)) * (m + 1 + 1) :=
              Nat.mul_le_mul_left _ (by omega)
      have hlt : Nat.card (closure (s : Set G)) < Nat.card P := by
        refine lt_of_le_of_ne (card_le_of_le hsP) fun heq => hP ?_
        exact eq_of_le_of_card_ge hsP heq.ge
      have hpow : 2 ^ (a + (j + 1)) = 2 * 2 ^ (a + j) := by
        rw [← add_assoc, pow_succ]
        ring
      refine ⟨insert y s, ?_, hKP, ?_⟩
      · calc (insert y s).card ≤ s.card + 1 := Finset.card_insert_le _ _
          _ ≤ s₀.card + (j + 1) := by omega
      · omega

theorem a8x_exists_closure_card_le_log {G : Type*} [Group G] (P : Subgroup G) [Finite P] (j : ℕ)
    (hj : Nat.card P ≤ 2 ^ j) : ∃ s : Finset G, s.card ≤ j ∧ closure (s : Set G) = P := by
  classical
  obtain ⟨s, hs, hsP, hmin⟩ := a8x_gen_aux P (∅ : Finset G) (by simp) 0 (by simp) j
  refine ⟨s, by simpa using hs, eq_of_le_of_card_ge hsP ?_⟩
  simp only [zero_add] at hmin
  omega

theorem a8x_exists_closure_card_le_four {G : Type*} [Group G] (P : Subgroup G) [Finite P]
    (hP : Nat.card P ≤ 32) {x : G} (hx : x ∈ P) (hord : 4 ≤ orderOf x) :
    ∃ s : Finset G, s.card ≤ 4 ∧ closure (s : Set G) = P := by
  classical
  have h₀ : closure (({x} : Finset G) : Set G) ≤ P := by
    rw [Finset.coe_singleton, closure_le]
    simpa using hx
  have hc : Nat.card (closure (({x} : Finset G) : Set G)) = orderOf x := by
    rw [Finset.coe_singleton, ← zpowers_eq_closure, Nat.card_zpowers]
  obtain ⟨s, hs, hsP, hmin⟩ := a8x_gen_aux P {x} h₀ 2 (by rw [hc]; omega) 3
  refine ⟨s, by simpa using hs, eq_of_le_of_card_ge hsP ?_⟩
  omega

theorem a8x_four_le_orderOf {G : Type*} [Group G] {P : Subgroup G} (hP : Nat.card P = 32) {x : G}
    (hx : x ∈ P) (hx2 : x ^ 2 ≠ 1) : 4 ≤ orderOf x := by
  have hd : orderOf x ∣ 32 := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : P)
    rwa [hP, Subgroup.orderOf_mk] at this
  have hnd : ¬ orderOf x ∣ 2 := fun h => hx2 (orderOf_dvd_iff_pow_eq_one.1 h)
  by_contra hlt
  have hle : orderOf x ≤ 3 := by omega
  interval_cases h : orderOf x <;> omega

end CFSG.CGT.T75P
