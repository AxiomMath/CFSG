module

public import Mathlib.GroupTheory.Perm.Centralizer
import CFSG.LocalAnalysis.OddStandard.AltStdSecPartSwap

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv Equiv.Perm Subgroup

section Card

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem cycleType_eq_replicate_two {σ : Perm α} (h2 : σ * σ = 1) :
    σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact cycleType_of_pow_prime_eq_one (by rw [pow_two]; exact h2)

theorem card_support_eq_two_mul_card_cycleType {σ : Perm α} (h2 : σ * σ = 1) :
    σ.support.card = 2 * Multiset.card σ.cycleType := by
  set k := Multiset.card σ.cycleType with hk
  have hct : σ.cycleType = Multiset.replicate k 2 := cycleType_eq_replicate_two h2
  rw [← sum_cycleType, hct, Multiset.sum_replicate, smul_eq_mul, mul_comm]

theorem nat_card_centralizer_of_mul_self {σ : Perm α} (h2 : σ * σ = 1) :
    Nat.card (centralizer ({σ} : Set (Perm α))) =
      (Fintype.card α - 2 * Multiset.card σ.cycleType).factorial *
        2 ^ Multiset.card σ.cycleType * (Multiset.card σ.cycleType).factorial := by
  set k := Multiset.card σ.cycleType with hk
  have hct : σ.cycleType = Multiset.replicate k 2 := cycleType_eq_replicate_two h2
  rw [nat_card_centralizer, hct, Multiset.sum_replicate, Multiset.prod_replicate, smul_eq_mul,
    Multiset.toFinset_replicate, mul_comm k 2]
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · simp [h0]
  · rw [ite_eq_right_iff.2 (fun h => absurd h (by omega)), Finset.prod_singleton,
      Multiset.count_replicate_self]

theorem nat_card_centralizer_of_isSwap {σ : Perm α} (hσ : σ.IsSwap) :
    Nat.card (centralizer ({σ} : Set (Perm α))) = 2 * (Fintype.card α - 2).factorial := by
  have h2 : σ * σ = 1 := by
    obtain ⟨x, y, -, rfl⟩ := hσ
    exact swap_mul_self x y
  have hs := card_support_eq_two_mul_card_cycleType h2
  rw [card_support_eq_two.2 hσ] at hs
  have hk : Multiset.card σ.cycleType = 1 := by omega
  rw [nat_card_centralizer_of_mul_self h2, hk]
  simp [mul_comm]

theorem factorial_mul_two_pow_mul_factorial_lt (a k : ℕ) (hk : 2 ≤ k) (ha : 7 ≤ a + 2 * k) :
    a.factorial * 2 ^ k * k.factorial < 2 * (a + 2 * k - 2).factorial := by
  have hA : 0 < a.factorial := Nat.factorial_pos _
  rcases (by omega : k = 2 ∨ k = 3 ∨ 4 ≤ k) with rfl | rfl | hk4
  · have h : a + 2 * 2 - 2 = a + 1 + 1 := by omega
    have e : (a + 1 + 1).factorial = (a + 1 + 1) * ((a + 1) * a.factorial) := by
      rw [Nat.factorial_succ, Nat.factorial_succ]
    have f2 : Nat.factorial 2 = 2 := rfl
    rw [h, e, f2]
    have ha3 : 3 ≤ a := by omega
    have h4 : 4 < (a + 1 + 1) * (a + 1) := by nlinarith
    calc a.factorial * 2 ^ 2 * 2 = 4 * 2 * a.factorial := by ring
      _ < (a + 1 + 1) * (a + 1) * 2 * a.factorial := by
          apply Nat.mul_lt_mul_of_pos_right _ hA; omega
      _ = 2 * ((a + 1 + 1) * ((a + 1) * a.factorial)) := by ring
  · have h : a + 2 * 3 - 2 = a + 1 + 1 + 1 + 1 := by omega
    have e : (a + 1 + 1 + 1 + 1).factorial =
        (a + 1 + 1 + 1 + 1) * ((a + 1 + 1 + 1) * ((a + 1 + 1) * ((a + 1) * a.factorial))) := by
      rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    have f3 : Nat.factorial 3 = 6 := rfl
    rw [h, e, f3]
    have h1 : 5 ≤ a + 1 + 1 + 1 + 1 := by omega
    have h2 : 4 ≤ a + 1 + 1 + 1 := by omega
    have h3 : 3 ≤ a + 1 + 1 := by omega
    have h4 : 2 ≤ a + 1 := by omega
    have h24 : 120 ≤ (a + 1 + 1 + 1 + 1) * (a + 1 + 1 + 1) * (a + 1 + 1) * (a + 1) := by
      calc 120 = 5 * 4 * 3 * 2 := by norm_num
        _ ≤ (a + 1 + 1 + 1 + 1) * (a + 1 + 1 + 1) * (a + 1 + 1) * (a + 1) := by gcongr
    calc a.factorial * 2 ^ 3 * 6 = 48 * a.factorial := by ring
      _ < (a + 1 + 1 + 1 + 1) * (a + 1 + 1 + 1) * (a + 1 + 1) * (a + 1) * 2 * a.factorial := by
          apply Nat.mul_lt_mul_of_pos_right _ hA; omega
      _ = 2 * ((a + 1 + 1 + 1 + 1) * ((a + 1 + 1 + 1) * ((a + 1 + 1) * ((a + 1) *
            a.factorial)))) := by ring
  · have h1 := two_pow_mul_factorial_lt k hk4
    have h2 : a.factorial * (2 * k - 2).factorial ≤ (a + 2 * k - 2).factorial := by
      have := Nat.factorial_mul_factorial_dvd_factorial_add a (2 * k - 2)
      rw [show a + (2 * k - 2) = a + 2 * k - 2 by omega] at this
      exact Nat.le_of_dvd (Nat.factorial_pos _) this
    calc a.factorial * 2 ^ k * k.factorial = a.factorial * (2 ^ k * k.factorial) := by ring
      _ < a.factorial * (2 * (2 * k - 2).factorial) := Nat.mul_lt_mul_of_pos_left h1 hA
      _ = 2 * (a.factorial * (2 * k - 2).factorial) := by ring
      _ ≤ 2 * (a + 2 * k - 2).factorial := Nat.mul_le_mul_left 2 h2

theorem isSwap_of_nat_card_centralizer (hα : 7 ≤ Fintype.card α) {σ : Perm α} (h2 : σ * σ = 1)
    (h1 : σ ≠ 1)
    (hc : Nat.card (centralizer ({σ} : Set (Perm α))) = 2 * (Fintype.card α - 2).factorial) :
    σ.IsSwap := by
  set k := Multiset.card σ.cycleType with hk
  have hs := card_support_eq_two_mul_card_cycleType h2
  have hle : σ.support.card ≤ Fintype.card α := Finset.card_le_univ _
  have hk0 : k ≠ 0 := by
    intro h0
    apply h1
    rw [← cycleType_eq_zero, cycleType_eq_replicate_two h2, ← hk, h0, Multiset.replicate_zero]
  rcases (by omega : k = 1 ∨ 2 ≤ k) with h | h
  · rw [← card_support_eq_two, hs, ← hk, h]
  · exfalso
    rw [nat_card_centralizer_of_mul_self h2, ← hk] at hc
    have hlt := factorial_mul_two_pow_mul_factorial_lt (Fintype.card α - 2 * k) k h (by omega)
    rw [show Fintype.card α - 2 * k + 2 * k - 2 = Fintype.card α - 2 by omega] at hlt
    omega

end Card

section Normalizes

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [DecidableEq α] [Fintype α] in
theorem apply_apply_of_mul_self {σ : Perm α} (h2 : σ * σ = 1) (x : α) : σ (σ x) = x := by
  have := congrArg (fun f : Perm α => f x) h2
  simpa using this

omit [Fintype α] in
theorem swap_mul_swap_comm_of_ne {a b c d : α} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : swap a b * swap c d = swap c d * swap a b := by
  apply Perm.Disjoint.commute
  intro i
  by_cases hi : i = a ∨ i = b
  · right
    rcases hi with rfl | rfl
    · exact swap_apply_of_ne_of_ne hac had
    · exact swap_apply_of_ne_of_ne hbc hbd
  · push Not at hi
    exact Or.inl (swap_apply_of_ne_of_ne hi.1 hi.2)

omit [Fintype α] in
theorem swap_comm_of_fixed {ρ : Perm α} {a b : α} (ha : ρ a = a) (hb : ρ b = b) :
    swap a b * ρ = ρ * swap a b := by
  rw [mul_swap_eq_swap_mul, ha, hb]

omit [Fintype α] in
theorem swap_mul_swap_comm_of_involution {ρ : Perm α} (hρ : ρ * ρ = 1) {x u : α}
    (hx : ρ x ≠ x) (hu : ρ u ≠ u) (hu1 : u ≠ x) (hu2 : u ≠ ρ x) :
    (swap x u * swap (ρ x) (ρ u)) * ρ = ρ * (swap x u * swap (ρ x) (ρ u)) := by
  have hρρ := apply_apply_of_mul_self hρ
  have hxu' : x ≠ ρ u := fun h => hu2 (by rw [h, hρρ])
  have hρne : ρ x ≠ ρ u := fun h => hu1 (ρ.injective h).symm
  have e1 : ρ * swap (ρ x) (ρ u) = swap x u * ρ := by rw [mul_swap_eq_swap_mul, hρρ, hρρ]
  have e2 : ρ * swap x u = swap (ρ x) (ρ u) * ρ := mul_swap_eq_swap_mul ρ x u
  have hd : swap (ρ x) (ρ u) * swap x u = swap x u * swap (ρ x) (ρ u) :=
    swap_mul_swap_comm_of_ne hx hu2.symm hxu'.symm hu
  calc (swap x u * swap (ρ x) (ρ u)) * ρ = swap x u * (swap (ρ x) (ρ u) * ρ) := by
        rw [mul_assoc]
    _ = swap x u * (ρ * swap x u) := by rw [e2]
    _ = (swap x u * ρ) * swap x u := by rw [mul_assoc]
    _ = (ρ * swap (ρ x) (ρ u)) * swap x u := by rw [e1]
    _ = ρ * (swap (ρ x) (ρ u) * swap x u) := by rw [mul_assoc]
    _ = ρ * (swap x u * swap (ρ x) (ρ u)) := by rw [hd]

variable {σ ρ : Perm α}

omit [Fintype α] in
theorem false_of_fixed_moved (hσρ : σ * ρ = ρ * σ)
    (hN : ∀ c : Perm α, c * ρ = ρ * c → c * σ * c⁻¹ = σ ∨ c * σ * c⁻¹ = σ * ρ)
    {x : α} (hx : ρ x = x) (hσx : σ x ≠ x) {w : α} (hw : ρ w = w) (hw1 : w ≠ x)
    (hw2 : w ≠ σ x) : False := by
  have hρσx : ρ (σ x) = σ x := by
    have := congrArg (fun f : Perm α => f x) hσρ
    simp only [Perm.mul_apply, hx] at this
    exact this.symm
  have hc := swap_comm_of_fixed hρσx hw
  have hcx : swap (σ x) w x = x := swap_apply_of_ne_of_ne (Ne.symm hσx) (Ne.symm hw1)
  have key : (swap (σ x) w * σ * (swap (σ x) w)⁻¹) x = w := by
    rw [swap_inv, Perm.mul_apply, Perm.mul_apply, hcx, swap_apply_left]
  rcases hN _ hc with h | h
  · rw [h] at key
    exact hw2 key.symm
  · rw [h, Perm.mul_apply, hx] at key
    exact hw2 key.symm

omit [Fintype α] in
theorem false_of_moved_off (hρ : ρ * ρ = 1)
    (hN : ∀ c : Perm α, c * ρ = ρ * c → c * σ * c⁻¹ = σ ∨ c * σ * c⁻¹ = σ * ρ)
    {x : α} (hx : ρ x ≠ x) (hσx1 : σ x ≠ x) (hσx2 : σ x ≠ ρ x) {u : α} (hu : ρ u ≠ u)
    (hu1 : u ≠ x) (hu2 : u ≠ ρ x) (hu3 : u ≠ σ x) (hu4 : u ≠ ρ (σ x)) : False := by
  have hρρ := apply_apply_of_mul_self hρ
  have hc := swap_mul_swap_comm_of_involution hρ hx hu hu1 hu2
  have hxu' : x ≠ ρ u := fun h => hu2 (by rw [h, hρρ])
  have h1 : (swap x u * swap (ρ x) (ρ u))⁻¹ u = x := by
    rw [mul_inv_rev, swap_inv, swap_inv, Perm.mul_apply, swap_apply_right,
      swap_apply_of_ne_of_ne (Ne.symm hx) hxu']
  have hy1 : σ x ≠ ρ u := fun h => hu4 (by rw [h, hρρ])
  have h2 : (swap x u * swap (ρ x) (ρ u)) (σ x) = σ x := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hσx2 hy1, swap_apply_of_ne_of_ne hσx1 hu3.symm]
  have key : (swap x u * swap (ρ x) (ρ u) * σ * (swap x u * swap (ρ x) (ρ u))⁻¹) u = σ x := by
    rw [Perm.mul_apply, Perm.mul_apply, h1, h2]
  rcases hN _ hc with h | h
  · rw [h] at key
    exact hu1 (σ.injective key)
  · rw [h, Perm.mul_apply] at key
    exact hu2 (by rw [← σ.injective key, hρρ])

omit [Fintype α] in
theorem false_of_mixed (h2 : σ * σ = 1) (hρ : ρ * ρ = 1) (hσρ : σ * ρ = ρ * σ)
    (hN : ∀ c : Perm α, c * ρ = ρ * c → c * σ * c⁻¹ = σ ∨ c * σ * c⁻¹ = σ * ρ)
    {x u : α} (hx : ρ x ≠ x) (hu : ρ u ≠ u) (hu1 : u ≠ x) (hu2 : u ≠ ρ x) (hσx : σ x = x)
    (hσu : σ u = ρ u) {v : α} (hv : ρ v ≠ v) (hv1 : v ≠ x) (hv2 : v ≠ ρ x) (hv3 : v ≠ u)
    (hv4 : v ≠ ρ u) : False := by
  have hρρ := apply_apply_of_mul_self hρ
  have hσσ := apply_apply_of_mul_self h2
  have hσρx : ∀ y, σ (ρ y) = ρ (σ y) := fun y => by
    have := congrArg (fun f : Perm α => f y) hσρ
    simpa using this
  have hc := swap_mul_swap_comm_of_involution hρ hx hu hu1 hu2
  have hxu' : x ≠ ρ u := fun h => hu2 (by rw [h, hρρ])
  have h1 : (swap x u * swap (ρ x) (ρ u))⁻¹ u = x := by
    rw [mul_inv_rev, swap_inv, swap_inv, Perm.mul_apply, swap_apply_right,
      swap_apply_of_ne_of_ne (Ne.symm hx) hxu']
  have h2' : (swap x u * swap (ρ x) (ρ u)) x = u := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hx) hxu', swap_apply_left]
  have keyu : (swap x u * swap (ρ x) (ρ u) * σ * (swap x u * swap (ρ x) (ρ u))⁻¹) u = u := by
    rw [Perm.mul_apply, Perm.mul_apply, h1, hσx, h2']
  rcases hN _ hc with h | h
  · rw [h, hσu] at keyu
    exact hu keyu
  ·
    have hv5 : (swap x u * swap (ρ x) (ρ u))⁻¹ v = v := by
      rw [mul_inv_rev, swap_inv, swap_inv, Perm.mul_apply, swap_apply_of_ne_of_ne hv1 hv3,
        swap_apply_of_ne_of_ne hv2 hv4]
    have hσv1 : σ v ≠ x := fun h' => hv1 (by rw [← hσσ v, h', hσx])
    have hσv2 : σ v ≠ ρ x := fun h' => hv2 (by rw [← hσσ v, h', hσρx, hσx])
    have hσv3 : σ v ≠ u := fun h' => hv4 (by rw [← hσσ v, h', hσu])
    have hσv4 : σ v ≠ ρ u := fun h' => hv3 (by rw [← hσσ v, h', hσρx, hσu, hρρ])
    have hv6 : (swap x u * swap (ρ x) (ρ u)) (σ v) = σ v := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hσv2 hσv4, swap_apply_of_ne_of_ne hσv1 hσv3]
    have keyv : (swap x u * swap (ρ x) (ρ u) * σ * (swap x u * swap (ρ x) (ρ u))⁻¹) v = σ v := by
      rw [Perm.mul_apply, Perm.mul_apply, hv5, hv6]
    rw [h, Perm.mul_apply] at keyv
    exact hv (σ.injective keyv)

theorem card_support_le_four_of_normalizes' (hα : 7 ≤ Fintype.card α) (h2 : σ * σ = 1)
    (hρ : ρ * ρ = 1) (hσρ : σ * ρ = ρ * σ) (h1 : σ ≠ 1) (h1' : σ * ρ ≠ 1)
    (hN : ∀ c : Perm α, c * ρ = ρ * c → c * σ * c⁻¹ = σ ∨ c * σ * c⁻¹ = σ * ρ) :
    σ.support.card ≤ 4 ∨ (σ * ρ).support.card ≤ 4 := by
  classical
  have hρρ := apply_apply_of_mul_self hρ
  have hσσ := apply_apply_of_mul_self h2
  have hσρx : ∀ y, σ (ρ y) = ρ (σ y) := fun y => by
    have := congrArg (fun f : Perm α => f y) hσρ
    simpa using this
  have hsmall : ρ.support.card ≤ 4 → σ.support ⊆ ρ.support := by
    intro hP x hx
    rw [mem_support] at hx ⊢
    intro hρx
    have hρσx : ρ (σ x) = σ x := by rw [← hσρx, hρx]
    have hcard : 3 ≤ (Finset.univ \ ρ.support).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
      omega
    obtain ⟨w, hw, hw'⟩ : ∃ w ∈ Finset.univ \ ρ.support, w ≠ x ∧ w ≠ σ x := by
      by_contra hcon
      push Not at hcon
      have : Finset.univ \ ρ.support ⊆ {x, σ x} := fun w hw => by
        rcases eq_or_ne w x with h | h
        · simp [h]
        · simp [hcon w hw h]
      have := Finset.card_le_card this
      have := Finset.card_insert_le x ({σ x} : Finset α)
      simp at *
      omega
    have hw2 : ρ w = w := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_support, not_not] at hw
      exact hw
    exact false_of_fixed_moved hσρ hN hρx hx hw2 hw'.1 hw'.2
  by_cases hP : ρ.support.card ≤ 4
  · left
    exact (Finset.card_le_card (hsmall hP)).trans hP
  push Not at hP
  have hc1 : ∀ x, ρ x ≠ x → σ x = x ∨ σ x = ρ x := by
    intro x hx
    by_contra hcon
    push Not at hcon
    have : ρ.support ⊆ {x, ρ x, σ x, ρ (σ x)} := by
      intro u hu
      rw [mem_support] at hu
      by_contra hu'
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu'
      exact false_of_moved_off hρ hN hx hcon.1 hcon.2 hu hu'.1 hu'.2.1 hu'.2.2.1 hu'.2.2.2
    have h4 := Finset.card_le_card this
    have h5 : ({x, ρ x, σ x, ρ (σ x)} : Finset α).card ≤ 4 := Finset.card_le_four
    omega
  have hc2 : (∀ x, ρ x ≠ x → σ x = x) ∨ (∀ x, ρ x ≠ x → σ x = ρ x) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨x, hx, hσx⟩, ⟨u, hu, hσu⟩⟩ := hcon
    have hσx' : σ x = ρ x := (hc1 x hx).resolve_left hσx
    have hσu' : σ u = u := (hc1 u hu).resolve_right hσu
    have hxu1 : x ≠ u := fun h => hσx (h ▸ hσu')
    have hxu2 : x ≠ ρ u := fun h => hσx (by rw [h, hσρx, hσu'])
    have : ρ.support ⊆ {u, ρ u, x, ρ x} := by
      intro v hv
      rw [mem_support] at hv
      by_contra hv'
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv'
      exact false_of_mixed h2 hρ hσρ hN hu hx hxu1 hxu2 hσu' hσx' hv hv'.1 hv'.2.1 hv'.2.2.1
        hv'.2.2.2
    have h4 := Finset.card_le_card this
    have h5 : ({u, ρ u, x, ρ x} : Finset α).card ≤ 4 := Finset.card_le_four
    omega
  by_cases hF : ∀ w, ρ w = w → σ w = w
  · exfalso
    rcases hc2 with h | h
    · apply h1
      ext y
      by_cases hy : ρ y = y
      · simp [hF y hy]
      · simp [h y hy]
    · apply h1'
      ext y
      simp only [Perm.mul_apply, Perm.one_apply]
      by_cases hy : ρ y = y
      · rw [hy, hF y hy]
      · have hρy : ρ (ρ y) ≠ ρ y := fun h' => hy (by rw [← h', hρρ])
        rw [h (ρ y) hρy, hρρ]
  · push Not at hF
    obtain ⟨w₀, hw₀, hσw₀⟩ := hF
    have hF' : ∀ w, ρ w = w → w = w₀ ∨ w = σ w₀ := by
      intro w hw
      by_contra hcon
      push Not at hcon
      exact false_of_fixed_moved hσρ hN hw₀ hσw₀ hw hcon.1 hcon.2
    rcases hc2 with h | h
    · left
      have : σ.support ⊆ {w₀, σ w₀} := by
        intro y hy
        rw [mem_support] at hy
        by_cases hρy : ρ y = y
        · rcases hF' y hρy with rfl | rfl <;> simp
        · exact absurd (h y hρy) hy
      exact (Finset.card_le_card this).trans (Finset.card_le_two.trans (by norm_num))
    · right
      have : (σ * ρ).support ⊆ {w₀, σ w₀} := by
        intro y hy
        rw [mem_support, Perm.mul_apply] at hy
        by_cases hρy : ρ y = y
        · rcases hF' y hρy with rfl | rfl <;> simp
        · have hρy' : ρ (ρ y) ≠ ρ y := fun h' => hρy (by rw [← h', hρρ])
          exact absurd (by rw [h (ρ y) hρy', hρρ]) hy
      exact (Finset.card_le_card this).trans (Finset.card_le_two.trans (by norm_num))

theorem card_support_le_four_of_normalizes (hα : 7 ≤ Fintype.card α) {σ σ' : Perm α}
    (h2 : σ * σ = 1) (h2' : σ' * σ' = 1) (hc : σ * σ' = σ' * σ) (h1 : σ ≠ 1) (h1' : σ' ≠ 1)
    (hN : ∀ c : Perm α, c * (σ * σ') = (σ * σ') * c → c * σ * c⁻¹ = σ ∨ c * σ * c⁻¹ = σ') :
    σ.support.card ≤ 4 ∨ σ'.support.card ≤ 4 := by
  have hρ : (σ * σ') * (σ * σ') = 1 := by
    calc σ * σ' * (σ * σ') = σ * (σ' * σ) * σ' := by group
      _ = σ * (σ * σ') * σ' := by rw [hc]
      _ = (σ * σ) * (σ' * σ') := by group
      _ = 1 := by rw [h2, h2', one_mul]
  have hσ' : σ * (σ * σ') = σ' := by rw [← mul_assoc, h2, one_mul]
  have hσρ : σ * (σ * σ') = (σ * σ') * σ := by
    rw [hσ']
    calc σ' = σ' * (σ * σ) := by rw [h2, mul_one]
      _ = σ * σ' * σ := by rw [← mul_assoc, ← hc]
  have h := card_support_le_four_of_normalizes' hα h2 hρ hσρ h1 (by rw [hσ']; exact h1')
    (fun c hcρ => by rw [hσ']; exact hN c hcρ)
  rwa [hσ'] at h

end Normalizes

end CFSG.OddStandard.AltStdSec
