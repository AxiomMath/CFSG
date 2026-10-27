module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.GH74.GLS.Stage1.Thm4.L96

open Equiv Equiv.Perm

theorem cycleType_eq_two_p_of_lcm {c : Multiset ℕ} {p : ℕ} (hp : 2 < p) (hsum : c.sum < p + 4)
    (h2 : ∀ x ∈ c, 2 ≤ x) (hmem : ∀ x ∈ c, x = 2 ∨ x = p) (hlcm : c.lcm = 2 * p) :
    c = {2, p} := by
  have hp2 : 2 ∈ c := by
    by_contra h
    have hd : c.lcm ∣ p := Multiset.lcm_dvd.mpr fun x hx => by
      rcases hmem x hx with rfl | rfl
      · exact absurd hx h
      · exact dvd_rfl
    rw [hlcm] at hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hpp : p ∈ c := by
    by_contra h
    have hd : c.lcm ∣ 2 := Multiset.lcm_dvd.mpr fun x hx => by
      rcases hmem x hx with rfl | rfl
      · exact dvd_rfl
      · exact absurd hx h
    rw [hlcm] at hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  obtain ⟨c1, rfl⟩ := Multiset.exists_cons_of_mem hp2
  have hp1 : p ∈ c1 := by
    rcases Multiset.mem_cons.mp hpp with h | h
    · omega
    · exact h
  obtain ⟨c2, rfl⟩ := Multiset.exists_cons_of_mem hp1
  have hc2 : c2 = 0 := by
    by_contra h
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero h
    have hx2 := h2 x (by simp [hx])
    have hxs : x ≤ c2.sum := Multiset.le_sum_of_mem hx
    simp only [Multiset.sum_cons] at hsum
    omega
  subst hc2
  rfl

theorem no_order_ten_alt8 (σ : Perm (Fin 8)) (hs : Perm.sign σ = 1) : orderOf σ ≠ 10 := by
  intro h10
  have hsum : σ.cycleType.sum ≤ 8 := by simpa using Perm.sum_cycleType_le σ
  have harith : ∀ x : ℕ, x ≤ 8 → 2 ≤ x → x ∣ 10 → x = 2 ∨ x = 5 := by decide
  have hc : σ.cycleType = {2, 5} :=
    cycleType_eq_two_p_of_lcm (by omega) (by omega)
      (fun x hx => Perm.two_le_of_mem_cycleType hx)
      (fun x hx => harith x ((Multiset.le_sum_of_mem hx).trans hsum)
        (Perm.two_le_of_mem_cycleType hx) (h10 ▸ Perm.dvd_of_mem_cycleType hx))
      (by rw [Perm.lcm_cycleType, h10])
  rw [Perm.sign_of_cycleType, hc] at hs
  revert hs
  decide

theorem no_order_fourteen_alt9 (σ : Perm (Fin 9)) (hs : Perm.sign σ = 1) : orderOf σ ≠ 14 := by
  intro h14
  have hsum : σ.cycleType.sum ≤ 9 := by simpa using Perm.sum_cycleType_le σ
  have harith : ∀ x : ℕ, x ≤ 9 → 2 ≤ x → x ∣ 14 → x = 2 ∨ x = 7 := by decide
  have hc : σ.cycleType = {2, 7} :=
    cycleType_eq_two_p_of_lcm (by omega) (by omega)
      (fun x hx => Perm.two_le_of_mem_cycleType hx)
      (fun x hx => harith x ((Multiset.le_sum_of_mem hx).trans hsum)
        (Perm.two_le_of_mem_cycleType hx) (h14 ▸ Perm.dvd_of_mem_cycleType hx))
      (by rw [Perm.lcm_cycleType, h14])
  rw [Perm.sign_of_cycleType, hc] at hs
  revert hs
  decide

theorem exists_perm_apply_eq_of_ne {α : Type*} [DecidableEq α] {a b i j : α} (hab : a ≠ b)
    (hij : i ≠ j) : ∃ τ : Perm α, τ a = i ∧ τ b = j := by
  have hb : swap a i b ≠ i := fun h =>
    hab ((swap a i).injective (h.trans (swap_apply_left a i).symm)).symm
  refine ⟨swap (swap a i b) j * swap a i, ?_, ?_⟩
  · rw [Perm.mul_apply, swap_apply_left]
    exact swap_apply_of_ne_of_ne hb.symm hij
  · rw [Perm.mul_apply]
    exact swap_apply_left _ _

theorem exists_conj_pair_fixing {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b)
    (g₁ g₂ : Perm α) (h₁a : g₁ a = a) (h₁b : g₁ b = b) (h₂a : g₂ a = a) (h₂b : g₂ b = b)
    {i j : α} (hij : i ≠ j) :
    ∃ γ₁ γ₂ : Perm α, orderOf γ₁ = orderOf g₁ ∧ orderOf γ₂ = orderOf g₂ ∧ γ₁ i = i ∧
      γ₁ j = j ∧ γ₂ i = i ∧ γ₂ j = j ∧ orderOf (γ₁ * γ₂) = orderOf (g₁ * g₂) := by
  obtain ⟨τ, hτa, hτb⟩ := exists_perm_apply_eq_of_ne hab hij
  have hia : τ⁻¹ i = a := by rw [Perm.inv_eq_iff_eq, hτa]
  have hjb : τ⁻¹ j = b := by rw [Perm.inv_eq_iff_eq, hτb]
  refine ⟨τ * g₁ * τ⁻¹, τ * g₂ * τ⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (MulAut.conj τ).orderOf_eq g₁
  · exact (MulAut.conj τ).orderOf_eq g₂
  · simp [Perm.mul_apply, hia, h₁a, hτa]
  · simp [Perm.mul_apply, hjb, h₁b, hτb]
  · simp [Perm.mul_apply, hia, h₂a, hτa]
  · simp [Perm.mul_apply, hjb, h₂b, hτb]
  · rw [show τ * g₁ * τ⁻¹ * (τ * g₂ * τ⁻¹) = MulAut.conj τ (g₁ * g₂) by
      simp [MulAut.conj_apply, mul_assoc]]
    exact (MulAut.conj τ).orderOf_eq _

theorem exists_two_threeCycles {n : ℕ} (hn : 6 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    ∃ γ₁ γ₂ : Perm (Fin n), orderOf γ₁ = 3 ∧ orderOf γ₂ = 3 ∧ γ₁ i = i ∧ γ₁ j = j ∧
      γ₂ i = i ∧ γ₂ j = j ∧ (γ₁ * γ₂).cycleType = {2, 2} := by
  have hinj : Function.Injective (Fin.castLE hn) := Fin.castLE_injective hn
  obtain ⟨τ, hτ0, hτ1⟩ := exists_perm_apply_eq_of_ne (a := Fin.castLE hn 0) (b := Fin.castLE hn 1)
    (hinj.ne (by decide)) hij
  have hpinj : Function.Injective fun k : Fin 6 => τ (Fin.castLE hn k) :=
    τ.injective.comp hinj
  generalize hp : (fun k : Fin 6 => τ (Fin.castLE hn k)) = p at hpinj
  have hi : p 0 = i := by rw [← hp]; exact hτ0
  have hj : p 1 = j := by rw [← hp]; exact hτ1
  have hne : ∀ k l : Fin 6, k ≠ l → p k ≠ p l := fun k l h => hpinj.ne h
  have hfix : ∀ a b c d x : Fin n, x ≠ a → x ≠ b → x ≠ c → x ≠ d →
      (swap a b * swap c d) x = x := fun a b c d x ha hb hc hd => by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hc hd, swap_apply_of_ne_of_ne ha hb]
  have h3 : ∀ k l m : Fin 6, k ≠ l → k ≠ m → l ≠ m →
      orderOf (swap (p k) (p l) * swap (p k) (p m)) = 3 := fun k l m hkl hkm hlm =>
    (isThreeCycle_swap_mul_swap_same (hne k l hkl) (hne k m hkm) (hne l m hlm)).orderOf
  refine ⟨swap (p 2) (p 3) * swap (p 2) (p 4), swap (p 2) (p 3) * swap (p 2) (p 5),
    h3 2 3 4 (by decide) (by decide) (by decide), h3 2 3 5 (by decide) (by decide) (by decide),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hi]
    exact hfix _ _ _ _ _ (hne 0 2 (by decide)) (hne 0 3 (by decide)) (hne 0 2 (by decide))
      (hne 0 4 (by decide))
  · rw [← hj]
    exact hfix _ _ _ _ _ (hne 1 2 (by decide)) (hne 1 3 (by decide)) (hne 1 2 (by decide))
      (hne 1 4 (by decide))
  · rw [← hi]
    exact hfix _ _ _ _ _ (hne 0 2 (by decide)) (hne 0 3 (by decide)) (hne 0 2 (by decide))
      (hne 0 5 (by decide))
  · rw [← hj]
    exact hfix _ _ _ _ _ (hne 1 2 (by decide)) (hne 1 3 (by decide)) (hne 1 2 (by decide))
      (hne 1 5 (by decide))
  · have h1 : swap (p 2) (p 3) * swap (p 2) (p 4) = swap (p 3) (p 4) * swap (p 2) (p 3) := by
      rw [mul_swap_eq_swap_mul, swap_apply_left,
        swap_apply_of_ne_of_ne (hne 4 2 (by decide)) (hne 4 3 (by decide))]
    rw [h1, mul_assoc, ← mul_assoc (swap (p 2) (p 3)), swap_mul_self, one_mul]
    exact cycleType_swap_mul_swap_of_nodup
      (by
        simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
          List.nodup_nil, and_true]
        exact ⟨⟨hne 3 4 (by decide), hne 3 2 (by decide), hne 3 5 (by decide)⟩,
          ⟨hne 4 2 (by decide), hne 4 5 (by decide)⟩, hne 2 5 (by decide)⟩)

theorem exists_two_pElements {n p : ℕ} (hnp : (n = 8 ∧ p = 5) ∨ (n = 9 ∧ p = 7)) (i j : Fin n)
    (hij : i ≠ j) :
    ∃ γ₁ γ₂ : Perm (Fin n), orderOf γ₁ = p ∧ orderOf γ₂ = p ∧ γ₁ i = i ∧ γ₁ j = j ∧
      γ₂ i = i ∧ γ₂ j = j ∧ Even (orderOf (γ₁ * γ₂)) := by
  rcases hnp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hz : orderOf (swap (2 : Fin 8) 4 * swap 3 5) = 2 :=
      orderOf_eq_prime (p := 2) (by decide) (by decide)
    have hg₁ : orderOf (List.formPerm [(2 : Fin 8), 3, 4, 5, 6]) = 5 :=
      orderOf_eq_prime (p := 5) (List.formPerm_pow_length_eq_one_of_nodup _ (by decide))
        (by decide)
    have hg₂ : orderOf (List.formPerm [(2 : Fin 8), 3, 4, 6, 5]) = 5 :=
      orderOf_eq_prime (p := 5) (List.formPerm_pow_length_eq_one_of_nodup _ (by decide))
        (by decide)
    have hg : List.formPerm [(2 : Fin 8), 3, 4, 5, 6] * List.formPerm [(2 : Fin 8), 3, 4, 6, 5] =
        swap 2 4 * swap 3 5 := by decide
    obtain ⟨γ₁, γ₂, h1, h2, h3, h4, h5, h6, h7⟩ := exists_conj_pair_fixing (a := (0 : Fin 8))
      (b := 1) (by decide) (List.formPerm [(2 : Fin 8), 3, 4, 5, 6])
      (List.formPerm [(2 : Fin 8), 3, 4, 6, 5]) (by decide) (by decide) (by decide) (by decide) hij
    exact ⟨γ₁, γ₂, h1.trans hg₁, h2.trans hg₂, h3, h4, h5, h6,
      by rw [h7, hg, hz]; exact even_two⟩
  · have : Fact (Nat.Prime 7) := ⟨by decide⟩
    have hz : orderOf (swap (2 : Fin 9) 4 * swap 3 5) = 2 :=
      orderOf_eq_prime (p := 2) (by decide) (by decide)
    have hg₁ : orderOf (List.formPerm [(2 : Fin 9), 3, 4, 5, 6, 7, 8]) = 7 :=
      orderOf_eq_prime (p := 7) (List.formPerm_pow_length_eq_one_of_nodup _ (by decide))
        (by decide)
    have hg₂ : orderOf (List.formPerm [(2 : Fin 9), 3, 4, 8, 7, 6, 5]) = 7 :=
      orderOf_eq_prime (p := 7) (List.formPerm_pow_length_eq_one_of_nodup _ (by decide))
        (by decide)
    have hg : List.formPerm [(2 : Fin 9), 3, 4, 5, 6, 7, 8] *
        List.formPerm [(2 : Fin 9), 3, 4, 8, 7, 6, 5] = swap 2 4 * swap 3 5 := by decide
    obtain ⟨γ₁, γ₂, h1, h2, h3, h4, h5, h6, h7⟩ := exists_conj_pair_fixing (a := (0 : Fin 9))
      (b := 1) (by decide) (List.formPerm [(2 : Fin 9), 3, 4, 5, 6, 7, 8])
      (List.formPerm [(2 : Fin 9), 3, 4, 8, 7, 6, 5]) (by decide) (by decide) (by decide)
      (by decide) hij
    exact ⟨γ₁, γ₂, h1.trans hg₁, h2.trans hg₂, h3, h4, h5, h6,
      by rw [h7, hg, hz]; exact even_two⟩

theorem oddInvolution_cycleType {n : ℕ} (hn : n ≤ 9) (σ : Perm (Fin n)) (h2 : σ ^ 2 = 1)
    (hs : Perm.sign σ = -1) : σ.cycleType = {2} ∨ σ.cycleType = {2, 2, 2} := by
  have hk : σ.cycleType = Multiset.replicate σ.cycleType.card 2 :=
    Perm.cycleType_of_pow_prime_eq_one h2
  have hsum := Perm.sum_cycleType_le σ
  rw [hk, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  rw [Perm.sign_of_cycleType, hk, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul] at hs
  generalize σ.cycleType.card = k at hk hsum hs
  rw [hk]
  obtain rfl | rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  · exact absurd hs (by decide)
  · left; rfl
  · exact absurd hs (by decide)
  · right; rfl
  · exact absurd hs (by decide)

theorem exists_swap_of_cycleType_two {n : ℕ} {σ : Perm (Fin n)} (h : σ.cycleType = {2}) :
    ∃ i j : Fin n, i ≠ j ∧ σ = swap i j :=
  Perm.isSwap_iff_cycleType.mpr h

end CFSG.GH74.GLS.Stage1.Thm4.L96
