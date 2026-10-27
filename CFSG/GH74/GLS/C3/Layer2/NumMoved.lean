module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GH74.GLS.C3.Layer2

open Equiv Perm

@[expose] def numMoved {α : Type*} [Fintype α] [DecidableEq α] (g : Perm α) : ℕ :=
  (Finset.univ.filter fun a => g a ≠ a).card

theorem numMoved_eq_card_support {α : Type*} [Fintype α] [DecidableEq α] (g : Perm α) :
    numMoved g = g.support.card :=
  rfl

theorem numMoved_conj {α : Type*} [Fintype α] [DecidableEq α] (g h : Perm α) :
    numMoved (h * g * h⁻¹) = numMoved g := by
  simp only [numMoved_eq_card_support]
  exact Equiv.Perm.card_support_conj

private theorem exists_cycleType_eq_replicate_two {α : Type*} [Fintype α] [DecidableEq α]
    {g : Perm α} (hg : orderOf g = 2) :
    ∃ n : ℕ, g.cycleType = Multiset.replicate (n + 1) 2 := by
  have hp : (orderOf g).Prime := by rw [hg]; exact Nat.prime_two
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order hp
  exact ⟨n, by rw [hn, hg]⟩

private theorem numMoved_eq_of_cycleType_eq_replicate_two {α : Type*} [Fintype α] [DecidableEq α]
    {g : Perm α} {n : ℕ} (hn : g.cycleType = Multiset.replicate (n + 1) 2) :
    numMoved g = 2 * (n + 1) := by
  rw [numMoved_eq_card_support, ← Equiv.Perm.sum_cycleType, hn, Multiset.sum_replicate]
  simp [mul_comm]

private theorem even_of_sign_eq_one_of_cycleType_eq_replicate_two {α : Type*} [Fintype α]
    [DecidableEq α] {g : Perm α} {n : ℕ} (hn : g.cycleType = Multiset.replicate (n + 1) 2)
    (hs : sign g = 1) : Even (n + 1) := by
  rw [Equiv.Perm.sign_of_cycleType, hn, Multiset.sum_replicate, Multiset.card_replicate] at hs
  have h3 : Even ((n + 1) • 2 + (n + 1)) := by
    rwa [neg_one_pow_eq_one_iff_even (by decide)] at hs
  simp only [smul_eq_mul] at h3
  obtain ⟨k, hk⟩ := h3
  exact ⟨k - (n + 1), by omega⟩

private theorem swap_mul_mul_swap_inv_eq_of_sq_eq_one {α : Type*} [DecidableEq α] {g : Perm α}
    (a : α) (hga : g (g a) = a) : swap a (g a) * g * (swap a (g a))⁻¹ = g := by
  have h3 := Equiv.swap_apply_apply g a (g a)
  rw [hga, Equiv.swap_comm (g a) a] at h3
  rw [mul_inv_eq_iff_eq_mul]
  calc swap a (g a) * g = (g * swap a (g a) * g⁻¹) * g := by rw [← h3]
    _ = g * swap a (g a) := by group

theorem numMoved_eq_of_involution_alternating (m : ℕ) (hm : m ≤ 11)
    (g : alternatingGroup (Fin m)) (hg : orderOf g = 2) :
    numMoved (g : Perm (Fin m)) = 4 ∨ numMoved (g : Perm (Fin m)) = 8 := by
  have hg' : orderOf (g : Perm (Fin m)) = 2 := by rw [Subgroup.orderOf_coe]; exact hg
  obtain ⟨n, hn⟩ := exists_cycleType_eq_replicate_two hg'
  have hsign : sign (g : Perm (Fin m)) = 1 := mem_alternatingGroup.1 g.2
  have hcard := numMoved_eq_of_cycleType_eq_replicate_two hn
  have hle : numMoved (g : Perm (Fin m)) ≤ m := by
    calc numMoved (g : Perm (Fin m)) = (support (g : Perm (Fin m))).card := rfl
      _ ≤ Fintype.card (Fin m) := Finset.card_le_univ _
      _ = m := Fintype.card_fin m
  obtain ⟨k, hk⟩ := even_of_sign_eq_one_of_cycleType_eq_replicate_two hn hsign
  omega

theorem isConj_alternating_of_numMoved_eq (m : ℕ) (g h : alternatingGroup (Fin m))
    (hg : orderOf g = 2) (hh : orderOf h = 2)
    (hn : numMoved (g : Perm (Fin m)) = numMoved (h : Perm (Fin m))) : IsConj g h := by
  have hg' : orderOf (g : Perm (Fin m)) = 2 := by rw [Subgroup.orderOf_coe]; exact hg
  have hh' : orderOf (h : Perm (Fin m)) = 2 := by rw [Subgroup.orderOf_coe]; exact hh
  obtain ⟨n, hgn⟩ := exists_cycleType_eq_replicate_two hg'
  obtain ⟨n', hhn⟩ := exists_cycleType_eq_replicate_two hh'
  have h1 := numMoved_eq_of_cycleType_eq_replicate_two hgn
  have h2 := numMoved_eq_of_cycleType_eq_replicate_two hhn
  have hnn : n = n' := by omega
  have hct : (g : Perm (Fin m)).cycleType = (h : Perm (Fin m)).cycleType := by
    rw [hgn, hhn, hnn]
  obtain ⟨σ, hσ⟩ := isConj_iff.1 (Equiv.Perm.isConj_iff_cycleType_eq.2 hct)
  have hne : (g : Perm (Fin m)) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hg'
    omega
  obtain ⟨a, ha⟩ : ∃ a, (g : Perm (Fin m)) a ≠ a := by
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 hne
    exact ⟨a, ha⟩
  have hsq : (g : Perm (Fin m)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (g : Perm (Fin m))
    rwa [hg'] at this
  have hga : (g : Perm (Fin m)) ((g : Perm (Fin m)) a) = a := by
    have := congrArg (fun f : Perm (Fin m) => f a) hsq
    simpa [sq, Perm.mul_apply] using this
  have hcomm := swap_mul_mul_swap_inv_eq_of_sq_eq_one a hga
  obtain ⟨τ, hτ1, hτ2⟩ : ∃ τ : Perm (Fin m), sign τ = 1 ∧ τ * (g : Perm (Fin m)) * τ⁻¹ = h := by
    rcases Int.units_eq_one_or (sign σ) with hs | hs
    · exact ⟨σ, hs, hσ⟩
    · refine ⟨σ * swap a ((g : Perm (Fin m)) a), ?_, ?_⟩
      · rw [map_mul, hs, sign_swap (Ne.symm ha)]
        decide
      · calc σ * swap a ((g : Perm (Fin m)) a) * (g : Perm (Fin m)) *
              (σ * swap a ((g : Perm (Fin m)) a))⁻¹
            = σ * (swap a ((g : Perm (Fin m)) a) * (g : Perm (Fin m)) *
              (swap a ((g : Perm (Fin m)) a))⁻¹) * σ⁻¹ := by group
          _ = σ * (g : Perm (Fin m)) * σ⁻¹ := by rw [hcomm]
          _ = h := hσ
  exact isConj_iff.2 ⟨⟨τ, mem_alternatingGroup.2 hτ1⟩, Subtype.ext hτ2⟩

theorem numMoved_eq_of_isConj_alternating (m : ℕ) {g h : alternatingGroup (Fin m)}
    (hc : IsConj g h) :
    numMoved (g : Perm (Fin m)) = numMoved (h : Perm (Fin m)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hc
  have : ((c * g * c⁻¹ : alternatingGroup (Fin m)) : Perm (Fin m)) = (h : Perm (Fin m)) := by
    rw [hc]
  rw [← this]
  exact (numMoved_conj _ _).symm

end CFSG.GH74.GLS.C3.Layer2
