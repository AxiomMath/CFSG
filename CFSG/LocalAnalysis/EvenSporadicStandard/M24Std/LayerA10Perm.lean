module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import CFSG.Milestones.AT_alternating_automorphism_permutation
import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup Equiv Equiv.Perm Nat

section Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem exists_cycleType_eq_replicate_two {σ : Perm α} (hσ : σ ^ 2 = 1) :
    ∃ k : ℕ, σ.cycleType = Multiset.replicate k 2 ∧ 2 * k ≤ Fintype.card α ∧
      Nat.card (centralizer {σ}) = (Fintype.card α - 2 * k)! * 2 ^ k * k ! ∧
      sign σ = (-1) ^ k := by
  have h : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 := by
    rw [Multiset.eq_replicate_card]
    intro m hm
    have h1 := dvd_of_mem_cycleType hm
    have h2 := two_le_of_mem_cycleType hm
    have h3 := Nat.le_of_dvd two_pos (h1.trans (orderOf_dvd_of_pow_eq_one hσ))
    omega
  set k := Multiset.card σ.cycleType with hk
  have hsum : σ.cycleType.sum = 2 * k := by
    rw [h, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  refine ⟨k, h, ?_, ?_, ?_⟩
  · rw [← hsum, sum_cycleType]
    exact Finset.card_le_univ _
  · rw [nat_card_centralizer, hsum, h, Multiset.prod_replicate, Multiset.toFinset_replicate]
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · simp [h0]
    · simp [h0.ne', Multiset.count_replicate_self]
  · rw [sign_of_cycleType, hsum, ← hk, pow_add, pow_mul, Int.units_sq, one_pow, one_mul]

theorem card_alternatingGroup_inf_centralizer_mul_two {σ : Perm α} (hσ : σ ^ 2 = 1)
    (hα : 2 ≤ Fintype.card α) :
    Nat.card (alternatingGroup α ⊓ centralizer {σ} : Subgroup (Perm α)) * 2 =
      Nat.card (centralizer {σ}) := by
  obtain ⟨k, hk, -⟩ := exists_cycleType_eq_replicate_two hσ
  have hnle : ¬ centralizer {σ} ≤ alternatingGroup α := by
    intro hle
    have hodd := OnCycleFactors.odd_of_centralizer_le_alternatingGroup hle
    have hcard := card_le_of_centralizer_le_alternating hle
    rw [hk] at hodd hcard
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, Multiset.replicate_zero, Multiset.sum_zero] at hcard
      omega
    · have := hodd 2 (Multiset.mem_replicate.2 ⟨h0.ne', rfl⟩)
      exact (Nat.not_odd_iff_even.2 even_two) this
  have hdvd : (alternatingGroup α).relIndex (centralizer {σ}) ∣ 2 := by
    have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
    rw [← alternatingGroup.index_eq_two (α := α)]
    exact relIndex_dvd_index_of_normal _ _
  have h2 : (alternatingGroup α).relIndex (centralizer {σ}) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
    · exact absurd (relIndex_eq_one.1 h1) hnle
    · exact h1
  rw [← relIndex_mul_card (alternatingGroup α) (centralizer {σ}), h2, mul_comm]

end Perm

section Aut

variable {n : ℕ}

theorem exists_perm_sq_eq_one_of_mulAut_alternatingGroup (hn : n = 5 ∨ 7 ≤ n)
    (f : MulAut (alternatingGroup (Fin n))) (hf : f * f = 1) :
    ∃ σ : Perm (Fin n), σ ^ 2 = 1 ∧
      ∀ g : alternatingGroup (Fin n), (f g : Perm (Fin n)) = σ * g * σ⁻¹ := by
  obtain ⟨σ, hσ⟩ := CFSG.Milestones.alternating_automorphism_permutation hn f
  refine ⟨σ, ?_, hσ⟩
  have hc : σ * σ ∈ centralizer (alternatingGroup (Fin n) : Set (Perm (Fin n))) := by
    rw [mem_centralizer_iff]
    intro g hg
    have h1 : ((f * f) ⟨g, hg⟩ : Perm (Fin n)) = σ * (σ * g * σ⁻¹) * σ⁻¹ := by
      rw [MulAut.mul_apply, hσ, hσ]
    rw [hf, MulAut.one_apply] at h1
    calc g * (σ * σ) = σ * (σ * g * σ⁻¹) * σ⁻¹ * (σ * σ) := by rw [← h1]
      _ = σ * σ * g := by group
  rw [CFSG.ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot
    (by rcases hn with h | h <;> simp <;> omega), mem_bot] at hc
  rw [sq, hc]

theorem card_fixed_mulAut_alternatingGroup {f : MulAut (alternatingGroup (Fin n))}
    {σ : Perm (Fin n)} (hσ : ∀ g : alternatingGroup (Fin n), (f g : Perm (Fin n)) = σ * g * σ⁻¹) :
    Nat.card {g : alternatingGroup (Fin n) // f g = g} =
      Nat.card (alternatingGroup (Fin n) ⊓ centralizer {σ} : Subgroup (Perm (Fin n))) := by
  have hiff : ∀ g : alternatingGroup (Fin n), f g = g ↔ (g : Perm (Fin n)) * σ = σ * g := by
    intro g
    rw [← Subtype.coe_inj, hσ, mul_inv_eq_iff_eq_mul, eq_comm]
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1.1, mem_inf.2 ⟨x.1.2, mem_centralizer_singleton_iff.2 ((hiff _).1 x.2)⟩⟩
      invFun := fun y => ⟨⟨y.1, (mem_inf.1 y.2).1⟩,
        (hiff _).2 (mem_centralizer_singleton_iff.1 (mem_inf.1 y.2).2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem eq_of_mulAut_alternatingGroup_eq_conj (hn : 4 ≤ n) {f : MulAut (alternatingGroup (Fin n))}
    {σ : Perm (Fin n)} (hσ : ∀ g : alternatingGroup (Fin n), (f g : Perm (Fin n)) = σ * g * σ⁻¹)
    {s : alternatingGroup (Fin n)} (hs : f = MulAut.conj s) : σ = s := by
  have hc : σ⁻¹ * s ∈ centralizer (alternatingGroup (Fin n) : Set (Perm (Fin n))) := by
    rw [mem_centralizer_iff]
    intro g hg
    have h1 := hσ ⟨g, hg⟩
    rw [hs, MulAut.conj_apply] at h1
    have h2 : (s : Perm (Fin n)) * g * (s : Perm (Fin n))⁻¹ = σ * g * σ⁻¹ := h1
    calc g * (σ⁻¹ * s) = σ⁻¹ * (σ * g * σ⁻¹) * s := by group
      _ = σ⁻¹ * ((s : Perm (Fin n)) * g * (s : Perm (Fin n))⁻¹) * s := by rw [h2]
      _ = σ⁻¹ * s * g := by group
  rw [CFSG.ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot
    (by simp; omega), mem_bot] at hc
  exact (inv_mul_eq_one.1 hc)

end Aut

theorem card_alternatingGroup_inf_centralizer_ten {σ : Perm (Fin 10)} (hσ : σ ^ 2 = 1) :
    Nat.card (alternatingGroup (Fin 10) ⊓ centralizer {σ} : Subgroup (Perm (Fin 10))) ∈
        ({1814400, 40320, 2880, 576, 384, 1920} : Finset ℕ) ∧
      (Nat.card (alternatingGroup (Fin 10) ⊓ centralizer {σ} : Subgroup (Perm (Fin 10))) =
        40320 → sign σ = -1) := by
  obtain ⟨k, -, hk, hc, hs⟩ := exists_cycleType_eq_replicate_two hσ
  have h2 := card_alternatingGroup_inf_centralizer_mul_two hσ (by simp)
  rw [hc, Fintype.card_fin] at h2
  rw [Fintype.card_fin] at hk
  set c := Nat.card (alternatingGroup (Fin 10) ⊓ centralizer {σ} : Subgroup (Perm (Fin 10)))
  have key : c ∈ ({1814400, 40320, 2880, 576, 384, 1920} : Finset ℕ) ∧ (c = 40320 → k = 1) := by
    have hk5 : k ≤ 5 := by omega
    interval_cases k <;> simp [Nat.factorial] at h2 ⊢ <;> omega
  exact ⟨key.1, fun h => by rw [hs, key.2 h, pow_one]⟩

end CFSG.EvenSporadicStandard.M24Std
