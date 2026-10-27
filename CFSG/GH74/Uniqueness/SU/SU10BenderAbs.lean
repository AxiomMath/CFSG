module

public import CFSG.GH74.Uniqueness.Bender.Lemma32

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup CFSG.GH74.Uniqueness.Bender

variable {K : Type} [Group K]

theorem benderType_structure
    [Finite K] {n i e : ℕ} (h : BenderType K n i e) (Q : Sylow 2 K) :
    2 ≤ n ∧ ∃ (Z : Subgroup K) (y : K), Z ≤ (Q : Subgroup K) ∧ Open.IsElemAbelian 2 Z ∧
      Nat.card Z = 2 ^ n ∧ (∀ g ∈ (Q : Subgroup K), g * g = 1 → g ∈ Z) ∧
      y ∈ normalizer (Z : Set K) ∧
      (∀ a ∈ Z, ∀ b ∈ Z, a ≠ 1 → b ≠ 1 → ∃ j : ℤ, y ^ j * a * (y ^ j)⁻¹ = b) := by
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hL := h.lemma_3_2 Q hc.sq_eq_one hc.not_mem
  have hn : 2 ≤ n := by
    rcases h.cases' with ⟨-, -, hn⟩ | ⟨-, -, a, ha, rfl⟩ | ⟨-, -, hn⟩ <;> omega
  obtain ⟨y, hy⟩ := hL.isCyclic_commutator.exists_generator
  have hyb : (y : K) ∈ borel (Q : Subgroup K) := by
    have h1 : (y : K) ∈ cartan (Q : Subgroup K) t :=
      (hc.mem_commutator_cartan_iff.mp y.2).1
    exact cartan_le_borel _ _ h1
  refine ⟨hn, rootCenter (Q : Subgroup K), (y : K), rootCenter_le _, hL.elemAbelian_center,
    hL.card_center, ?_, ?_, ?_⟩
  · intro g hgQ hg2
    by_cases hg1 : g = 1
    · rw [hg1]
      exact one_mem _
    · have hord : orderOf g = 2 := orderOf_eq_prime (by rw [sq]; exact hg2) hg1
      exact ((hL.involutions_iff g).mp ⟨le_borel _ hgQ, hord⟩).1
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact conj_mem_rootCenter hyb hx
    · intro hx
      have := conj_mem_rootCenter ((borel (Q : Subgroup K)).inv_mem hyb) hx
      simpa [mul_assoc] using this
  · intro a ha b hb ha1 hb1
    obtain ⟨d, ⟨hd, hbd⟩, -⟩ := hL.regular a ha ha1 b hb hb1
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hy ⟨d, hd⟩)
    have hdm : d = (y : K) ^ m := by
      have := congrArg Subtype.val hm
      simpa using this.symm
    refine ⟨-m, ?_⟩
    rw [hbd, hdm, zpow_neg, inv_inv]

end CFSG.GH74.Uniqueness.SU.SU10
