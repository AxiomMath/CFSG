module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.LieType.Simplicity

theorem fam_prime_order_simple (G : Type) [Group G] [Finite G] (p : ℕ) (hp : p.Prime)
    (hG : Nat.card G = p) : Nontrivial G ∧ IsSimpleGroup G := by
  have : Fact p.Prime := ⟨hp⟩
  have := isSimpleGroup_of_prime_card hG
  exact ⟨IsSimpleGroup.toNontrivial, this⟩

theorem fam_prime_cyclic_converse (G : Type) [Group G]
    (h : ∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* Multiplicative (ZMod p))) :
    Finite G ∧ Nontrivial G ∧ IsSimpleGroup G := by
  obtain ⟨p, hp, ⟨e⟩⟩ := h
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite G := Finite.of_equiv _ e.symm.toEquiv
  refine ⟨this, fam_prime_order_simple G p hp ?_⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem fam_alternating_converse (G : Type) [Group G]
    (h : ∃ n : ℕ, 5 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) :
    Finite G ∧ Nontrivial G ∧ IsSimpleGroup G := by
  obtain ⟨n, hn, ⟨e⟩⟩ := h
  have := alternatingGroup.isSimpleGroup (α := Fin n) (by simpa using hn)
  have hG : IsSimpleGroup G := e.isSimpleGroup
  exact ⟨Finite.of_equiv _ e.symm.toEquiv, hG.toNontrivial, hG⟩

end CFSG.LieType.Simplicity
