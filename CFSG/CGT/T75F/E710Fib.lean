module

public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Group.Action.Defs

public section

namespace CFSG.CGT.T75F

theorem ncard_eq_mul_of_fibres {α β : Type*} [Finite α] [Finite β] (s : Set α) (t : Set β)
    (f : α → β) (hmaps : ∀ a ∈ s, f a ∈ t) (φ : ℕ)
    (hfib : ∀ b ∈ t, {a | a ∈ s ∧ f a = b}.ncard = φ) : s.ncard = t.ncard * φ := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  have h1 := Finset.card_eq_sum_card_fiberwise (f := f) (s := s.toFinset) (t := t.toFinset)
    (by
      intro a ha
      simp only [Finset.mem_coe, Set.mem_toFinset] at ha ⊢
      exact hmaps a ha)
  have h2 : ∀ b ∈ t.toFinset, (s.toFinset.filter (fun a => f a = b)).card = φ := by
    intro b hb
    rw [Set.mem_toFinset] at hb
    have := hfib b hb
    rw [Set.ncard_eq_toFinset_card'] at this
    rw [← this]
    congr 1
    ext a
    simp
  rw [Set.ncard_eq_toFinset_card' s, Set.ncard_eq_toFinset_card' t, h1,
    Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul]

end CFSG.CGT.T75F
