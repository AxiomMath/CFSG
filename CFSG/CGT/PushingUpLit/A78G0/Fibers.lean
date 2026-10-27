module

public import Mathlib.Data.Set.Card

public section

namespace CFSG.CGT.PushingUpLit.A78G0

theorem ncard_pairs {α β : Type*} [Finite α] [Finite β] (s : Set α) (F : α → Set β) (c : ℕ)
    (hF : ∀ a ∈ s, (F a).ncard = c) :
    {p : α × β | p.1 ∈ s ∧ p.2 ∈ F p.1}.ncard = s.ncard * c := by
  classical
  have : Fintype ↥s := Fintype.ofFinite _
  let e : ↥{p : α × β | p.1 ∈ s ∧ p.2 ∈ F p.1} ≃ Σ a : ↥s, ↥(F a) :=
    { toFun := fun p => ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩⟩
      invFun := fun q => ⟨(q.1.1, q.2.1), q.1.2, q.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  have hc : ∀ a : ↥s, Nat.card ↥(F a) = c := fun a => by
    rw [Nat.card_coe_set_eq]
    exact hF a a.2
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_sigma]
  simp only [hc, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

theorem ncard_offDiag_eq {α : Type*} (s : Set α) (hs : s.Finite) :
    s.offDiag.ncard = s.ncard * (s.ncard - 1) := by
  classical
  obtain ⟨t, rfl⟩ := hs.exists_finset_coe
  rw [← Finset.coe_offDiag, Set.ncard_coe_finset, Set.ncard_coe_finset, Finset.offDiag_card,
    Nat.mul_sub_one]

end CFSG.CGT.PushingUpLit.A78G0
