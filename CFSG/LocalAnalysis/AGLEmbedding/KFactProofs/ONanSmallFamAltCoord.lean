module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltPerm

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open Equiv Equiv.Perm

variable {p : ℕ}

theorem pow_val_add_of_pow_eq_one' [NeZero p] {M : Type*} [Monoid M] {b : M} (hb : b ^ p = 1)
    (i j : ZMod p) : b ^ (i + j).val = b ^ i.val * b ^ j.val := by
  rw [ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod _ hb).symm

theorem exists_alt_coord [Fact p.Prime] {a₁ a₂ : Perm (Fin (2 * p))} {O₁ O₂ : Finset (Fin (2 * p))}
    (h₁ : a₁ ^ p = 1) (h₂ : a₂ ^ p = 1) (hc₁ : O₁.card = p) (hc₂ : O₂.card = p)
    (hd : Disjoint O₁ O₂) (hm₁ : ∀ x, a₁ x ≠ x ↔ x ∈ O₁) (hm₂ : ∀ x, a₂ x ≠ x ↔ x ∈ O₂) :
    ∃ c : ZMod p × Fin 2 ≃ Fin (2 * p), ∀ k : ZMod p,
      a₁ (c (k, 0)) = c (k + 1, 0) ∧ a₁ (c (k, 1)) = c (k, 1) ∧
      a₂ (c (k, 0)) = c (k, 0) ∧ a₂ (c (k, 1)) = c (k + 1, 1) := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  obtain ⟨x₁, hx₁⟩ : O₁.Nonempty := Finset.card_pos.mp (by rw [hc₁]; exact hp.pos)
  obtain ⟨x₂, hx₂⟩ : O₂.Nonempty := Finset.card_pos.mp (by rw [hc₂]; exact hp.pos)
  have hbx₁ : a₁ x₁ ≠ x₁ := (hm₁ x₁).2 hx₁
  have hbx₂ : a₂ x₂ ≠ x₂ := (hm₂ x₂).2 hx₂
  have hfix₁ : ∀ x, x ∈ O₂ → a₁ x = x := fun x hx => by
    by_contra h
    exact Finset.disjoint_left.1 hd ((hm₁ x).1 h) hx
  have hfix₂ : ∀ x, x ∈ O₁ → a₂ x = x := fun x hx => by
    by_contra h
    exact Finset.disjoint_left.1 hd hx ((hm₂ x).1 h)
  let E : ZMod p × Fin 2 → Fin (2 * p) := fun t =>
    if t.2 = 0 then (a₁ ^ t.1.val) x₁ else (a₂ ^ t.1.val) x₂
  have hE0 : ∀ i : ZMod p, E (i, 0) = (a₁ ^ i.val) x₁ := fun i => by simp [E]
  have hE1 : ∀ i : ZMod p, E (i, 1) = (a₂ ^ i.val) x₂ := fun i => by simp [E]
  have hE0mem : ∀ i : ZMod p, E (i, 0) ∈ O₁ := fun i => by
    rw [hE0]
    exact pow_apply_mem_of_moves hm₁ hx₁ _
  have hE1mem : ∀ i : ZMod p, E (i, 1) ∈ O₂ := fun i => by
    rw [hE1]
    exact pow_apply_mem_of_moves hm₂ hx₂ _
  have hinj0 : ∀ i i' : ZMod p, E (i, 0) = E (i', 0) → i = i' := by
    intro i i' h
    rw [hE0, hE0] at h
    exact ZMod.val_injective p
      (pow_apply_injOn hp h₁ hbx₁ (ZMod.val_lt i) (ZMod.val_lt i') h)
  have hinj1 : ∀ i i' : ZMod p, E (i, 1) = E (i', 1) → i = i' := by
    intro i i' h
    rw [hE1, hE1] at h
    exact ZMod.val_injective p
      (pow_apply_injOn hp h₂ hbx₂ (ZMod.val_lt i) (ZMod.val_lt i') h)
  have hinj : Function.Injective E := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    fin_cases j <;> fin_cases j'
    · simp only [Fin.zero_eta] at h ⊢
      rw [hinj0 i i' h]
    · exfalso
      simp only [Fin.zero_eta, Fin.mk_one] at h
      exact Finset.disjoint_left.1 hd (hE0mem i) (h ▸ hE1mem i')
    · exfalso
      simp only [Fin.zero_eta, Fin.mk_one] at h
      exact Finset.disjoint_left.1 hd (hE0mem i') (h.symm ▸ hE1mem i)
    · simp only [Fin.mk_one] at h ⊢
      rw [hinj1 i i' h]
  have hbij : Function.Bijective E := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    simp [ZMod.card, Fintype.card_prod, mul_comm]
  refine ⟨Equiv.ofBijective E hbij, fun k => ?_⟩
  simp only [Equiv.ofBijective_apply]
  refine ⟨?_, hfix₁ _ (hE1mem k), hfix₂ _ (hE0mem k), ?_⟩
  · rw [hE0, hE0, pow_val_add_of_pow_eq_one' h₁, ZMod.val_one, pow_one, Perm.mul_apply,
      ← Perm.mul_apply, ← Perm.mul_apply, (Commute.self_pow a₁ _).eq]
  · rw [hE1, hE1, pow_val_add_of_pow_eq_one' h₂, ZMod.val_one, pow_one, Perm.mul_apply,
      ← Perm.mul_apply, ← Perm.mul_apply, (Commute.self_pow a₂ _).eq]

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
