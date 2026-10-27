module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open QuotientGroup
open scoped Pointwise

theorem card_image_mk_eq_relIndex {G : Type*} [Group G] [Finite G] (A T : Subgroup G) :
    Nat.card ((fun x : G => (x : G ⧸ T)) '' (A : Set G)) = T.relIndex A := by
  let f : A ⧸ T.subgroupOf A → G ⧸ T :=
    Quotient.map' (fun a : A => (a : G)) (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      exact hab)
  have hinj : Function.Injective f := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | _ a => ?_
    induction y using QuotientGroup.induction_on with | _ b => ?_
    have : ((a : G) : G ⧸ T) = ((b : G) : G ⧸ T) := hxy
    rw [QuotientGroup.eq] at this ⊢
    exact this
  have hrange : Set.range f = (fun x : G => (x : G ⧸ T)) '' (A : Set G) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      induction x using QuotientGroup.induction_on with | _ a => exact ⟨a, a.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨((⟨x, hx⟩ : A) : A ⧸ T.subgroupOf A), rfl⟩
  rw [← hrange, Subgroup.relIndex, Subgroup.index, ← Nat.card_congr (Equiv.ofInjective f hinj)]

theorem card_mul_inf_eq {G : Type*} [Group G] [Finite G] (A T B : Subgroup G) (hAB : A ≤ B)
    (hTB : T ≤ B) (hcov : ∀ b ∈ B, ∃ a ∈ A, ∃ t ∈ T, b = a * t) :
    Nat.card B * Nat.card (A ⊓ T : Subgroup G) = Nat.card A * Nat.card T := by
  have hset : ((A : Set G) * (T : Set G)) = (B : Set G) := by
    ext x
    constructor
    · rintro ⟨a, ha, t, ht, rfl⟩
      exact B.mul_mem (hAB ha) (hTB ht)
    · intro hx
      obtain ⟨a, ha, t, ht, rfl⟩ := hcov x hx
      exact ⟨a, ha, t, ht, rfl⟩
  have h1 := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient T (A : Set G)
  rw [hset, card_image_mk_eq_relIndex] at h1
  have h2 : T.relIndex A * Nat.card (T ⊓ A : Subgroup G) = Nat.card A :=
    Subgroup.relIndex_mul_card T A
  have hB : Nat.card B = Nat.card (B : Set G) := rfl
  rw [hB, h1, inf_comm A T]
  calc Nat.card T * T.relIndex A * Nat.card (T ⊓ A : Subgroup G)
      = Nat.card T * (T.relIndex A * Nat.card (T ⊓ A : Subgroup G)) := by ring
    _ = Nat.card A * Nat.card T := by rw [h2, mul_comm]

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
