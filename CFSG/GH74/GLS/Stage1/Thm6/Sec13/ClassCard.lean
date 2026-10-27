module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

variable {G : Type*} [Group G]

@[expose] def cls (M : Subgroup G) (x : G) : Set G := {y | ∃ m ∈ M, y = m * x * m⁻¹}

theorem card_cls_mul [Finite G] (M : Subgroup G) {x : G} (hx : x ∈ M) :
    Nat.card (cls M x) * Nat.card ↥(M ⊓ centralizer ({x} : Set G)) = Nat.card M := by
  let x' : ↥M := ⟨x, hx⟩
  have h1 := Subgroup.index_centralizer_eq_ncard x'
  have h2 := Subgroup.index_mul_card (Subgroup.centralizer ({x'} : Set ↥M))
  have h3 : (conjugatesOf x').ncard = Nat.card (cls M x) := by
    have : cls M x = Subtype.val '' conjugatesOf x' := by
      ext y
      constructor
      · rintro ⟨m, hm, rfl⟩
        refine ⟨⟨m * x * m⁻¹, M.mul_mem (M.mul_mem hm hx) (M.inv_mem hm)⟩, ?_, rfl⟩
        show IsConj x' _
        rw [isConj_iff]
        exact ⟨⟨m, hm⟩, Subtype.ext rfl⟩
      · rintro ⟨a, ha, rfl⟩
        have ha' : IsConj x' a := ha
        rw [isConj_iff] at ha'
        obtain ⟨c, hc⟩ := ha'
        exact ⟨c, c.2, by rw [← hc]; rfl⟩
    rw [this, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ Subtype.val_injective]
  have h4 : Nat.card ↥(Subgroup.centralizer ({x'} : Set ↥M)) =
      Nat.card ↥(M ⊓ centralizer ({x} : Set G)) := by
    refine Nat.card_congr
      { toFun := fun c => ⟨c.1.1, c.1.2, ?_⟩
        invFun := fun d => ⟨⟨d.1, d.2.1⟩, ?_⟩
        left_inv := fun c => rfl
        right_inv := fun d => rfl }
    · show c.1.1 ∈ centralizer ({x} : Set G)
      rw [mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact congrArg Subtype.val (mem_centralizer_iff.1 c.2 x' rfl)
    · rw [mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      apply Subtype.ext
      exact mem_centralizer_iff.1 d.2.2 x rfl
  rw [h4, h1, h3] at h2
  exact h2

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
