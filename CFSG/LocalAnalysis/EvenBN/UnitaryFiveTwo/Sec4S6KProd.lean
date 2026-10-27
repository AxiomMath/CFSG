module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Tactic.Group
public import Mathlib.Data.Finset.Attr
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.KProd

open Subgroup

variable {G : Type*} [Group G] (A B : Subgroup G)

theorem commute_subtype (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ (m : ↥A) (n : ↥B), Commute (A.subtype m) (B.subtype n) := fun m n => hc m m.2 n n.2

theorem prodMap_injective (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hi : A ⊓ B = ⊥) :
    Function.Injective (MonoidHom.noncommCoprod A.subtype B.subtype (commute_subtype A B hc)) := by
  rw [MonoidHom.noncommCoprod_injective]
  refine ⟨A.subtype_injective, B.subtype_injective, ?_⟩
  rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
  exact hi

theorem prodMap_range (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    (MonoidHom.noncommCoprod A.subtype B.subtype (commute_subtype A B hc)).range = A ⊔ B := by
  rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]

@[expose] noncomputable def prodEquivSup (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hi : A ⊓ B = ⊥) : (↥A × ↥B) ≃* ↥(A ⊔ B) :=
  (MonoidHom.ofInjective (prodMap_injective A B hc hi)).trans
    (MulEquiv.subgroupCongr (prodMap_range A B hc))

theorem prodEquivSup_apply (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hi : A ⊓ B = ⊥)
    (p : ↥A × ↥B) : ((prodEquivSup A B hc hi p : ↥(A ⊔ B)) : G) = (p.1 : G) * (p.2 : G) := rfl

@[expose] noncomputable def projA (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hi : A ⊓ B = ⊥) :
    ↥(A ⊔ B) →* ↥A :=
  (MonoidHom.fst ↥A ↥B).comp (prodEquivSup A B hc hi).symm.toMonoidHom

@[expose] noncomputable def projB (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hi : A ⊓ B = ⊥) :
    ↥(A ⊔ B) →* ↥B :=
  (MonoidHom.snd ↥A ↥B).comp (prodEquivSup A B hc hi).symm.toMonoidHom

theorem exists_eq_mul (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hi : A ⊓ B = ⊥)
    (x : ↥(A ⊔ B)) :
    (x : G) = (projA A B hc hi x : G) * (projB A B hc hi x : G) := by
  have h := prodEquivSup_apply A B hc hi ((prodEquivSup A B hc hi).symm x)
  rw [MulEquiv.apply_symm_apply] at h
  exact h

theorem projA_prod (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hi : A ⊓ B = ⊥) (a : ↥A) (b : ↥B) :
    projA A B hc hi (prodEquivSup A B hc hi (a, b)) = a := by
  simp [projA]

theorem projB_prod (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hi : A ⊓ B = ⊥) (a : ↥A) (b : ↥B) :
    projB A B hc hi (prodEquivSup A B hc hi (a, b)) = b := by
  simp [projB]

theorem projA_eq_one_iff (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hi : A ⊓ B = ⊥)
    (x : ↥(A ⊔ B)) : projA A B hc hi x = 1 ↔ (x : G) ∈ B := by
  constructor
  · intro h
    have := exists_eq_mul A B hc hi x
    rw [h, Subgroup.coe_one, one_mul] at this
    rw [this]
    exact (projB A B hc hi x).2
  · intro hx
    have : x = prodEquivSup A B hc hi (1, ⟨(x : G), hx⟩) :=
      Subtype.ext (by rw [prodEquivSup_apply]; simp)
    rw [this, projA_prod]

theorem projB_eq_one_iff (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hi : A ⊓ B = ⊥)
    (x : ↥(A ⊔ B)) : projB A B hc hi x = 1 ↔ (x : G) ∈ A := by
  constructor
  · intro h
    have := exists_eq_mul A B hc hi x
    rw [h, Subgroup.coe_one, mul_one] at this
    rw [this]
    exact (projA A B hc hi x).2
  · intro hx
    have : x = prodEquivSup A B hc hi (⟨(x : G), hx⟩, 1) :=
      Subtype.ext (by rw [prodEquivSup_apply]; simp)
    rw [this, projB_prod]

theorem exists_mul_of_mem_sup_of_comm {X : Type*} [Group X] {A B : Subgroup X}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : X} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup X :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [hAB a' ha' b hb]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        rw [mul_inv_rev, ← hAB a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)] }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, by simp⟩)
    (fun b hb => ⟨1, one_mem _, b, hb, by simp⟩)
  exact hle hx

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.KProd
