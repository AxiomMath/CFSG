module
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.Bound.Init

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

theorem coe_sup_eq_mul_of_commute {W₁ W₂ : Subgroup G}
    (hcomm : ∀ x ∈ W₁, ∀ y ∈ W₂, Commute x y) :
    ((W₁ ⊔ W₂ : Subgroup G) : Set G) = (W₁ : Set G) * (W₂ : Set G) := by
  refine Subgroup.coe_mul_of_left_le_normalizer_right W₁ W₂ ?_
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  intro x hx
  exact Subgroup.mem_centralizer_iff.2 fun h hh => ((hcomm x hx h hh).symm).eq

theorem eq_sup_of_coe_eq_mul {W W₁ W₂ : Subgroup G}
    (hW : (W : Set G) = (W₁ : Set G) * (W₂ : Set G))
    (hcomm : ∀ x ∈ W₁, ∀ y ∈ W₂, Commute x y) : W = W₁ ⊔ W₂ :=
  SetLike.coe_injective (hW.trans (coe_sup_eq_mul_of_commute hcomm).symm)

noncomputable def mulEquivProdOfCoeEqMul {W W₁ W₂ : Subgroup G}
    (hW : (W : Set G) = (W₁ : Set G) * (W₂ : Set G)) (hinter : W₁ ⊓ W₂ = ⊥)
    (hcomm : ∀ x ∈ W₁, ∀ y ∈ W₂, Commute x y) : (W₁ × W₂) ≃* W := by
  have comm : ∀ (m : W₁) (n : W₂), Commute (W₁.subtype m) (W₂.subtype n) :=
    fun m n => hcomm m m.2 n n.2
  have hinj : Function.Injective ((W₁.subtype).noncommCoprod (W₂.subtype) comm) := by
    have h := Subgroup.mul_injective_of_disjoint (H₁ := W₁) (H₂ := W₂) (disjoint_iff.2 hinter)
    intro a b hab
    rw [MonoidHom.noncommCoprod_apply, MonoidHom.noncommCoprod_apply] at hab
    exact h hab
  refine (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr ?_)
  rw [MonoidHom.noncommCoprod_range, Subgroup.subtype_range, Subgroup.subtype_range,
    eq_sup_of_coe_eq_mul hW hcomm]

@[simp]
theorem coe_mulEquivProdOfCoeEqMul_apply {W W₁ W₂ : Subgroup G}
    (hW : (W : Set G) = (W₁ : Set G) * (W₂ : Set G)) (hinter : W₁ ⊓ W₂ = ⊥)
    (hcomm : ∀ x ∈ W₁, ∀ y ∈ W₂, Commute x y) (x : W₁ × W₂) :
    ((mulEquivProdOfCoeEqMul hW hinter hcomm x : W) : G) = (x.1 : G) * (x.2 : G) := (rfl)

theorem nonempty_sdiff_union {W W₁ W₂ : Subgroup G}
    (hW : (W : Set G) = (W₁ : Set G) * (W₂ : Set G)) (hW₁ : W₁ ≠ ⊥) (hW₂ : W₂ ≠ ⊥)
    (hinter : W₁ ⊓ W₂ = ⊥) :
    ((W : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G))).Nonempty := by
  obtain ⟨w₁, hw₁, hw₁1⟩ := W₁.bot_or_exists_ne_one.resolve_left hW₁
  obtain ⟨w₂, hw₂, hw₂1⟩ := W₂.bot_or_exists_ne_one.resolve_left hW₂
  refine ⟨w₁ * w₂, hW ▸ Set.mul_mem_mul hw₁ hw₂, ?_⟩
  rintro (h | h)
  · refine hw₂1 ?_
    have hmem : w₂ ∈ W₁ := by
      have := W₁.mul_mem (W₁.inv_mem hw₁) h
      simpa using this
    simpa [hinter] using Subgroup.mem_inf.2 ⟨hmem, hw₂⟩
  · refine hw₁1 ?_
    have hmem : w₁ ∈ W₂ := by
      have := W₂.mul_mem h (W₂.inv_mem hw₂)
      simpa using this
    simpa [hinter] using Subgroup.mem_inf.2 ⟨hw₁, hmem⟩

theorem centralizer_le_of_normalizer_sdiff_union_eq {W W₁ W₂ : Subgroup G}
    (_hW₁ : W₁ ≠ ⊥) (_hW₂ : W₂ ≠ ⊥)
    (_hW : (W : Set G) = (W₁ : Set G) * (W₂ : Set G))
    (_hinter : W₁ ⊓ W₂ = ⊥)
    (_hcomm : ∀ x ∈ W₁, ∀ y ∈ W₂, Commute x y)
    (hND : Subgroup.normalizer ((W : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G))) = W) :
    Subgroup.centralizer (W : Set G) ≤ W :=
  hND.le.trans' <| (Subgroup.centralizer_le Set.sdiff_subset).trans
    (Subgroup.centralizer_le_normalizer _)

end CFSG.FeitThompson
