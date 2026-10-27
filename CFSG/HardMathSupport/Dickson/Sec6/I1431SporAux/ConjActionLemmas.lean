module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Set.Card

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Subgroup

section Fixed

variable {G : Type*} [Group G]

theorem card_fixedBy_eq_ncard {K : Subgroup G} {D : Set G} [MulAction K D]
    (hsmul : ∀ (g : K) (s : D), ((g • s : D) : G) = g * s * g⁻¹) (g : K) :
    Nat.card (MulAction.fixedBy D g) = {t | t ∈ D ∧ (g : G) * t = t * g}.ncard := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr
    { toFun := fun ω => ⟨ω.1.1, ω.1.2, ?_⟩
      invFun := fun t => ⟨⟨t.1, t.2.1⟩, ?_⟩
      left_inv := fun ω => rfl
      right_inv := fun t => rfl }
  · have h1 : g • ω.1 = ω.1 := MulAction.mem_fixedBy.1 ω.2
    have h2 := congrArg Subtype.val h1
    rw [hsmul, Subgroup.coe_inv, mul_inv_eq_iff_eq_mul] at h2
    exact h2
  · refine MulAction.mem_fixedBy.2 (Subtype.ext ?_)
    rw [hsmul]
    show (g : G) * t.1 * (g : G)⁻¹ = t.1
    rw [mul_inv_eq_iff_eq_mul]
    exact t.2.2

theorem card_stabilizer_eq {K : Subgroup G} {D : Set G} [MulAction K D]
    (hsmul : ∀ (g : K) (s : D), ((g • s : D) : G) = g * s * g⁻¹) (ω : D) :
    Nat.card (MulAction.stabilizer K ω) = Nat.card ↥(K ⊓ centralizer ({(ω : G)} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨(g.1 : G), g.1.2, mem_centralizer_singleton_iff.2 (by
        have h1 := congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 g.2)
        rw [hsmul, Subgroup.coe_inv, mul_inv_eq_iff_eq_mul] at h1
        exact h1)⟩
      invFun := fun h => ⟨⟨(h : G), (mem_inf.1 h.2).1⟩, MulAction.mem_stabilizer_iff.2
        (Subtype.ext (by
          rw [hsmul]
          show (h : G) * (ω : G) * (h : G)⁻¹ = (ω : G)
          rw [mul_inv_eq_iff_eq_mul]
          exact mem_centralizer_singleton_iff.1 (mem_inf.1 h.2).2))⟩
      left_inv := fun g => rfl
      right_inv := fun h => rfl }

end Fixed

end CFSG.HardMathSupport.Dickson.Sec6.I1431
