module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Fink

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec8T84DCtx (G : Type) [Group G] [Finite G] (t : G) (E X1 X2 : Subgroup G) : Prop where
  elem : IsElemAb2 E 8
  hX : Sec8X G t E X1 X2
  t_sq : t * t = 1
  hCE : centralizer (E : Set G) = E ⊔ oddCoreIn (normalizer (E : Set G))
  hO : oddCoreIn (normalizer (E : Set G)) ≤ centralizer (E : Set G)

structure Sec8T84DDec (G : Type) [Group G] [Finite G] (t : G) (E X1 X2 E1 E2 : Subgroup G) :
    Prop where
  le1 : E1 ≤ E
  le2 : E2 ≤ E
  e16_1 : IsElemAb2 E1 4
  e16_2 : IsElemAb2 E2 4
  inf : E1 ⊓ E2 = ⊥
  sup : E1 ⊔ E2 = E
  inv1 : ∀ x ∈ X1, ∀ e ∈ E1, x * e * x⁻¹ ∈ E1
  inv2 : ∀ x ∈ X2, ∀ e ∈ E2, x * e * x⁻¹ ∈ E2
  triv1 : ∀ x ∈ X1, ∀ e ∈ E2, x * e * x⁻¹ = e
  triv2 : ∀ x ∈ X2, ∀ e ∈ E1, x * e * x⁻¹ = e
  faith1 : ∀ x ∈ X1, (∀ e ∈ E1, x * e * x⁻¹ = e) → x ∈ centralizer (E : Set G)
  faith2 : ∀ x ∈ X2, (∀ e ∈ E2, x * e * x⁻¹ = e) → x ∈ centralizer (E : Set G)
  fpf1 : ∀ x ∈ X1, x ^ 5 ∈ centralizer (E : Set G) → x ∉ centralizer (E : Set G) →
    ∀ e ∈ E1, x * e * x⁻¹ = e → e = 1
  fpf2 : ∀ x ∈ X2, x ^ 5 ∈ centralizer (E : Set G) → x ∉ centralizer (E : Set G) →
    ∀ e ∈ E2, x * e * x⁻¹ = e → e = 1
  ex5_1 : ∃ x ∈ X1, x ^ 5 ∈ centralizer (E : Set G) ∧ x ∉ centralizer (E : Set G)
  ex5_2 : ∃ x ∈ X2, x ^ 5 ∈ centralizer (E : Set G) ∧ x ∉ centralizer (E : Set G)
  trans1 : ∀ v ∈ E1, v ≠ 1 → ∀ w ∈ E1, w ≠ 1 → ∃ x ∈ X1, x * v * x⁻¹ = w
  trans2 : ∀ v ∈ E2, v ≠ 1 → ∀ w ∈ E2, w ≠ 1 → ∃ x ∈ X2, x * v * x⁻¹ = w
  swap1 : ∀ e ∈ E1, t * e * t⁻¹ ∈ E2
  swap2 : ∀ e ∈ E2, t * e * t⁻¹ ∈ E1

variable {G : Type} [Group G] [Finite G] {t : G} {E X1 X2 E1 E2 : Subgroup G}

theorem Sec8X.symm' (h : Sec8X G t E X1 X2) : Sec8X G t E X2 X1 where
  c_le1 := h.c_le2
  c_le2 := h.c_le1
  le1 := h.le2
  le2 := h.le1
  comm := fun a ha b hb => by
    have := inv_mem (h.comm b hb a ha)
    simpa [mul_assoc] using this
  inf := by rw [inf_comm]; exact h.inf
  sup := by rw [sup_comm X2 X1]; exact h.sup
  t_not := by rw [sup_comm X2 X1]; exact h.t_not
  swap1 := h.swap2
  swap2 := h.swap1
  quot1 := h.quot2
  quot2 := h.quot1

theorem Sec8T84DCtx.symm (h : Sec8T84DCtx G t E X1 X2) : Sec8T84DCtx G t E X2 X1 :=
  ⟨h.elem, h.hX.symm', h.t_sq, h.hCE, h.hO⟩

theorem Sec8T84DDec.symm (h : Sec8T84DDec G t E X1 X2 E1 E2) : Sec8T84DDec G t E X2 X1 E2 E1 where
  le1 := h.le2
  le2 := h.le1
  e16_1 := h.e16_2
  e16_2 := h.e16_1
  inf := by rw [inf_comm]; exact h.inf
  sup := by rw [sup_comm]; exact h.sup
  inv1 := h.inv2
  inv2 := h.inv1
  triv1 := h.triv2
  triv2 := h.triv1
  faith1 := h.faith2
  faith2 := h.faith1
  fpf1 := h.fpf2
  fpf2 := h.fpf1
  ex5_1 := h.ex5_2
  ex5_2 := h.ex5_1
  trans1 := h.trans2
  trans2 := h.trans1
  swap1 := h.swap2
  swap2 := h.swap1

end CFSG.OddStandard.SmallF3.Omega
