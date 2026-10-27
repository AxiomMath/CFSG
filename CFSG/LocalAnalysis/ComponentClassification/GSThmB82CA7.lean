module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CA1

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr Seven
open scoped commutatorElement

namespace Eight2

variable {X : Type} [Group X] [Finite X]

structure CtxA0 (X : Type) [Group X] [Finite X] where
  s : Setting3 X
  Z : ZData s.h
  b : X
  htL : s.t ∈ Seven.Lay s.h s.y
  ht2 : s.t * s.t ∈ s.h.S ⊓ s.h.secG0 s.y
  hN : normalizer (s.h.S : Set X) ≤ centralizer ({s.h.a} : Set X)
  hbB : b ∈ s.h.secB0 s.y
  hbb : b * b = 1
  hzb : s.t⁻¹ * Z.z * s.t = s.h.a * b

structure CtxA (X : Type) [Group X] [Finite X] extends CtxA0 X where
  hbU : b ∈ s.h.upperP 2

namespace CtxA

variable (c : CtxA X)

abbrev a : X := c.s.h.a

theorem haa : c.a * c.a = 1 := Six.a_mul_a_self c.s.h

theorem hbP : c.b ∈ c.s.h.P := c.s.B0_le_P c.hbB

theorem hb1 : c.b ≠ 1 := by
  intro h
  have h1 := c.hzb
  rw [h, mul_one] at h1
  apply not_conj_a_z c.Z c.s.S_sylow c.hN c.s.t⁻¹
  rw [inv_inv, ← h1]
  group

theorem conj_b_cases {x : X} (hx : x ∈ c.s.h.S) :
    x⁻¹ * c.b * x = c.b ∨ x⁻¹ * c.b * x = c.a * c.b := by
  have hx' := inv_mem hx
  have hb2 : c.b ∈ c.s.h.upperP 2 := c.hbU
  have h1 := ((c.s.h.mem_upperS_succ).mp (mem_inf.mp hb2).1).2 _ hx'
  have h2 : ⁅c.b, x⁻¹⁆ ∈ c.s.h.P := by
    have : ⁅c.b, x⁻¹⁆ = c.b * (x⁻¹ * c.b⁻¹ * x⁻¹⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact mul_mem c.hbP (c.s.h.conj_mem_P hx' (inv_mem c.hbP))
  have h3 : ⁅c.b, x⁻¹⁆ ∈ c.s.h.upperP 1 := mem_inf.mpr ⟨h1, h2⟩
  rw [Six.upperP_one_eq c.s.C_eq] at h3
  rcases Six.eq_one_or_eq_a h3 with h4 | h4
  · left
    rw [commutatorElement_eq_one_iff_mul_comm] at h4
    calc x⁻¹ * c.b * x = c.b * x⁻¹ * x := by rw [← h4]
      _ = c.b := by group
  · right
    rw [commutatorElement_def, inv_inv] at h4
    have hainv : c.a⁻¹ = c.a := inv_eq_of_mul_eq_one_right c.haa
    calc x⁻¹ * c.b * x = (c.b⁻¹ * (c.b * x⁻¹ * c.b⁻¹ * x))⁻¹ := by group
      _ = (c.b⁻¹ * c.a)⁻¹ := by rw [h4]
      _ = c.a * c.b := by rw [mul_inv_rev, inv_inv, hainv]

theorem conj_x_b : c.s.h.x⁻¹ * c.b * c.s.h.x = c.a * c.b := by
  rcases c.conj_b_cases c.s.h.x_mem with h | h
  · exfalso
    apply c.hb1
    have hbB : c.b ∈ c.s.h.B := c.s.h.secB0_le_B c.s.y c.hbB
    have hbx : c.b ∈ c.s.h.B ⊓ conjugate c.s.h.B c.s.h.x := by
      refine mem_inf.mpr ⟨hbB, ?_⟩
      rw [mem_conjugate_iff]
      have h1 : c.s.h.x * c.b * c.s.h.x⁻¹ = c.b := by
        calc c.s.h.x * c.b * c.s.h.x⁻¹ =
            c.s.h.x * (c.s.h.x⁻¹ * c.b * c.s.h.x) * c.s.h.x⁻¹ := by rw [h]
          _ = c.b := by group
      rw [h1]
      exact hbB
    rw [c.s.h.inf_conjugate_x, mem_bot] at hbx
    exact hbx
  · exact h

end CtxA

end Eight2

end CFSG.ComponentClassification.GSThmB
