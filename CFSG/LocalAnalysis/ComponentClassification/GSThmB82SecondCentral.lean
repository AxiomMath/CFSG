module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CaseASplit

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

namespace Eight2

namespace CtxA0

variable {X : Type} [Group X] [Finite X] (c : CtxA0 X)

theorem b_ne_one : c.b ≠ 1 := by
  intro h
  have h1 := c.hzb
  rw [h, mul_one] at h1
  apply not_conj_a_z c.Z c.s.S_sylow c.hN c.s.t⁻¹
  rw [inv_inv, ← h1]
  group

theorem b_comm_of_mem_S0 {w : X} (hw : w ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y) :
    c.b * w = w * c.b := by
  have h1 := c.ab_comm_of_mem_S0 hw
  have hwa : w * c.s.h.a = c.s.h.a * w := c.s.h.comm_a (mem_inf.mp hw).1
  have haa : c.s.h.a * c.s.h.a = 1 := Six.a_mul_a_self c.s.h
  calc c.b * w = c.s.h.a * (c.s.h.a * c.b * w) := by
        rw [← mul_assoc, ← mul_assoc, haa, one_mul]
    _ = c.s.h.a * (w * (c.s.h.a * c.b)) := by rw [h1]
    _ = (c.s.h.a * w) * c.s.h.a * c.b := by group
    _ = (w * c.s.h.a) * c.s.h.a * c.b := by rw [hwa]
    _ = w * c.b := by rw [mul_assoc w, haa, mul_one]

end CtxA0

end Eight2

end CFSG.ComponentClassification.GSThmB
