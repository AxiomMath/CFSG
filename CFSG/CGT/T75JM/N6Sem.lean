module

public import CFSG.CGT.T75JM.N6Rels

public section

namespace CFSG.CGT.T75JM

variable {H : Type*} [Group H]

structure Sem6 (f : Fin 6 → H) : Prop where
  x2 : f 0 * f 0 = 1
  y4 : f 1 * f 1 * f 1 * f 1 = 1
  xy5 : (f 0 * f 1) ^ 5 = 1
  xyy5 : (f 0 * f 1 * f 1) ^ 5 = 1
  sq2 : f 2 * f 2 = 1
  sq3 : f 3 * f 3 = 1
  sq4 : f 4 * f 4 = 1
  sq5 : f 5 * f 5 = 1
  c23 : f 2 * f 3 = f 3 * f 2
  c24 : f 2 * f 4 = f 4 * f 2
  c25 : f 2 * f 5 = f 5 * f 2
  c34 : f 3 * f 4 = f 4 * f 3
  c35 : f 3 * f 5 = f 5 * f 3
  c45 : f 4 * f 5 = f 5 * f 4
  ax2 : f 0 * f 2 * (f 0)⁻¹ = f 2
  ax3 : f 0 * f 3 * (f 0)⁻¹ = f 2 * f 3 * f 5
  ax4 : f 0 * f 4 * (f 0)⁻¹ = f 4 * f 5
  ax5 : f 0 * f 5 * (f 0)⁻¹ = f 5
  ay2 : f 1 * f 2 * (f 1)⁻¹ = f 3 * f 5
  ay3 : f 1 * f 3 * (f 1)⁻¹ = f 4
  ay4 : f 1 * f 4 * (f 1)⁻¹ = f 2 * f 4
  ay5 : f 1 * f 5 * (f 1)⁻¹ = f 2 * f 5

theorem rel_comm {a b : H} (hc : a * b = b * a) (ha : a * a = 1) (hb : b * b = 1) :
    a * b * a * b = 1 := by
  calc a * b * a * b = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hc]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha, hb, one_mul]

theorem rel_act {g t u : H} (h : g * t * g⁻¹ = u) : g * t * g⁻¹ * u⁻¹ = 1 := by
  rw [h, mul_inv_cancel]

theorem lift_rels6_eq_one {f : Fin 6 → H} (hf : Sem6 f) :
    ∀ r ∈ rels6, FreeGroup.lift f (FreeGroup.mk r) = 1 := by
  intro r hr
  simp only [rels6, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [FreeGroup.lift_mk] using hf.x2
  · simpa [FreeGroup.lift_mk, mul_assoc] using hf.y4
  · simpa [FreeGroup.lift_mk, pow_succ, mul_assoc] using hf.xy5
  · simpa [FreeGroup.lift_mk, pow_succ, mul_assoc] using hf.xyy5
  · simpa [FreeGroup.lift_mk] using hf.sq2
  · simpa [FreeGroup.lift_mk, mul_assoc] using rel_comm hf.c23 hf.sq2 hf.sq3
  · simpa [FreeGroup.lift_mk, mul_assoc] using rel_comm hf.c24 hf.sq2 hf.sq4
  · simpa [FreeGroup.lift_mk, mul_assoc] using rel_comm hf.c25 hf.sq2 hf.sq5
  · simpa [FreeGroup.lift_mk] using hf.sq3
  · simpa [FreeGroup.lift_mk, mul_assoc] using rel_comm hf.c34 hf.sq3 hf.sq4
  · simpa [FreeGroup.lift_mk, mul_assoc] using rel_comm hf.c35 hf.sq3 hf.sq5
  · simpa [FreeGroup.lift_mk] using hf.sq4
  · simpa [FreeGroup.lift_mk, mul_assoc] using rel_comm hf.c45 hf.sq4 hf.sq5
  · simpa [FreeGroup.lift_mk] using hf.sq5
  · simpa [FreeGroup.lift_mk, mul_assoc] using rel_act hf.ax2
  · simpa [FreeGroup.lift_mk, mul_assoc] using rel_act hf.ax3
  · simpa [FreeGroup.lift_mk, mul_assoc] using rel_act hf.ax4
  · simpa [FreeGroup.lift_mk, mul_assoc] using rel_act hf.ax5
  · simpa [FreeGroup.lift_mk, mul_assoc] using rel_act hf.ay2
  · simpa [FreeGroup.lift_mk, mul_assoc] using rel_act hf.ay3
  · simpa [FreeGroup.lift_mk, mul_assoc] using rel_act hf.ay4
  · simpa [FreeGroup.lift_mk, mul_assoc] using rel_act hf.ay5

end CFSG.CGT.T75JM
