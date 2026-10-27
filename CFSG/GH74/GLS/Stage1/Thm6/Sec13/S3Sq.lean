module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Struct

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

variable {G : Type*} [Group G]

theorem sq_conj_mem {P : Subgroup G} {m : G} (hm : ∀ h ∈ P, m * h * m⁻¹ ∈ P) :
    ∀ z ∈ sq P, m * z * m⁻¹ ∈ sq P := by
  have hle : sq P ≤ (sq P).comap (MulAut.conj m).toMonoidHom := by
    unfold sq
    rw [Subgroup.closure_le]
    rintro _ ⟨h, hh, rfl⟩
    show m * (h * h) * m⁻¹ ∈ Subgroup.closure {z | ∃ h ∈ P, z = h * h}
    have e : m * (h * h) * m⁻¹ = (m * h * m⁻¹) * (m * h * m⁻¹) := by group
    rw [e]
    exact Subgroup.subset_closure ⟨m * h * m⁻¹, hm h hh, rfl⟩
  intro z hz
  exact hle hz

theorem sq_le_self {P : Subgroup G} : sq P ≤ P := by
  unfold sq
  rw [Subgroup.closure_le]
  rintro _ ⟨h, hh, rfl⟩
  exact P.mul_mem hh hh

theorem mul_self_mem_sq {P : Subgroup G} {a : G} (ha : a ∈ P) : a * a ∈ sq P :=
  Subgroup.subset_closure ⟨a, ha, rfl⟩

namespace Ctx3

variable {x : G} {T V H : Subgroup G} {f : G} (c : Ctx3 G x T V H f)
include c

theorem V_le_sq [Finite G] (ha : ∃ a ∈ Hzero H f, a * a ≠ 1) : V ≤ sq (Hzero H f) := by
  obtain ⟨a, haP, ha2⟩ := ha
  exact c.V_le_of_invariant sq_le_self
    (one_lt_card_of_ne_one (mul_self_mem_sq haP) ha2)
    (sq_conj_mem (fun h hh => c.H0_norm_H x c.x_mem_H h hh))
    (sq_conj_mem (fun h hh => c.f_conj_H0 hh))

end Ctx3

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
