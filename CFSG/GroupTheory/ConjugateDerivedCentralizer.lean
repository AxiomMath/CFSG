module

public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G]

theorem mul_mul_inv_mem_commutator_centralizer_of_mem {z g : G}
    (hz : z ∈ ⁅centralizer ({z} : Set G) ⊓ centralizer {g⁻¹ * z * g},
      centralizer ({z} : Set G) ⊓ centralizer {g⁻¹ * z * g}⁆) :
    g * z * g⁻¹ ∈ ⁅centralizer ({z} : Set G), centralizer ({z} : Set G)⁆ := by
  set K := centralizer ({z} : Set G) ⊓ centralizer {g⁻¹ * z * g}
  have hK : K.map (MulAut.conj g).toMonoidHom ≤ centralizer ({z} : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    have hk2 : k * (g⁻¹ * z * g) = g⁻¹ * z * g * k :=
      mem_centralizer_singleton_iff.mp (mem_inf.mp hk).2
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * k * g⁻¹ * z = g * (k * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g * k) * g⁻¹ := by rw [hk2]
      _ = z * (g * k * g⁻¹) := by group
  have h1 : (MulAut.conj g).toMonoidHom z ∈ ⁅K, K⁆.map (MulAut.conj g).toMonoidHom :=
    mem_map_of_mem _ hz
  rw [map_commutator] at h1
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using commutator_mono hK hK h1

end CFSG.GroupTheory
