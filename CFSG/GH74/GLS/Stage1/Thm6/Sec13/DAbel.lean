module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.DCtx

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace D13

variable {x : G} {T V H : Subgroup G} {f : G} (d : D13 x T V H f)
include d

theorem inv_of_cls (hX : ∀ q ∈ Hzero H f, q * x ∈ cls (Mm V H) x) :
    ∀ q ∈ Hzero H f, x * q * x⁻¹ = q⁻¹ := by
  intro q hq
  obtain ⟨m, -, hm⟩ := hX q hq
  have h1 : (q * x) * (q * x) = 1 := by
    rw [hm]
    calc m * x * m⁻¹ * (m * x * m⁻¹) = m * (x * x) * m⁻¹ := by group
      _ = 1 := by rw [d.out.x_sq]; group
  calc x * q * x⁻¹ = x * q * x := by rw [d.out.x_inv]
    _ = q⁻¹ * (q * x * (q * x)) := by group
    _ = q⁻¹ := by rw [h1]; group

theorem inv_mem_V [Finite G] (hinv : ∀ q ∈ Hzero H f, x * q * x⁻¹ = q⁻¹) :
    ∀ q ∈ Hzero H f, q * q = 1 → q ∈ V := by
  intro q hq hq2
  have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq2
  have h1 : x * q = q * x := by
    have := hinv q hq
    rw [hqi] at this
    exact mul_inv_eq_iff_eq_mul.1 this
  have hqH : q ∈ H := d.H0_le hq
  have hq' : q ∈ H ⊓ centralizer ({x} : Set G) := by
    refine ⟨hqH, ?_⟩
    show q ∈ centralizer ({x} : Set G)
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact h1
  rw [InH.C_H_x d.out d.hI] at hq'
  obtain ⟨v, hv, hq'' | hq''⟩ := (d.out.mem_EV).1 hq'
  · rw [hq'']; exact hv
  · exfalso
    apply d.x_not_mem_H0
    have hvH0 : v ∈ Hzero H f := InH.V_le_Hzero d.out d.hI hv
    have hx : x = v⁻¹ * q := by rw [hq'']; group
    rw [hx]
    exact (Hzero H f).mul_mem ((Hzero H f).inv_mem hvH0) hq

end D13

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
