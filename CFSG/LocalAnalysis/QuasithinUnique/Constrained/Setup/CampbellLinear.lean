module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSL2
public import Mathlib.RingTheory.PiTensorProduct

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Matrix Module
open scoped LinearAlgebra.Projectivization


theorem involution_image_fixed_lift {k E V : Type*} [Field k] [CharP k 2] [AddCommGroup E]
    [Module k E] [AddCommGroup V] [Module k V] (bE : Module.End k E) (bV : Module.End k V)
    (hE : bE * bE = 1) (_hV : bV * bV = 1) (φ : E →ₗ[k] V) (hφ : Function.Surjective φ)
    (hcomm : φ ∘ₗ bE = bV ∘ₗ φ) (hker : ∀ x ∈ LinearMap.ker φ, bE x = x) :
    ∀ e : E, φ e ∈ LinearMap.range (bV - 1) → bE e = e := by
  intro e he
  obtain ⟨v, hv⟩ := he
  obtain ⟨x, rfl⟩ := hφ v
  have hc : ∀ y, φ (bE y) = bV (φ y) := fun y => LinearMap.congr_fun hcomm y
  have hv' : bV (φ x) - φ x = φ e := by
    rw [LinearMap.sub_apply, Module.End.one_apply] at hv
    exact hv
  have h1 : φ (e - (bE - 1) x) = 0 := by
    rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, map_sub, hc, ← hv']
    abel
  have hz : bE (e - (bE - 1) x) = e - (bE - 1) x := hker _ (LinearMap.mem_ker.mpr h1)
  have h2 : ((bE - 1) * (bE - 1)) = 0 := by
    have h2' : (2 : Module.End k E) = 0 := by
      have : ((2 : ℕ) : Module.End k E) = 0 := by
        rw [← map_natCast (algebraMap k (Module.End k E)) 2, CharP.cast_eq_zero k 2, map_zero]
      simpa using this
    have e1 : (bE - 1) * (bE - 1) = bE * bE - bE - bE + 1 := by noncomm_ring
    have e2 : (1 : Module.End k E) - bE - bE + 1 = 2 * (1 - bE) := by noncomm_ring
    rw [e1, hE, e2, h2', zero_mul]
  have h3 : (bE - 1) e = 0 := by
    have hsplit : e = (bE - 1) x + (e - (bE - 1) x) := by abel
    rw [hsplit, map_add]
    have h4 : (bE - 1) ((bE - 1) x) = 0 := by
      have := LinearMap.congr_fun h2 x
      simpa [Module.End.mul_apply] using this
    have h5 : (bE - 1) (e - (bE - 1) x) = 0 := by
      rw [LinearMap.sub_apply, Module.End.one_apply, hz, sub_self]
    rw [h4, h5, add_zero]
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h3
  exact h3


end CFSG.QuasithinUnique.Setup.Campbell
