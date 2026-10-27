module

public import CFSG.Certificates.Kernel.QTwoD6.Glue
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.StandardType.QTwoD6.K

open Module CFSG.KC.QTwoD6K CFSG.StandardType.QTwoLin

theorem absD_of_planeFact {B : Subgroup (V7 ≃ₗ[ZMod 3] V7)} {k : Nat} (hP : PlaneFact B k)
    {G : V7 ≃ₗ[ZMod 3] V7} (hG : (G : V7 →ₗ[ZMod 3] V7) = twL k) :
    ∃ ψ ∈ B, ∀ v ∈ Dplane, ψ (G v) ∈ Dplane := by
  obtain ⟨ψ, hψB, h1, h2⟩ := hP
  have hGv : ∀ v, twL k v = G v := fun v => by rw [← hG, LinearEquiv.coe_coe]
  rw [hGv, hGv] at h1 h2
  have hspan : Submodule.span (ZMod 3) {G e0, G wb} = Dplane.map (G : V7 →ₗ[ZMod 3] V7) := by
    rw [Dplane, Submodule.map_span, Set.image_pair, LinearEquiv.coe_coe]
  have hle : Dplane.map (ψ : V7 →ₗ[ZMod 3] V7) ≤ Dplane.map (G : V7 →ₗ[ZMod 3] V7) := by
    rw [Dplane, Submodule.map_span, Submodule.span_le, Set.image_pair, Set.pair_subset_iff,
      ← Dplane, ← hspan]
    exact ⟨h1, h2⟩
  have heq : Dplane.map (ψ : V7 →ₗ[ZMod 3] V7) = Dplane.map (G : V7 →ₗ[ZMod 3] V7) :=
    Submodule.eq_of_le_of_finrank_eq hle (by
      rw [LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq])
  refine ⟨ψ⁻¹, B.inv_mem hψB, fun v hv => ?_⟩
  have hm : G v ∈ Dplane.map (ψ : V7 →ₗ[ZMod 3] V7) := by
    rw [heq]
    exact Submodule.mem_map_of_mem hv
  obtain ⟨u, hu, hψu⟩ := hm
  rw [LinearEquiv.coe_coe] at hψu
  rw [← hψu]
  change ψ.symm (ψ u) ∈ Dplane
  rw [LinearEquiv.symm_apply_apply]
  exact hu

theorem us_ub : ∀ i j : Fin 7, us i (ub j) = if i = j then 1 else 0 := by
  decide +kernel

theorem sum_us_ub_single : ∀ i : Fin 7,
    ∑ j : Fin 7, us j (Pi.single i 1) • ub j = (Pi.single i 1 : V7) := by
  decide +kernel

theorem eq_sum_us_ub (v : V7) : v = ∑ j : Fin 7, us j v • ub j := by
  have hL : (∑ j : Fin 7, (us j).smulRight (ub j)) = (LinearMap.id : V7 →ₗ[ZMod 3] V7) := by
    refine LinearMap.pi_ext fun i x => ?_
    have hx : (Pi.single i x : V7) = x • (Pi.single i 1 : V7) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hx, map_smul, LinearMap.id_apply, LinearMap.sum_apply]
    simp only [LinearMap.smulRight_apply]
    rw [sum_us_ub_single]
  have h := LinearMap.congr_fun hL v
  rw [LinearMap.sum_apply, LinearMap.id_apply] at h
  simp only [LinearMap.smulRight_apply] at h
  exact h.symm

theorem twL_e0 : ∀ k : Fin 4, twL k e0 = ((twLam k : Nat) : ZMod 3) • e0 := by
  decide +kernel

theorem twL_hvec : ∀ k : Fin 4, ∀ i : Fin 6,
    twL k (hvec i) = ((twC k : Nat) : ZMod 3) • hvec (swapD6 i) := by
  decide +kernel

end CFSG.StandardType.QTwoD6.K

end
