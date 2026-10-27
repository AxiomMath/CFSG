module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.LA5Cyclic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

theorem finrank_ker_involution_eq_four {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (hdim : Module.finrank (ZMod 2) W = 8) (σ : W ≃ₗ[ZMod 2] W) (hσ : σ * σ = 1) (hσ1 : σ ≠ 1)
    (f : W ≃ₗ[ZMod 2] W) (hf5 : f ^ 5 = 1) (hfσ : f * σ = σ * f)
    (hfpf : ∀ x : W, f x = x → x = 0) :
    Module.finrank (ZMod 2)
      (LinearMap.ker ((σ : W →ₗ[ZMod 2] W) - LinearMap.id)) = 4 := by
  let σL : W →ₗ[ZMod 2] W := (σ : W →ₗ[ZMod 2] W)
  let fL : W →ₗ[ZMod 2] W := (f : W →ₗ[ZMod 2] W)
  let D : W →ₗ[ZMod 2] W := σL - LinearMap.id
  let K : Submodule (ZMod 2) W := LinearMap.ker D
  let I : Submodule (ZMod 2) W := LinearMap.range D
  haveI : Finite K := Subtype.finite
  change Module.finrank (ZMod 2) K = 4
  have hσL : σL * σL = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (σ : W →ₗ[ZMod 2] W) ((σ : W →ₗ[ZMod 2] W) x) = x
    have h := congrArg (fun e : W ≃ₗ[ZMod 2] W => e x) hσ
    simpa [LinearEquiv.mul_apply] using h
  have hfL5 : fL ^ 5 = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change ((f : W →ₗ[ZMod 2] W) ^ 5) x = x
    rw [Module.End.pow_apply]
    have h := congrArg (fun e : W ≃ₗ[ZMod 2] W => e x) hf5
    rw [LinearEquiv.pow_apply] at h
    simpa using h
  have hfσL : fL * σL = σL * fL := by
    have h := congrArg
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := W)) hfσ
    simpa using h
  have hσsq : ∀ x : W, σL (σL x) = x := by
    intro x
    have h := congrArg (fun g : W →ₗ[ZMod 2] W => g x) hσL
    simpa [Module.End.mul_apply] using h
  have hD0 : D * D = 0 := by
    apply LinearMap.ext
    intro x
    change D (D x) = 0
    change σL (σL x - x) - (σL x - x) = 0
    rw [map_sub, hσsq x]
    have hyy : (x - σL x) + (x - σL x) = 0 := by
      rw [← two_smul (ZMod 2) (x - σL x)]
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, zero_smul]
    have hsub : (x - σL x) - (σL x - x) = (x - σL x) + (x - σL x) := by abel
    rw [hsub, hyy]
  have hIleK : I ≤ K := LinearMap.range_le_ker_iff.mpr hD0
  have hrank : Module.finrank (ZMod 2) I + Module.finrank (ZMod 2) K
      = Module.finrank (ZMod 2) W := D.finrank_range_add_finrank_ker
  have hik : Module.finrank (ZMod 2) I ≤ Module.finrank (ZMod 2) K :=
    Submodule.finrank_mono hIleK
  have hkw : Module.finrank (ZMod 2) K ≤ 8 := by
    have h := Submodule.finrank_le K
    rwa [hdim] at h
  have hk4 : 4 ≤ Module.finrank (ZMod 2) K := by
    have hsum : Module.finrank (ZMod 2) I + Module.finrank (ZMod 2) K = 8 := by
      rw [hrank, hdim]
    omega
  have hstab : ∀ x ∈ K, fL x ∈ K := by
    intro x hx
    change D x = 0 at hx
    change D (fL x) = 0
    change σL (fL x) - fL x = 0
    have hcomm : fL (σL x) = σL (fL x) := by
      have h := congrArg (fun g : W →ₗ[ZMod 2] W => g x) hfσL
      simpa [Module.End.mul_apply] using h
    rw [← hcomm, ← map_sub]
    have hx' : σL x - x = 0 := hx
    rw [hx']
    simp
  let fK : K →ₗ[ZMod 2] K := fL.restrict hstab
  have h5K : fK ^ 5 = 1 := by
    change (fL.restrict hstab) ^ 5 = 1
    rw [Module.End.pow_restrict]
    ext x
    have hx := congrArg (fun g : W →ₗ[ZMod 2] W => g (x : W)) hfL5
    simpa using hx
  have hfixK : ∀ x : K, fK x = x → x = 0 := by
    intro x hx
    apply Subtype.ext
    have hx' : fL (x : W) = (x : W) := by
      have hxr : (fL.restrict hstab) x = x := hx
      have h := congrArg (fun y : K => (y : W)) hxr
      simpa [LinearMap.coe_restrict_apply] using h
    exact hfpf (x : W) hx'
  have h4dvd : 4 ∣ Module.finrank (ZMod 2) K :=
    four_dvd_finrank_of_fpf fK h5K hfixK
  have hk48 : Module.finrank (ZMod 2) K = 4 ∨ Module.finrank (ZMod 2) K = 8 := by
    obtain ⟨m, hm⟩ := h4dvd
    have hm1 : 1 ≤ m := by omega
    have hm2 : m ≤ 2 := by omega
    have hmcases : m = 1 ∨ m = 2 := by omega
    rcases hmcases with hm1' | hm2'
    · left; omega
    · right; omega
  rcases hk48 with h4 | h8
  · exact h4
  ·
    exfalso
    have hKtop : K = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h8, hdim])
    have hDzero : D = 0 := LinearMap.ker_eq_top.mp hKtop
    have hσLid : σL = LinearMap.id := sub_eq_zero.mp hDzero
    exact hσ1 (LinearEquiv.ext fun x => by
      have h := congrArg (fun g : W →ₗ[ZMod 2] W => g x) hσLid
      change (σ : W →ₗ[ZMod 2] W) x = x at h
      simpa using h)

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
