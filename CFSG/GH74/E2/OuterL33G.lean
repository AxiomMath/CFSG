
module

public import CFSG.GH74.E2.OuterL33GBase

public import CFSG.GH74.E2.OuterL33
public import CFSG.GH74.E2.OuterCore
public import CFSG.GH74.E2.L33AutTable
public import CFSG.GH74.E2.LocalLeaves
public import CFSG.GH74.E2.Alpha1Core
public meta import Mathlib
public meta import CFSG.CharacterTheory.Semidihedral.Model
public meta import CFSG.GH74.E2.SD16Cert
public import CFSG.GH74.E2.Alpha1CoreInputs
public import Certificates.Certificate5015
public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.PSLN
public import CFSG.GH74.KGroups.L33Inputs

public section

namespace CFSG.GH74.E2

open Subgroup CFSG.GH74.GLS

attribute [local instance] instDecEqSD16

attribute [local instance] instDecEqSD16

theorem sd16_exists_central :
    ∃ z : SD16M, (∀ w : SD16M, w * z = z * w) ∧ z * z = 1 ∧ z ≠ 1 :=
  Certificates.certificate5015

theorem exists_central_involution_sylow
    {G : Type} [Group G] {K SK S₁ : Subgroup G}
    (hSKK : SK ≤ K) (hSKS : SK ≤ S₁) (hKn : ∀ x ∈ S₁, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (hS₁K : ∀ y ∈ S₁, y ∈ K → y ∈ SK) (eK : ↥SK ≃* SD16M) :
    ∃ s ∈ SK, s ≠ 1 ∧ s * s = 1 ∧ ∀ x ∈ S₁, x * s = s * x := by
  obtain ⟨z, hzc, hz2, hz1⟩ := sd16_exists_central
  have hz : (∀ w : SD16M, w * z = z * w) ∧ z * z = 1 := ⟨hzc, hz2⟩
  refine ⟨(eK.symm z : G), (eK.symm z).2, ?_, ?_, ?_⟩
  · intro h
    apply hz1
    have h' : eK.symm z = 1 := Subtype.ext h
    simpa using congrArg eK h'
  · have h' : eK.symm z * eK.symm z = 1 := by rw [← map_mul, hz.2, map_one]
    simpa using congrArg (fun y : ↥SK => (y : G)) h'
  · intro x hx
    set s : ↥SK := eK.symm z with hs
    have hsc : ∀ y : ↥SK, y * s = s * y := by
      intro y
      apply eK.injective
      rw [map_mul, map_mul, hs, MulEquiv.apply_symm_apply]
      exact hz.1 (eK y)
    have hx' : x * (s : G) * x⁻¹ ∈ SK :=
      hS₁K _ (S₁.mul_mem (S₁.mul_mem hx (hSKS s.2)) (S₁.inv_mem hx)) (hKn x hx _ (hSKK s.2))
    let s' : ↥SK := ⟨x * (s : G) * x⁻¹, hx'⟩
    have hs'c : ∀ y : ↥SK, y * s' = s' * y := by
      intro y
      have hy' : x⁻¹ * (y : G) * x ∈ SK := by
        refine hS₁K _ (S₁.mul_mem (S₁.mul_mem (S₁.inv_mem hx) (hSKS y.2)) hx) ?_
        have := hKn x⁻¹ (S₁.inv_mem hx) y (hSKK y.2)
        simpa using this
      have h1 := hsc ⟨x⁻¹ * y * x, hy'⟩
      have h2 : (x⁻¹ * (y : G) * x) * (s : G) = (s : G) * (x⁻¹ * y * x) :=
        congrArg (fun w : ↥SK => (w : G)) h1
      apply Subtype.ext
      show (y : G) * (x * s * x⁻¹) = (x * s * x⁻¹) * y
      calc (y : G) * (x * s * x⁻¹) = x * ((x⁻¹ * y * x) * s) * x⁻¹ := by group
        _ = x * (s * (x⁻¹ * y * x)) * x⁻¹ := by rw [h2]
        _ = (x * s * x⁻¹) * y := by group
    have hs'2 : s' * s' = 1 := by
      apply Subtype.ext
      have h0 : (s : G) * s = 1 := by
        have h' : s * s = 1 := by rw [hs, ← map_mul, hz.2, map_one]
        simpa using congrArg (fun y : ↥SK => (y : G)) h'
      show (x * s * x⁻¹) * (x * s * x⁻¹) = 1
      calc (x * (s : G) * x⁻¹) * (x * s * x⁻¹) = x * (s * s) * x⁻¹ := by group
        _ = 1 := by rw [h0]; group
    have hcentral : ∀ w : SD16M, w * eK s' = eK s' * w := by
      intro w
      obtain ⟨y, rfl⟩ := eK.surjective w
      rw [← map_mul, ← map_mul, hs'c y]
    have hsq : eK s' * eK s' = 1 := by rw [← map_mul, hs'2, map_one]
    have key := sd16_central_involutions (eK s') z 1 hcentral hsq
      (fun w => hz.1 w) hz.2 (fun w => by simp) (by simp)
    rcases key with h | h | h
    ·
      have h' : s' = s := by
        apply eK.injective
        rw [h, hs, MulEquiv.apply_symm_apply]
      have h'' : x * (s : G) * x⁻¹ = s := congrArg (fun y : ↥SK => (y : G)) h'
      calc x * (s : G) = x * s * x⁻¹ * x := by group
        _ = s * x := by rw [h'']
    · exfalso
      have h1 : s' = 1 := eK.injective (by rw [h, map_one])
      have h2 : x * (s : G) * x⁻¹ = 1 := congrArg (fun y : ↥SK => (y : G)) h1
      have h3 : (s : G) = 1 := by
        have := congrArg (fun y => x⁻¹ * y * x) h2
        simpa [mul_assoc] using this
      apply hz1
      have h4 : s = 1 := Subtype.ext h3
      have := congrArg eK h4
      rw [hs, MulEquiv.apply_symm_apply, map_one] at this
      exact this
    · exact absurd h hz1

end CFSG.GH74.E2
