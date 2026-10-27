module


public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Continuity.Init
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.InvertedOddOrderDisplacementRank

open Module

theorem finrank_range_le {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (τ σ : V ≃ₗ[F] V) (p : ℕ) (hp : Odd p)
    (hτ : τ * τ = 1) (hσ : σ ^ p = 1) (hinv : τ * σ * τ = σ⁻¹) :
    finrank F (LinearMap.range ((σ : V →ₗ[F] V) - 1)) ≤
      2 * finrank F (LinearMap.range ((τ : V →ₗ[F] V) - 1)) := by
  obtain ⟨m, rfl⟩ := hp
  set ρ : V ≃ₗ[F] V := σ ^ (m + 1) with hρ
  have hσρ : ρ * ρ = σ := by
    rw [hρ, ← pow_add]
    have : m + 1 + (m + 1) = (2 * m + 1) + 1 := by omega
    rw [this, pow_succ, hσ, one_mul]
  have hτσ : τ * σ = σ⁻¹ * τ := by
    have := congrArg (· * τ) hinv
    simpa [mul_assoc, hτ] using this
  have hτρ : τ * ρ = ρ⁻¹ * τ := by
    have h1 : τ * σ ^ (m+1) = (σ⁻¹) ^ (m+1) * τ := by
      induction (m+1) with
      | zero => simp
      | succ n ih => rw [pow_succ, ← mul_assoc, ih, pow_succ, mul_assoc, mul_assoc, hτσ]
    rw [hρ, h1, inv_pow]
  have e1 : σ * τ * ρ = ρ * τ := by
    rw [mul_assoc, hτρ, ← hσρ]; simp [mul_assoc]
  set A : V →ₗ[F] V := ((σ * τ : V ≃ₗ[F] V) : V →ₗ[F] V) - 1 with hA
  set B : V →ₗ[F] V := (τ : V →ₗ[F] V) - 1 with hB
  have hcomp : A ∘ₗ (ρ : V →ₗ[F] V) = (ρ : V →ₗ[F] V) ∘ₗ B := by
    ext x
    have := LinearEquiv.congr_fun e1 x
    simp only [hA, hB, LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearEquiv.coe_coe, map_sub]
    simp only [LinearEquiv.mul_apply] at this ⊢
    rw [this]
  have hrank : finrank F (LinearMap.range A) = finrank F (LinearMap.range B) := by
    have h1 : LinearMap.range (A ∘ₗ (ρ : V →ₗ[F] V)) = LinearMap.range A :=
      LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range ρ)
    have h2 : LinearMap.range ((ρ : V →ₗ[F] V) ∘ₗ B) =
        (LinearMap.range B).map (ρ : V →ₗ[F] V) := LinearMap.range_comp _ _
    rw [← h1, hcomp, h2]
    exact LinearEquiv.finrank_map_eq ρ _
  have hsplit : (σ : V →ₗ[F] V) - 1 = A ∘ₗ (τ : V →ₗ[F] V) + B := by
    ext x
    have hh : τ (τ x) = x := LinearEquiv.congr_fun hτ x
    simp only [hA, hB, LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearEquiv.coe_coe, LinearMap.add_apply, LinearEquiv.mul_apply, hh]
    abel
  have hAτ : finrank F (LinearMap.range (A ∘ₗ (τ : V →ₗ[F] V))) = finrank F (LinearMap.range A) := by
    rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range τ)]
  rw [hsplit]
  have hsub : LinearMap.range (A ∘ₗ (τ : V →ₗ[F] V) + B) ≤
      LinearMap.range (A ∘ₗ (τ : V →ₗ[F] V)) ⊔ LinearMap.range B := by
    rintro _ ⟨x, rfl⟩
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  calc _ ≤ finrank F ↥(LinearMap.range (A ∘ₗ (τ : V →ₗ[F] V)) ⊔ LinearMap.range B) :=
        Submodule.finrank_mono hsub
    _ ≤ finrank F (LinearMap.range (A ∘ₗ (τ : V →ₗ[F] V))) + finrank F (LinearMap.range B) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ = _ := by rw [hAτ, hrank]; ring

end CFSG.GroupTheory.CoprimeActionSupport.InvertedOddOrderDisplacementRank
