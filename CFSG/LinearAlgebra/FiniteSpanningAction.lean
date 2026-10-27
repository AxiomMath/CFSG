module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
public import Mathlib.LinearAlgebra.Span.Basic

public noncomputable section

open scoped Pointwise

namespace CFSG.Certificates

variable {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]

@[expose] def linearSetRestriction (X : Set V) :
    MulAction.stabilizer (V ≃ₗ[K] V) X →* Equiv.Perm X :=
  MulAction.toPermHom _ _

theorem linearSetRestriction_injective (X : Set V)
    (hspan : Submodule.span K X = ⊤) : Function.Injective (linearSetRestriction (K := K) X) := by
  intro f g h
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on hspan
  intro x hx
  exact congrArg (fun e : Equiv.Perm X => (e ⟨x, hx⟩ : V)) h

end CFSG.Certificates

namespace CFSG.LinearAlgebra

theorem finite_subgroup_of_preserves_spanning_set {R V : Type*} [Semiring R]
    [AddCommMonoid V] [Module R V] {S : Set V} (hS : S.Finite)
    (hspan : Submodule.span R S = ⊤) (Γ : Subgroup (V ≃ₗ[R] V))
    (hpres : ∀ g : Γ, Set.MapsTo (g : V ≃ₗ[R] V) S S) : Finite Γ := by
  let : Finite S := hS.to_subtype
  have hle : Γ ≤ MulAction.stabilizer (V ≃ₗ[R] V) S := by
    intro g hg
    exact (MulAction.mem_stabilizer_set' hS).mpr (hpres ⟨g, hg⟩)
  let ρ := (CFSG.Certificates.linearSetRestriction S).comp (Subgroup.inclusion hle)
  exact Finite.of_injective ρ ((CFSG.Certificates.linearSetRestriction_injective S hspan).comp
    (Subgroup.inclusion_injective hle))

theorem finite_range_of_preserves_spanning_set {R V G : Type*} [Semiring R]
    [AddCommMonoid V] [Module R V] [Group G] (ρ : G →* (V ≃ₗ[R] V)) {S : Set V}
    (hS : S.Finite) (hspan : Submodule.span R S = ⊤)
    (hpres : ∀ g : G, Set.MapsTo (ρ g) S S) : Finite ρ.range := by
  apply finite_subgroup_of_preserves_spanning_set hS hspan ρ.range
  rintro ⟨g, hgrange⟩
  obtain ⟨a, rfl⟩ := hgrange
  exact hpres a

end CFSG.LinearAlgebra
