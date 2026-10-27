module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasicAux
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open CFSG.AGLEmbedding (blockV)
open Module

section Dual

variable {A U : Type*} [Group A] [AddCommGroup U] [Module (ZMod 2) U]

theorem span_eq_top_of_no_invariant (ρ : A →* (U ≃ₗ[ZMod 2] U))
    (hno : ∀ ψ : U →ₗ[ZMod 2] ZMod 2,
      (∀ a, ψ.comp (ρ a⁻¹ : U →ₗ[ZMod 2] U) = ψ) → ψ = 0) :
    Submodule.span (ZMod 2) {x : U | ∃ a u, x = ρ a u - u} = ⊤ := by
  by_contra hne
  have hlt : Submodule.span (ZMod 2) {x : U | ∃ a u, x = ρ a u - u} < ⊤ :=
    lt_top_iff_ne_top.2 hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  apply hf0
  apply hno
  intro a
  ext u
  have h0 : f (ρ a⁻¹ u - u) = 0 :=
    LinearMap.mem_ker.1 (hle (Submodule.subset_span ⟨a⁻¹, u, rfl⟩))
  have h1 : f (ρ a⁻¹ u) = f u := sub_eq_zero.1 (by rwa [map_sub] at h0)
  simpa using h1

end Dual

end CFSG.HardMathSupport.Cooperstein.Proving

end
