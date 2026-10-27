module

public import CFSG.LieType.AlgebraicGroups.CentralizerInvolutionTangent
public import CFSG.LieType.AlgebraicGroups.AdjointTangentAction
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

open scoped CFSG.ConvolutionPoints

public section

namespace CFSG.LieType.AlgebraicGroups

open WithConv

variable {k : Type} [Field k] [IsAlgClosed k] {A : Type} [CommRing A] [HopfAlgebra k A]
  [Algebra.FiniteType k A]

theorem mem_adFixedTangent_iff (M : Subgroup (WithConv (A →ₐ[k] k)))
    {S : Set (WithConv (A →ₐ[k] k))} (hS : S ⊆ M)
    (D : TangentSpace k (A ⧸ subgroupIdeal M) (Bialgebra.counitAlgHom k _)) :
    D ∈ adFixedTangent M S ↔ ∀ g (hg : g ∈ S), adTangent M (hS hg) D = D := by
  constructor
  · intro hD g hg
    refine Subtype.ext (LinearMap.ext fun q => ?_)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [adTangent_apply]
    exact hD g hg a
  · intro hD g hg a
    rw [← adTangent_apply M (hS hg) D a, hD g hg]

theorem adFixedTangent_singleton (M : Subgroup (WithConv (A →ₐ[k] k)))
    {g : WithConv (A →ₐ[k] k)} (hg : g ∈ M) :
    adFixedTangent M {g} = LinearMap.ker (adTangent M hg - 1) := by
  ext D
  rw [mem_adFixedTangent_iff M (Set.singleton_subset_iff.2 hg), LinearMap.mem_ker,
    LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  constructor
  · intro h
    exact h g rfl
  · rintro h g' rfl
    exact h

theorem adFixedTangent_pair_eq (M : Subgroup (WithConv (A →ₐ[k] k)))
    {g₁ g₂ : WithConv (A →ₐ[k] k)} (h₁ : g₁ ∈ M) (h₂ : g₂ ∈ M) :
    adFixedTangent M {g₁, g₂} =
      LinearMap.ker (adTangent M h₁ - 1) ⊓ LinearMap.ker (adTangent M h₂ - 1) := by
  ext D
  rw [Submodule.mem_inf, ← adFixedTangent_singleton M h₁, ← adFixedTangent_singleton M h₂]
  constructor
  · intro h
    refine ⟨fun g hg a => ?_, fun g hg a => ?_⟩
    · rw [Set.mem_singleton_iff.1 hg]
      exact h g₁ (Set.mem_insert _ _) a
    · rw [Set.mem_singleton_iff.1 hg]
      exact h g₂ (Set.mem_insert_of_mem _ rfl) a
  · rintro ⟨h1, h2⟩ g hg a
    rcases hg with rfl | rfl
    · exact h1 _ rfl a
    · exact h2 _ rfl a

end CFSG.LieType.AlgebraicGroups

end
