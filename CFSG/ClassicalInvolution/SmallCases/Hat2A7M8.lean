module

public import CFSG.ClassicalInvolution.Q3.Q3T7F25M8
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7M3

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false
namespace CFSG.ClassicalInvolution.Hat2A7M
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace C25V
open CFSG.ClassicalInvolution.Asc77.C25V
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement
section Main
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
theorem exists_comm_swap_of_ff (h11 : C25_11) (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF : IsFAut R a)
    (hF' : IsFAut R' a) :
    ∃ t' g : G, T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t' ∧ g * z * g⁻¹ = t' ∧
      (¬ ∃ y : G, y * z * y⁻¹ = t' * z) ∧ a * t' = t' * a := by
  obtain ⟨t', g, hT, h1⟩ := CFSG.ClassicalInvolution.T7F25.Asc77.C25V.exists_comm_swap_of_ff
    (h11 G Ω K K' W S R R' z t u₁ u₂ hyp) hyp.toF haS ha2 hF hF'
  exact ⟨t', g, ⟨hyp, hT.ht'S, hT.ht'2, hT.ht'R⟩, h1⟩
theorem false_of_zStar_ff (h11 : C25_11) (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF : IsFAut R a)
    (hF' : IsFAut R' a) (hZ : z ∈ zStarOf (Subgroup.centralizer ({a} : Set G))) : False :=
  CFSG.ClassicalInvolution.T7F25.Asc77.C25V.false_of_zStar_ff (h11 G Ω K K' W S R R' z t u₁ u₂ hyp)
    hyp.toF haS ha2 hF hF' hZ
end Main
end C25V
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace C25V
open CFSG.ClassicalInvolution.Asc77.C25V
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement
section Main
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ : G}
theorem exists_ff_of_inner (h11 : C25_11) (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF' : IsFAut R' a)
    (hin : ∃ r ∈ R, ∀ x ∈ R, (r⁻¹ * a) * x = x * (r⁻¹ * a)) :
    ∃ e ∈ (S : Subgroup G), e * e = 1 ∧ IsFAut R e ∧ IsFAut R' e :=
  CFSG.ClassicalInvolution.T7F25.Asc77.C25V.exists_ff_of_inner
    (h11 G Ω K K' W S R R' z t u₁ u₂ hyp) hyp.toF haS ha2 hF' hin
end Main
end C25V
end Asc77
end
end CFSG.ClassicalInvolution.Hat2A7M
