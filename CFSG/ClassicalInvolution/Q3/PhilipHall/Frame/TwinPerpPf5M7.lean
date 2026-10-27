module

public import CFSG.ClassicalInvolution.Q3.Q3T7F25M7
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M3

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false
namespace CFSG.ClassicalInvolution.Q8P

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
namespace T7T
open CFSG.ClassicalInvolution.Asc77.T7T
variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)}
    {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
in
theorem exists_hyp25T (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) :
    ∃ t' : G, T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t' := by
  obtain ⟨t', hT⟩ := CFSG.ClassicalInvolution.T7F25.Asc77.T7T.exists_hyp25T hyp.toF
  exact ⟨t', hyp, hT.ht'S, hT.ht'2, hT.ht'R⟩
end T7T
end Asc77
end
end CFSG.ClassicalInvolution.Q8P
