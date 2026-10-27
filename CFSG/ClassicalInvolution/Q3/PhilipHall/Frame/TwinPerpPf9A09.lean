module

import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF09
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf9Ctx8Frame
public import CFSG.ClassicalInvolution.Asc77.AscS24CGraph
public import CFSG.ClassicalInvolution.Asc77.AscS24CQuat
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf9A04

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace S24
open CFSG.ClassicalInvolution.Asc77.S24
section Ctx
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8F Ω K K' W S R R' z u)
include C in

theorem exists_caseI {c : G} (hcS : c ∈ (S : Subgroup G)) (hc2 : c * c = 1)
    (hinv : ∀ w ∈ W, c * w * c⁻¹ = w⁻¹) (hcr : c * C.D.F.ρ.r = C.D.F.ρ.r * c)
    (hin : InnerOn c R') :
    ∃ e ∈ (S : Subgroup G), e ∉ sZero Ω W S ∧ e * e = 1 ∧
      (∀ x ∈ (S : Subgroup G), x ∉ sZero Ω W S → e⁻¹ * x ∈ sZero Ω W S) ∧
      (∀ v ∈ R, v * e = e * v) ∧ (∀ v ∈ R', v * e = e * v) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.exists_caseI C.toFrame hcS hc2 hinv
    hcr hin
end Ctx

end S24
end Asc77

end

end CFSG.ClassicalInvolution.Q8P
