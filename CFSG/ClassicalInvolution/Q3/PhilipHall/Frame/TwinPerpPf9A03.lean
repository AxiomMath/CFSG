module

import CFSG.ClassicalInvolution.Q3.Q3T7P24EngA
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M1

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7E
open CFSG.ClassicalInvolution.Asc77.T7E
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem involution_cases {K K' : Subgroup G} {z : G} (hs : Hyp23Setting Ω K K' z)
    {S : Sylow 2 G} {R R' : Subgroup G} (hR : IsSylow2In R K) (hR' : IsSylow2In R' K')
    (hRS : R ≤ (S : Subgroup G)) (hR'S : R' ≤ (S : Subgroup G)) {b b' u : G} (hb : b ∈ R)
    (hb' : b' ∈ R') (ob : orderOf b = 4) (ob' : orderOf b' = 4) (huK : u ∈ K ⊔ K')
    (huS : u ∈ (S : Subgroup G)) (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ z)
    (hub : u * b = b * u) (hub' : u * b' = b' * u) : u = b * b' ∨ u = z * (b * b') := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7E.involution_cases_of hs.stand.hyp hs.stand.mem hs.hK' hs.hne hs.hz hR hR' hRS
    hR'S hb hb' ob ob' huK huS hu2 hu1 huz hub hub'
end T7E
end Asc77

end

end CFSG.ClassicalInvolution.Q8P
