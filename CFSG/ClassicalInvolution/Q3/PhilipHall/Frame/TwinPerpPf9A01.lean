module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M0
public import CFSG.ClassicalInvolution.Q3.Q3T7P24A01

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem conj_mem_MGrp [Finite G] (hΩ : HypOmegaMod Ω) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) {x : G} (hx : x ∈ MGrp Ω W) :
    g * x * g⁻¹ ∈ MGrp Ω W :=
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Thompson.conj_mem_MGrp hΩ hg hx

end Thompson
end Asc77

end

end CFSG.ClassicalInvolution.Q8P
