module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldNormalize
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviBaseChange

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore)

local instance e6PilotFieldNormalizeExistsNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Models

variable (K : Type) [Field K]

@[expose] noncomputable def neighbourLeviEquiv (N : E6Neighbour) : ↥(a5Levi K) ≃* ↥(N.levi K) :=
  ((MulAut.conj (N.rep K)).subgroupMap (a5Levi K)).trans
    (MulEquiv.subgroupCongr (map_conj_rep_a5Levi N))

variable {K}

theorem coe_neighbourLeviEquiv (N : E6Neighbour) (g : a5Levi K) :
    (((neighbourLeviEquiv K N g : N.levi K) : adjointGroup .E6 K) : ModGL .E6 K) =
      (N.rep K : ModGL .E6 K) * ((g : adjointGroup .E6 K) : ModGL .E6 K) *
        (N.rep K : ModGL .E6 K)⁻¹ :=
  rfl

theorem baseChangeGL_weylElt_one_E6 {k : Type} [Field k] (ι : k →+* K) (i : Fin (Tag.rank .E6)) :
    baseChangeGL ι (weylElt .E6 k i 1) = weylElt .E6 K i 1 := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, map_mul, map_mul, baseChangeGL_xUnit,
    baseChangeGL_yUnit, CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  simp

theorem baseChangeGL_rep {k : Type} [Field k] (ι : k →+* K) (N : E6Neighbour) :
    baseChangeGL ι (N.rep k : ModGL .E6 k) = (N.rep K : ModGL .E6 K) := by
  rw [E6Neighbour.coe_rep, E6Neighbour.coe_rep, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => baseChangeGL_weylElt_one_E6 ι i

theorem leviBaseChange_neighbourLeviEquiv {k : Type} [Field k] (ι : k →+* K) (N : E6Neighbour)
    (g : a5Levi k) :
    leviBaseChange ι N (neighbourLeviEquiv k N g) =
      neighbourLeviEquiv K N (a5LeviBaseChange ι g) := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [coe_leviBaseChange, coe_neighbourLeviEquiv, coe_neighbourLeviEquiv, map_mul, map_mul, map_inv,
    baseChangeGL_rep, coe_a5LeviBaseChange]

end Models

end CFSG.SeitzReduction.E6Pilot
