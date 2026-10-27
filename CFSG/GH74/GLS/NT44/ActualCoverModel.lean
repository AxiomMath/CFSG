module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open CFSG
open CFSG.GH74.GLS
open CFSG.LieType.Multipliers
open CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.GrSLit.L34Facts

noncomputable abbrev fullTwoCoverKernel : Subgroup L34.Cover :=
  Subgroup.normalClosure ({L34Facts.z₃} : Set L34.Cover)

noncomputable abbrev FullTwoCover : Type :=
  L34.Cover ⧸ fullTwoCoverKernel

@[expose] noncomputable def quotientMk : L34.Cover →* FullTwoCover :=
  QuotientGroup.mk' fullTwoCoverKernel

@[expose] noncomputable def sigmaS :
    L34.Cover →* CFSG.ComponentClassification.PSL3Four.S :=
  (MulEquiv.subgroupCongr L34Facts.range_sigma).toMonoidHom.comp
    L34Facts.sigma.rangeRestrict

private theorem sigmaS_z₃ :
    sigmaS L34Facts.z₃ = 1 := by
  apply Subtype.ext
  simpa only [sigmaS, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.subgroupCongr_apply, MonoidHom.coe_rangeRestrict, Subgroup.coe_one]
    using L34Facts.sigma_z₃

theorem normalClosure_z₃_le_sigmaS_ker :
    fullTwoCoverKernel ≤ sigmaS.ker := by
  have : sigmaS.ker.Normal := MonoidHom.normal_ker sigmaS
  change Subgroup.normalClosure ({L34Facts.z₃} : Set L34.Cover) ≤ sigmaS.ker
  refine Subgroup.normalClosure_le_normal ?_
  rw [Set.singleton_subset_iff]
  exact MonoidHom.mem_ker.mpr sigmaS_z₃

@[expose] noncomputable def fullTwoCoverToS :
    FullTwoCover →* CFSG.ComponentClassification.PSL3Four.S :=
  QuotientGroup.lift fullTwoCoverKernel sigmaS normalClosure_z₃_le_sigmaS_ker

theorem fullTwoCoverToS_comp_quotientMk :
    fullTwoCoverToS.comp quotientMk = sigmaS := by
  simpa only [fullTwoCoverToS, quotientMk] using
    (QuotientGroup.lift_comp_mk' fullTwoCoverKernel sigmaS
      normalClosure_z₃_le_sigmaS_ker)

end CFSG.GH74.GLS.NT44
