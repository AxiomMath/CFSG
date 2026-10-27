module

public import CFSG.LargeExtraspecial.GLRFusConfig
public import CFSG.LargeExtraspecial.GLRElimMain

public section

namespace CFSG.LargeExtraspecial.Setting

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {S : Setting G}

theorem not_s12GammaLResidual {g : G} {t : S.O} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (h5 : 5 ≤ S.width) : ¬ S.S12GammaLResidual g t := fun hR =>
  (GLR.nonempty_config haQ hne hR h5).elim fun C => GLR.false_of_config C h5

end CFSG.LargeExtraspecial.Setting
