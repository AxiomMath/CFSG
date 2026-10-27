module

public import CFSG.Foundations.KCoreOpen
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGenericCatalog

public section

namespace CFSG

open CFSG.Open

theorem isCatalogGroup_of_isComponentOf {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.IsKGroup X) {K : Subgroup X} (hK : CFSG.Open.IsComponentOf K ⊤) :
    IsCatalogGroup (↥K ⧸ Subgroup.center ↥K) :=
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance.inCatalog_quotient_center_of_kgroup hK.2.2
    (CFSG.Open.IsKGroup.subgroup hX K)

end CFSG
