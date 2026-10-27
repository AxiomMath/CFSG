module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Shapes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    IsOmega5 L ∨ IsOmega6Plus L ∨ IsOmega6Minus L

theorem sec3SettingLB_of_component {G : Type} [Group G] [Finite G] {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {y : G} {Y : Subgroup G} (hy : orderOf y = 2)
    (hY : IsComponentIn Y (centralizer ({y} : Set G))) (hYF : InF Y) : Sec3SettingLB G y Y :=
  { toSec3Setting := { hS.toSec3Setting with involution := hy, component := hY, inF := hYF }
    lBalance := hS.lBalance
    kProper := hS.kProper
    notCat := hS.notCat }

end CFSG.OddStandard.SmallF3.Omega
