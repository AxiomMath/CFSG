module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Setting2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.ClassS

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

structure EndData (G : Type) [Group G] [Finite G] (x : G) (Y : Subgroup G) : Prop where
  setting : HSetting G
  ox : orderOf x = 2
  comp : Omega.IsComponentIn Y (centralizer ({x} : Set G))
  standard : CFSG.Open.standardComponentIsStandard Y
  inS : InS (↥Y ⧸ center ↥Y)

namespace EndData

variable {G : Type} [Group G] [Finite G] {x : G} {Y : Subgroup G}

theorem isQuasisimple (h : EndData G x Y) : IsQuasisimple ↥Y := by
  exact CFSG.IsQuasisimple.of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe h.comp.1).symm h.comp.2.1

theorem oddCore_eq_bot (h : EndData G x Y) : oddCore ↥Y = ⊥ := by
  exact oddCore_eq_bot_of_isComponentIn (h.setting.balanced x h.ox) h.comp

theorem isPGroup_center (h : EndData G x Y) : IsPGroup 2 ↥(center ↥Y) := by
  exact isPGroup_two_center_of_isComponentIn (h.setting.balanced x h.ox) h.comp

theorem standardSetting (h : EndData G x Y) : CFSG.OddStandard.StandardSetting G Y := by
  exact ⟨h.setting.simple, h.setting.nonab, h.setting.kProper, h.standard⟩

theorem balanced_open (h : EndData G x Y) :
    ∀ t : G, orderOf t = 2 →
      CFSG.Open.standardComponentOddCore (Subgroup.centralizer ({t} : Set G)) = ⊥ := by
  exact fun t ht => h.setting.balanced t ht

end EndData

end CFSG.OddStandard.SmallF3.HypA2
