module

public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ComponentClassification.CentralSylowImage

theorem central {G : Type*} [Group G]
    (ambient factor : Subgroup G) (hcontained : ambient ≤ factor) (sylow : Sylow 2 ambient)
    (hcentral : (sylow : Subgroup ambient).map ambient.subtype ≤ (Subgroup.center factor).map factor.subtype) :
    (sylow : Subgroup ambient) ≤ Subgroup.center ambient := by
  intro member hmember
  obtain ⟨lift, hlift, heq⟩ := Subgroup.mem_map.mp
    (hcentral (Subgroup.mem_map.mpr ⟨member, hmember, rfl⟩))
  apply Subgroup.mem_center_iff.mpr
  intro other
  apply Subtype.ext
  have hcommutes := congrArg Subtype.val
    (Subgroup.mem_center_iff.mp hlift (⟨other.val, hcontained other.property⟩ : factor))
  change other.val * lift.val = lift.val * other.val at hcommutes
  change lift.val = member.val at heq
  rwa [heq] at hcommutes

theorem unique {G : Type*} [Group G] [Finite G]
    (ambient factor : Subgroup G) (hcontained : ambient ≤ factor) (sylow : Sylow 2 ambient)
    (hcentral : (sylow : Subgroup ambient).map ambient.subtype ≤ (Subgroup.center factor).map factor.subtype) :
    ∀ other : Sylow 2 ambient, other = sylow := by
  have hcenter := central ambient factor hcontained sylow hcentral
  have hnormal : (sylow : Subgroup ambient).Normal := by
    constructor
    intro member hmember actor
    have hcommutes := Subgroup.mem_center_iff.mp (hcenter hmember) actor
    rw [hcommutes, mul_inv_cancel_right]
    exact hmember
  let : Unique (Sylow 2 ambient) := sylow.unique_of_normal hnormal
  intro other
  exact Subsingleton.elim other sylow

end CFSG.ComponentClassification.CentralSylowImage
