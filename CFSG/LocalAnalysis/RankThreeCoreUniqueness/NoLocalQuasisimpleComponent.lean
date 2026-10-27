module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
public import CFSG.Assembly.Defs

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem quasisimple_pCore_le_center
    {G : Type*} [Group G] [Finite G] (hquasisimple : IsQuasisimple G)
    (prime : ℕ) (hprime : prime.Prime) : pCore prime G ≤ Subgroup.center G := by
  let : Group.IsPerfect G := Group.isPerfect_def.mpr hquasisimple.1
  let : IsSimpleGroup (G ⧸ Subgroup.center G) := hquasisimple.2
  let : Fact prime.Prime := ⟨hprime⟩
  let quotientMap := QuotientGroup.mk' (Subgroup.center G)
  let imageCore := Subgroup.map quotientMap (pCore prime G)
  have himageNormal : imageCore.Normal :=
    (pCore_normal prime).map quotientMap (QuotientGroup.mk'_surjective _)
  have himageGroup : IsPGroup prime imageCore := (pCore_isPGroup prime).map quotientMap
  have himageBottom : imageCore = ⊥ := by
    rcases CFSG.eq_bot_or_eq_top_of_normal imageCore himageNormal with hbottom | htop
    · exact hbottom
    · have hquotientGroup : IsPGroup prime (G ⧸ Subgroup.center G) :=
        himageGroup.of_equiv ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
      exact False.elim (Group.IsPerfect.not_isNilpotent (G ⧸ Subgroup.center G)
        hquotientGroup.isNilpotent)
  intro element helement
  have hkernel : element ∈ quotientMap.ker :=
    Subgroup.mem_bot.mp (himageBottom ▸ Subgroup.mem_map_of_mem quotientMap helement)
  rwa [QuotientGroup.ker_mk'] at hkernel

end CFSG.RankThreeCoreUniqueness.Helpers
