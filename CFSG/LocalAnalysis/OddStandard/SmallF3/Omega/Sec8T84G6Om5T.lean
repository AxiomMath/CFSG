module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G6Om5TSet
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84GTab

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec8t84g_om5Tab : Sec8T84FactOm5Tab := by
  intro G _ _ K hK t ht2 htK A hA hL
  obtain ⟨V, _, _, _, Q, hQ, hdim, hσ, ⟨e⟩⟩ := ff_isOmegaStar_center_five hK
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h
  obtain ⟨u, hu, huu, hu1, hin⟩ := sec8t84g6t_reduce hQ hdim hσ hK e htt htK hA hL
  exact ⟨u, hu, orderOf_eq_prime (by rwa [pow_two]) hu1, hin⟩

end CFSG.OddStandard.SmallF3.Omega
