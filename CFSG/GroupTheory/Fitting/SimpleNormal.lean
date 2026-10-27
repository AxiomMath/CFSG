module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GroupTheory

open CFSG

variable {G : Type*} [Group G] [Finite G]

theorem generalizedFitting_le_of_normal (hS : IsSimpleGroup ↥(generalizedFitting G))
    {N : Subgroup G} (hN : N.Normal) (hN1 : N ≠ ⊥) : generalizedFitting G ≤ N := by
  haveI := hN
  haveI : (generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  rcases hS.eq_bot_or_eq_top_of_normal ((N ⊓ generalizedFitting G).subgroupOf _) with
    hbot | htop
  · have hinf : N ⊓ generalizedFitting G = ⊥ := by
      simpa [inf_assoc] using disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hbot)
    have hcomm : ⁅N, generalizedFitting G⁆ = ⊥ :=
      le_bot_iff.mp ((Subgroup.commutator_le_inf N _).trans_eq hinf)
    have hle : N ≤ generalizedFitting G :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
        (centralizer_generalizedFitting_le G)
    exact absurd (le_bot_iff.mp ((le_inf le_rfl hle).trans_eq hinf)) hN1
  · exact (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_left

end CFSG.GroupTheory
