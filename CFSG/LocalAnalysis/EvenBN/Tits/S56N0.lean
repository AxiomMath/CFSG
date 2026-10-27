module

public import CFSG.Yardstones.M41b0c98b3153.Definitions
import all CFSG.Yardstones.M41b0c98b3153.Definitions

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup

namespace Data

variable {G : Type} [Group G] [Finite G]

theorem s56P0_def (d : Data G) : d.s56P0 = (CFSG.pCore 2 ↥d.N).map d.N.subtype := by
  simp only [s56P0]

theorem s56P_def (d : Data G) : d.s56P = d.s56P0 ⊓ centralizer (d.F : Set G) := by
  simp only [s56P]

theorem s56U11_def (d : Data G) : d.s56U11 = closure ({d.pv 11, d.pv 12} : Set G) := by
  simp only [s56U11]

theorem s56U10_def (d : Data G) : d.s56U10 = d.s56U11 ⊔ zpowers (d.pv 10) := by
  simp only [s56U10]

theorem s56P10_def (d : Data G) : d.s56P10 = d.s56P0 ⊓ centralizer (d.s56U10 : Set G) := by
  simp only [s56P10]

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
