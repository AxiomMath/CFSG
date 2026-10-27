module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ComponentCases3
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ComponentSL3
import CFSG.LocalAnalysis.RankThreeTheoremC.OutTwoExponentThree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open
open CFSG.AGLEmbedding (KOutTwoGroup)

variable {G : Type} [Group G] [Finite G]

theorem D1ComponentAlphaData3.false_of_exp_three {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R : Subgroup G} {z : G} {Pbar : Sylow p (ReducedCentralizer p z)}
    {zbar : ReducedCentralizer p z} {K : Subgroup (ReducedCentralizer p z)}
    (h : D1ComponentAlphaData3 p P M H R z Pbar zbar K) (hp3 : p = 3) (hout : KOutTwoGroup K)
    (hexp : ∀ t ∈ (Pbar : Subgroup (ReducedCentralizer p z)) ⊓ K, t ^ p = 1) : False := by
  subst hp3
  have : K.Normal := h.data.normal
  obtain ⟨E, L, hER, -, hEexp, hEZ, e, hSL⟩ := h.data.exists_extraspecial
  exact false_of_outTwo_exponent_three Pbar hout hexp h.mem h.omega hER hEexp hEZ e hSL

end CFSG.LocalAnalysis.RankThreeTheoremC
