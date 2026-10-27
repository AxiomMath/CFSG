module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Split
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Facts
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Layer
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Comp
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Dich
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Rank
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Index
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64Chain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6ShapesDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Outside
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Statements

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Case64E8_of (h33 : Asc82Lemma33) (h61 : Asc82Lemma61) (h63 : Asc82Lemma63)
    (hsh : Asc82Shapes) (hout : Asc82Outside) (hCh : Asc82AutCentChain3)
    (hF1 : Asc82E8LayerFact) (hF2 : Asc82AutCentOmega5) : Asc82Case64E8 := by
  apply asc82Case64E8_of_G
  intro G _ _ t L hset hyp y X Y T hy hXC hXF hX29 hYc hXY hYC hYF hY6 hT hyT hab h8 h2 hne
  have c : M6E8Ctx t L y X Y T :=
    ⟨hset, hyp, hy, hXC, hXF, hX29, hYc, hXY, hYC, hYF, hY6, hT, hyT, hab, h8, h2, hne⟩
  obtain ⟨r, d⟩ := m6e8_exists_datum h63 hF1 c
  obtain ⟨I, hI, hJI, hIF⟩ := m6e8_exists_I h63 d
  rcases m6e8_dichotomy h61 h63 hsh d hI hJI hIF with hIJ | ⟨hI6, hyI⟩
  · right
    have hnorm : ∀ c' ∈ centralizer ({r} : Set G), c' ∈ normalizer (layerCent Y r : Set G) := by
      intro c' hc'
      rw [← hIJ]
      exact sec64_mem_normalizer h63 d.setting d.hyp62 d.orderOf_r hI (Or.inl hIF) hc'
    obtain ⟨K, hK, hyK, hrK, hKi, hKR⟩ := m6e8_index hF2 d hnorm
    exact ⟨r, d.mem_R, d.not_mem, d.card_gt, K, hK, hyK, hrK, hKi, hKR⟩
  · left
    exact m6e8_rank_of_u43 h33 h63 hsh hout hCh d hI hJI hIF hI6 hyI

end CFSG.OddStandard.SmallF3.Omega
