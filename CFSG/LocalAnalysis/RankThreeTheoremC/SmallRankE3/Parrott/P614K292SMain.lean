module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsCase
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292SPlane
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292SInner

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
open P614K292 P614K292S


theorem kD292Shape3_holds : KD292Shape3 := by
  intro hT X _ _ L x Px B cfg
  have h := cfg.setup
  haveI : L.Normal := h.normal
  obtain ⟨hcyc, hΩ, hLε, hZ3⟩ := core_facts hT cfg
  obtain ⟨π, p, f, K, _, ν, M⟩ := exists_lModel h.comp.2.2 hLε (dvd_of_eq hZ3)
  have hinj : Function.Injective ν := by
    rcases M.cases with hinj | ⟨hZ, -⟩
    · exact hinj
    · rw [hZ, Subgroup.card_bot] at hZ3
      omega
  obtain ⟨y, hy, hT3⟩ := M.exists_isTypeThree h (dvd_of_eq hZ3)
  have hcent := centralizer_eq_pCore cfg hcyc hΩ
  obtain ⟨hplane, hB9⟩ := plane_eq cfg hZ3
  have hxB : x ∈ B := by
    rw [hplane]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  exact ⟨π, p, f, K, inferInstance, ν, y, M, hinj, hy, hT3, hcent, hplane,
    isSCp_of_card cfg hxB hB9, fun t ht c hc => mem_of_isLiftAt_two M hcent ht hc,
    fun g g' => exists_isLiftAt_commutator M g g'⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
