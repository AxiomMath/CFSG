module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneTrivialOn
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneUnitary
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialFamilies
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicBase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.AGLEmbedding
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial

private theorem smallRankOneData_of_unitaryIndex {K : Type} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d)
    (hK : Nonempty (K ≃* CatGroup d)) (T : Sylow p K) : SmallRankOneData p K T := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨he⟩ := hK
  obtain ⟨-, hf, hq, F, _, _, J, hJ, hF, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd ⟨he⟩)
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hF hfix hf
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e T S
  exact SmallRankOneData.of_equiv e' he'
    (UnitaryModel.smallRankOneData_psu J hJ hF hfix hq S hS hd ⟨e'.symm.trans he⟩)

theorem signalizerThreeUnitary_holds : SignalizerThreeUnitary := by
  intro p hp hp5 q d hqp hd K _ _ hK
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  refine signalizerThreeOn_of_signalizerTrivialOn hp (by omega) fun P W hW hnorm => ?_
  have hdU : IsUnitaryIndex p d := ⟨q, hqp, hd⟩
  have D := smallRankOneData_of_unitaryIndex hp hdU hK P
  obtain ⟨hcard, -, hexp, -⟩ := kFactUnitarySylowStructure K p d hp2 hdU hK P
  obtain ⟨q', -, -, hfe, hq'⟩ := hdU.exists_eq
  have hn : 2 ≤ 3 * d.1.fieldExponent := by
    rw [hfe]
    omega
  exact signalizer_eq_bot_of_ti_planes hp P D.center D.ti D.inner
    (le_iSup_planes_of_card _ hn hcard hexp) W hW hnorm

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
