module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.CentralOmega.Alt
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.CentralOmega.M22
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.CentralOmega.Onan
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.CentralOmega.Linear
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TripleCoverWide
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3ResCenter
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3ResSL3Model

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.CentralOmega

theorem centralOmegaReduced_of_tables (hGA : CFSG.Open.GriessAllModelsStatement)
    (hAlt : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) :
    CentralOmegaReduced := by
  intro L _ _ hq hcat hne hZp hrk S
  obtain ⟨hcyc, hc⟩ :=
    KFactProofs.Stroth.Bal3.bal3ThreeCenter_of_tables hGA hAlt hSpor L hq hcat hne hZp hrk
  rcases KFactProofs.Stroth.TripleCover.kFactAlphaListM3Wide_of_tables hGA hSpor L hq hcat hne
      hZp hcyc hrk with he | he | he | he | ⟨d, hd, he⟩
  · obtain ⟨e⟩ := he
    exact not_forall_commute_alt hq hc (by norm_num) (by norm_num) e S
  · obtain ⟨e⟩ := he
    exact not_forall_commute_alt hq hc (by norm_num) (by norm_num) e S
  · obtain ⟨e⟩ := he
    exact not_forall_commute_m22 hq hc e S
  · obtain ⟨e⟩ := he
    exact not_forall_commute_onan hq hc e S
  · exact not_forall_commute_of_isSLThreePi
      (KFactProofs.Stroth.Bal3.isSLThreePi_of_cover hGA hq hc ⟨d, hd, he⟩) S

end CFSG.LocalAnalysis.RankThreeTheoremC.CentralOmega
