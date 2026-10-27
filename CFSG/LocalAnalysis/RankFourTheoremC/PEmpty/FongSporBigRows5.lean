module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigGenSound
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalTransport
public import Certificates.Certificate40345
public import CFSG.Sporadic.Bridge.HNSurj

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Blueprint CFSG.SectionRank

theorem genW_HN_7 : GenW NativeSporadic.HN 7 :=
  GClaim.genW_of_check (specP 5 133) NativeSporadic.HNSeed1 NativeSporadic.HNSeed2 hn_7_claims
    Certificates.certificate40345

theorem row_HN_7 :
    KFactSporLocalRow .HN 7 := by
  apply row_of_model
  intro G _ _ ⟨e⟩ hp _ K z hz hK hzK hN hcl _ _
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  have f : NativeSporadic.HN ≃* G := b.trans e.symm
  have hW : GenW G 7 :=
    @GenW.of_mulEquiv NativeSporadic.HN G inferInstance inferInstance f 7 genW_HN_7
  have hcard : Nat.card G = 273030912000000 := by
    rw [Nat.card_congr (e.trans b.symm).toEquiv]
    exact CFSG.Sporadic.HN.card_HN
  exact (false_of_genW hp (by rw [hcard]; norm_num) hW hz hzK hN hcl hK).elim

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
