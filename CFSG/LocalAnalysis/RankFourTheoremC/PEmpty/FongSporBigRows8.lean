module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigSecSound
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalTransport
public import Certificates.Certificate40347
public import CFSG.Sporadic.Bridge.HNSurj

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Blueprint CFSG.SectionRank

theorem secW_HN_11 : SecW NativeSporadic.HN 11 :=
  SClaim.secW_of_check (specP 5 133) NativeSporadic.HNSeed1 NativeSporadic.HNSeed2 hn_11_claims
    Certificates.certificate40347

theorem row_HN_11 :
    KFactSporLocalRow .HN 11 := by
  apply row_of_model
  intro G _ _ ⟨e⟩ hp _ K z hz hK hzK hN hcl _ _
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  have f : NativeSporadic.HN ≃* G := b.trans e.symm
  have hW : SecW G 11 :=
    @SecW.of_mulEquiv NativeSporadic.HN G inferInstance inferInstance f 11 secW_HN_11
  have hcard : Nat.card G = 273030912000000 := by
    rw [Nat.card_congr (e.trans b.symm).toEquiv]
    exact CFSG.Sporadic.HN.card_HN
  exact ⟨kxSection_of_secW hp (by rw [hcard]; norm_num) hW hz hzK hN hcl, by decide⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
