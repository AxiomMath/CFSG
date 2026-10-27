module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigSecSound
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalTransport
public import Certificates.Certificate40346
public import CFSG.Sporadic.Bridge.J4Surj

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Blueprint CFSG.SectionRank

theorem secW_J4_7 : SecW NativeSporadic.J4 7 :=
  SClaim.secW_of_check (spec2 112) NativeSporadic.J4Seed1 NativeSporadic.J4Seed2 j4_7_claims
    Certificates.certificate40346

theorem row_J4_7 :
    KFactSporLocalRow .J4 7 := by
  apply row_of_model
  intro G _ _ ⟨e⟩ hp _ K z hz hK hzK hN hcl _ _
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have f : NativeSporadic.J4 ≃* G := b.trans e.symm
  have hW : SecW G 7 :=
    @SecW.of_mulEquiv NativeSporadic.J4 G inferInstance inferInstance f 7 secW_J4_7
  have hcard : Nat.card G = 86775571046077562880 := by
    rw [Nat.card_congr (e.trans b.symm).toEquiv]
    exact CFSG.Sporadic.J4.card_J4
  exact ⟨kxSection_of_secW hp (by rw [hcard]; norm_num) hW hz hzK hN hcl, by decide⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
