module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMSecSound
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalTransport
public import CFSG.Sporadic.Presentation.McLExact
public import CFSG.Sporadic.Bridge.Co3Surj
public import CFSG.Sporadic.Bridge.SuzSurj
public import Certificates.Certificate40262

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Blueprint CFSG.SectionRank

theorem secW_McL_7 : SecW NativeSporadic.McL 7 :=
  MSec.secW_of_check (spec3 21) mcl_7_claims Certificates.certificate40262.1

theorem secW_Co3_11 : SecW NativeSporadic.Co3 11 :=
  MSec.secW_of_check (spec2 22) co3_11_claims Certificates.certificate40262.2.1

theorem secW_Suz_7 : SecW NativeSporadic.Suz 7 :=
  MSec.secW_of_check (spec3 64) suz_7_claims Certificates.certificate40262.2.2

theorem row_McL_7 :
    KFactSporLocalRow .McL 7 := by
  apply row_of_model
  intro G _ _ ⟨e⟩ hp _ K z hz hK hzK hN hcl _ _
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  have f : NativeSporadic.McL ≃* G := b.trans e.symm
  have hW : SecW G 7 :=
    @SecW.of_mulEquiv NativeSporadic.McL G inferInstance inferInstance f 7 secW_McL_7
  have hcard : Nat.card G = 898128000 := by
    rw [Nat.card_congr (e.trans b.symm).toEquiv]
    exact CFSG.Sporadic.McL.card_McL
  exact ⟨kxSection_of_secW hp (by rw [hcard]; norm_num) hW hz hzK hN hcl, by decide⟩

theorem row_Co3_11 :
    KFactSporLocalRow .Co3 11 := by
  apply row_of_model
  intro G _ _ ⟨e⟩ hp _ K z hz hK hzK hN hcl _ _
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
  have f : NativeSporadic.Co3 ≃* G := b.trans e.symm
  have hW : SecW G 11 :=
    @SecW.of_mulEquiv NativeSporadic.Co3 G inferInstance inferInstance f 11 secW_Co3_11
  have hcard : Nat.card G = 495766656000 := by
    rw [Nat.card_congr (e.trans b.symm).toEquiv]
    exact CFSG.Sporadic.Co3.card_Co3
  exact ⟨kxSection_of_secW hp (by rw [hcard]; norm_num) hW hz hzK hN hcl, by decide⟩

theorem row_Suz_7 :
    KFactSporLocalRow .Suz 7 := by
  apply row_of_model
  intro G _ _ ⟨e⟩ hp _ K z hz hK hzK hN hcl _ _
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  have f : NativeSporadic.Suz ≃* G := b.trans e.symm
  have hW : SecW G 7 :=
    @SecW.of_mulEquiv NativeSporadic.Suz G inferInstance inferInstance f 7 secW_Suz_7
  have hcard : Nat.card G = 448345497600 := by
    rw [Nat.card_congr (e.trans b.symm).toEquiv]
    exact CFSG.Sporadic.Suz.card_Suz
  exact ⟨kxSection_of_secW hp (by rw [hcard]; norm_num) hW hz hzK hN hcl, by decide⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
