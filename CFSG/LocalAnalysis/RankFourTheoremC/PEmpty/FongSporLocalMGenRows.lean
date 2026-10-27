module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMGenSound
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalTransport
public import CFSG.Sporadic.Bridge.J3Surj
public import CFSG.Sporadic.Bridge.Co3Surj
public import CFSG.Sporadic.Presentation.Co2Exact
public import Certificates.Certificate40261

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Blueprint CFSG.SectionRank

theorem genW_J3_5 : GenW NativeSporadic.J3 5 :=
  MGen.genW_of_check (spec2 80) NativeSporadic.J3Seed1 NativeSporadic.J3Seed2 j3_5_claims
    Certificates.certificate40261.1

theorem genW_Co3_7 : GenW NativeSporadic.Co3 7 :=
  MGen.genW_of_check (spec2 22) NativeSporadic.Co3Seed1 NativeSporadic.Co3Seed2 co3_7_claims
    Certificates.certificate40261.2.1

theorem genW_Co2_7 : GenW NativeSporadic.Co2 7 :=
  MGen.genW_of_check (spec2 22) NativeSporadic.Co2Seed1 NativeSporadic.Co2Seed2 co2_7_claims
    Certificates.certificate40261.2.2

theorem row_J3_5 :
    KFactSporLocalRow .J3 5 := by
  apply row_of_model
  intro G _ _ ⟨e⟩ hp _ K z hz hK hzK hN hcl _ _
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  have f : NativeSporadic.J3 ≃* G := b.trans e.symm
  have hW : GenW G 5 :=
    @GenW.of_mulEquiv NativeSporadic.J3 G inferInstance inferInstance f 5 genW_J3_5
  have hcard : Nat.card G = 50232960 := by
    rw [Nat.card_congr (e.trans b.symm).toEquiv]
    exact CFSG.Sporadic.J3.card_J3
  exact (false_of_genW hp (by rw [hcard]; norm_num) hW hz hzK hN hcl hK).elim

theorem row_Co3_7 :
    KFactSporLocalRow .Co3 7 := by
  apply row_of_model
  intro G _ _ ⟨e⟩ hp _ K z hz hK hzK hN hcl _ _
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
  have f : NativeSporadic.Co3 ≃* G := b.trans e.symm
  have hW : GenW G 7 :=
    @GenW.of_mulEquiv NativeSporadic.Co3 G inferInstance inferInstance f 7 genW_Co3_7
  have hcard : Nat.card G = 495766656000 := by
    rw [Nat.card_congr (e.trans b.symm).toEquiv]
    exact CFSG.Sporadic.Co3.card_Co3
  exact (false_of_genW hp (by rw [hcard]; norm_num) hW hz hzK hN hcl hK).elim

theorem row_Co2_7 :
    KFactSporLocalRow .Co2 7 := by
  apply row_of_model
  intro G _ _ ⟨e⟩ hp _ K z hz hK hzK hN hcl _ _
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  have f : NativeSporadic.Co2 ≃* G := b.trans e.symm
  have hW : GenW G 7 :=
    @GenW.of_mulEquiv NativeSporadic.Co2 G inferInstance inferInstance f 7 genW_Co2_7
  have hcard : Nat.card G = 42305421312000 := by
    rw [Nat.card_congr (e.trans b.symm).toEquiv]
    exact CFSG.Sporadic.Co2.card_Co2
  exact (false_of_genW hp (by rw [hcard]; norm_num) hW hz hzK hN hcl hK).elim

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
