module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigGenSound
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalTransport
public import Certificates.Certificate40343
public import CFSG.Sporadic.Bridge.ONSurj
public import CFSG.Sporadic.ON

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Blueprint CFSG.SectionRank

theorem genW_ON_5 : GenW NativeSporadic.ON 5 :=
  GClaim.genW_of_check (specP 3 154) NativeSporadic.ONSeed1 NativeSporadic.ONSeed2 on_5_claims
    Certificates.certificate40343

theorem row_ON_5 :
    KFactSporLocalRow .ONan 5 := by
  apply row_of_model
  intro G _ _ ⟨e⟩ hp _ K z hz hK hzK hN hcl _ _
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have f : NativeSporadic.ON ≃* G := b.trans e.symm
  have hW : GenW G 5 :=
    @GenW.of_mulEquiv NativeSporadic.ON G inferInstance inferInstance f 5 genW_ON_5
  have hcard : Nat.card G = 460815505920 := by
    rw [Nat.card_congr (e.trans b.symm).toEquiv]
    exact CFSG.Sporadic.ON.card_ON
  exact (false_of_genW hp (by rw [hcard]; norm_num) hW hz hzK hN hcl hK).elim

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
