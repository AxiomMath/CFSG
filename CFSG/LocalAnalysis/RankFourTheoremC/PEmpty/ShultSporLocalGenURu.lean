module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalGenUMat
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalTransport
public import CFSG.Sporadic.Bridge.RuSurj
public import Certificates.Certificate42304

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem genUW_Ru_7 : GenUW NativeSporadic.Ru 7 :=
  MGenU.genUW_of_check (spec2 28) NativeSporadic.RuSeed1 NativeSporadic.RuSeed2 ru_7_genu
    Certificates.certificate42304

theorem row_Ru_7 :
    KFactSporLocalRow .Ru 7 := by
  apply row_of_model
  intro G _ _ ⟨e⟩ hp _ K z hz hK _ hN hcl _ _
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  have f : NativeSporadic.Ru ≃* G := b.trans e.symm
  have hW : GenUW G 7 :=
    @GenUW.of_mulEquiv NativeSporadic.Ru G inferInstance inferInstance f 7 genUW_Ru_7
  have hcard : Nat.card G = 145926144000 := by
    rw [Nat.card_congr (e.trans b.symm).toEquiv]
    exact CFSG.Sporadic.Ru.card_Ru
  exact (false_of_genUW hp (by rw [hcard]; norm_num) hW hz hN hcl hK).elim

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
