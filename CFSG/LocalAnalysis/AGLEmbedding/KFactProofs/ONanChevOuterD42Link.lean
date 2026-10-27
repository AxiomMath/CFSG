module

public import CFSG.Quasithin.Recognition.CertD4Bridge
public import CFSG.RankThree.PartOne.S11c.Sec66TModelsTw
import CFSG.Adapters.TauCetiExceptional.EvenB1
public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Check
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42LinkCheck

public section

open CFSG.Quasithin CFSG.Open CFSG.Blueprint CFSG.RankThree.PartTwo.Sec4.Item434D42

namespace CFSG.AGLEmbedding.ChevOuter


theorem exists_model_equiv {L : Type} [Group L] (d : TauCeti.ValidLieTypeIndex)
    (q : TauCeti.PrimePower) (hq : q.p = 2) (hq1 : q.exponent = 1) (hdq : d.1 = .trialityD4 q)
    (e : L ≃* CatGroup d) :
    ChevalleyExceptionalModel L .trialityD4 2 1 ∧ Nonempty (L ≃* lineGroup) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.trialityD4 q := hdq
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel
      (CatGroup ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩) .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hv hq (by decide)
        (MulEquiv.refl _)⟩
  rw [hq, hq1] at hm
  refine ⟨CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e hm, ?_⟩
  have hL : CFSG.Blueprint.LieModel (CatGroup ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩)
      .trialityD4 0 2 1 := CFSG.RankThree.PartOne.Sec66T.lieModel_trialityD4_iff.mpr ⟨rfl, hm⟩
  obtain ⟨e2⟩ := trialityD4ModelBridge_of_lieModel _ hL
  have hk8 : Nat.card GF8 = 8 := by rw [Nat.card_eq_fintype_card]; rfl
  obtain ⟨e3⟩ := d4bG8_equiv_quasithin GF8 hk8
  exact ⟨e.trans (e2.trans (e3.symm.trans (MulEquiv.subgroupCongr lineGroup_eq.symm)))⟩

end CFSG.AGLEmbedding.ChevOuter
