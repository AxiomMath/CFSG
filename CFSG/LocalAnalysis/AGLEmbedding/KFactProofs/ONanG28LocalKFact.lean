module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalMain
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalSU
public import CFSG.Adapters.TauCetiExceptional.EvenB1

set_option linter.unusedSectionVars false

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.RankThree.PartTwo.Sec4.Item434G28 CFSG.RankThree.PartTwo.Sec4
  CFSG.AGLEmbedding.KFactProofs.G28

section KFact


theorem kFactG28Local : KFactG28Local := by
  intro Y _ _ Kn d hd hKn hKcat hC T Y₀ h3 hweak hne
  have : Kn.Normal := hKn
  obtain ⟨q, hq2, hq3, hdq⟩ := hd
  obtain ⟨i, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨e₀⟩ := hKcat
  have hmodel : UntwistedChevalleyModel Kn .G2 (q.p ^ q.exponent) :=
    CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
      CFSG.TauCetiBridge.Even.chevalleyBridgesEven.g2 q hv hq2 e₀
  obtain ⟨F, _, _, hF, ⟨e₁⟩⟩ := hmodel
  rw [hq2, hq3] at hF
  have hF8 : Nat.card F = 8 := by rw [hF]; norm_num
  have : CharP F 2 := CFSG.Quasithin.B42G2Id.charP_two_of_card hF
  obtain ⟨M⟩ := exists_model (K := F) hF8
  have hZF := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := F)
  let eC : AdjointQuotient .G2 F ≃* adjointGroup .G2 F :=
    (QuotientGroup.quotientMulEquivOfEq hZF).trans QuotientGroup.quotientBot
  exact kfact_main M hF8 (su_struct M hF8 (suHyp M hF8)) Kn (e₁.trans eC) hC T Y₀ h3 hweak hne

end KFact

end CFSG.AGLEmbedding

