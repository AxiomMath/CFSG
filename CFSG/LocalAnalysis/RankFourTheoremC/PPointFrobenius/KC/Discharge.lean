module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KC.SeitzScope
public import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExclusionsTwo
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGen
public import CFSG.GH74.Orders.LieType
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

theorem kcSporOrd_eq_sporOrd (s : TauCeti.SporadicName) :
    kcSporOrd s = CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s := by
  cases s <;> rfl

theorem kcSporadicOrders_of_table (h : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable) :
    KCSporadicOrders :=
  fun s => (h s).trans (kcSporOrd_eq_sporOrd s).symm

theorem kcThFive_of_noncomm
    (h : CFSG.RankThree.PartOne.StrongP.HasNoncommPair 5 CFSG.Blueprint.NativeSporadic.Th)
    (e : CFSG.Blueprint.NativeSporadic.Carrier .Th ≃* (TauCeti.CFSGIndex.sporadic .Th).Group) :
    KCThFive :=
  h.map e.toMonoidHom e.injective

theorem kcFiveParts_of_cards
    (htits : ∀ hv : TauCeti.LieTypeIndex.tits.Valid,
      Nat.card (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group = 17971200)
    (hsz : ∀ hv : (TauCeti.LieTypeIndex.suzuki 2).Valid,
      Nat.card (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group = 32537600) : KCFiveParts := by
  rintro ⟨d, hv⟩ hd
  rcases hd with (rfl : d = .tits) | (rfl : d = .suzuki 2)
  · rw [htits hv]
    norm_num
  · rw [hsz hv]
    norm_num

section TitsCard

theorem kc_card_tits (hv : TauCeti.LieTypeIndex.tits.Valid) :
    Nat.card (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group = 17971200 := by
  have hR : CFSG.Blueprint.ReeTitsModel (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group .Tits 2 1 :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.reeTitsModel_tits_of_lie hv (MulEquiv.refl _)
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 hR
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD]

end TitsCard

section SuzukiCard

theorem kc_card_suzuki_two (hv : (TauCeti.LieTypeIndex.suzuki 2).Valid) :
    Nat.card (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group = 32537600 := by
  have hm := CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie
    (S := (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group) 2 ⟨hv, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, a, -, -, hc⟩ := CFSG.GH74.card_of_suzukiModel hm
  rw [hc]
  norm_num [CFSG.Open.ordSuzuki]

end SuzukiCard

section FiveParts

theorem kcFiveParts_holds : KCFiveParts :=
  kcFiveParts_of_cards kc_card_tits kc_card_suzuki_two

end FiveParts

section Orders

theorem kcSporadicOrders_holds : KCSporadicOrders :=
  kcSporadicOrders_of_table CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds

end Orders

section ThFive

theorem kcThFive_holds : KCThFive :=
  kcThFive_of_noncomm CFSG.RankThree.PartOne.CTP.hasNoncommPair_Th
    (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Th).some

end ThFive

section CharP

theorem kcCharPGen_holds : CharPGen := charPGen

end CharP

section Final

section Exceptional

theorem stronglyEmbeddedPSL2KFact_of_excParabolicFive (hP : ExcParabolicPlaneFive) :
    StronglyEmbeddedPSL2KFact :=
  stronglyEmbeddedPSL2KFact_of_inputs_five (seitzInnerExFive_of_excParabolicFive hP)
    kcCharPGen_holds kcFiveParts_holds kcSporadicOrders_holds kcThFive_holds

theorem stronglyEmbeddedPSL2KFact_of_excFiveResiduals (hR : ExcFiveResiduals) :
    StronglyEmbeddedPSL2KFact :=
  stronglyEmbeddedPSL2KFact_of_excParabolicFive (excParabolicPlaneFive_of_residuals hR)

end Exceptional

end Final

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
