module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionEntriesCriteria
import CFSG.RankThree.PartOne.CTP.SporadicNoncommFi24
import CFSG.Sporadic.Presentation.McLExact
import CFSG.Sporadic.Bridge.HSSurj
import CFSG.Sporadic.Bridge.RuSurj
import CFSG.Sporadic.Bridge.ONSurj
import CFSG.Sporadic.Bridge.Fi24Surj
import CFSG.Sporadic.Bridge.HeSurj
import CFSG.Sporadic.Bridge.J4Surj

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

open CFSG.RankThree.PartOne.StrongP (HasNoncommPair)

theorem not_smallAutomizer_of_carrier {s : TauCeti.SporadicName} {p : ℕ}
    (hbr : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃*
      (TauCeti.CFSGIndex.sporadic s).Group))
    (hN : HasNoncommPair p (CFSG.Blueprint.NativeSporadic.Carrier s)) {K : Type} [Group K]
    [Finite K] (e : K ≃* (TauCeti.CFSGIndex.sporadic s).Group) : ¬ SmallAutomizer p K := by
  obtain ⟨b⟩ := hbr
  exact not_smallAutomizer_of_hasNoncommPair
    (hN.map (e.trans b.symm).symm.toMonoidHom (e.trans b.symm).symm.injective)

theorem not_smallAutomizer_sporFive
    {s : TauCeti.SporadicName} (hs : s = .McL ∨ s = .HS ∨ s = .Ru) {K : Type} [Group K]
    [Finite K] (e : K ≃* (TauCeti.CFSGIndex.sporadic s).Group) : ¬ SmallAutomizer 5 K := by
  rcases hs with rfl | rfl | rfl
  · exact not_smallAutomizer_of_carrier (s := .McL) CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
      CFSG.RankThree.PartOne.CTP.hasNoncommPair_McL e
  · exact not_smallAutomizer_of_carrier (s := .HS) CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
      CFSG.RankThree.PartOne.CTP.hasNoncommPair_HS e
  · exact not_smallAutomizer_of_carrier (s := .Ru) CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
      CFSG.RankThree.PartOne.CTP.hasNoncommPair_Ru e

theorem not_smallAutomizer_sporSeven
    {s : TauCeti.SporadicName} (hs : s = .ONan ∨ s = .Fi24Prime ∨ s = .He) {K : Type}
    [Group K] [Finite K] (e : K ≃* (TauCeti.CFSGIndex.sporadic s).Group) :
    ¬ SmallAutomizer 7 K := by
  rcases hs with rfl | rfl | rfl
  · exact not_smallAutomizer_of_carrier (s := .ONan) CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
      CFSG.RankThree.PartOne.CTP.hasNoncommPair_ON e
  · exact not_smallAutomizer_of_carrier (s := .Fi24Prime)
      CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
      CFSG.RankThree.PartOne.CTP.hasNoncommPair_Fi24_seven e
  · exact not_smallAutomizer_of_carrier (s := .He) CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
      CFSG.RankThree.PartOne.CTP.hasNoncommPair_He e

theorem not_smallAutomizer_sporEleven
    {K : Type} [Group K] [Finite K]
    (e : K ≃* (TauCeti.CFSGIndex.sporadic .J4).Group) : ¬ SmallAutomizer 11 K :=
  not_smallAutomizer_of_carrier (s := .J4) CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
    CFSG.RankThree.PartOne.CTP.hasNoncommPair_J4 e

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSection
