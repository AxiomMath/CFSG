module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralH360Comp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralH360CompTw
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CDynE
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqLieEven
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltSevenNotLie
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.DiagonalLink
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpChainBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.ContainerDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ClosingAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FiStep
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.TypeMax
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Lemma39
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Mult
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3Glob
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Residual
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSetting
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynExc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct
open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.GroupActions CFSG.LocalAnalysis.GLTheoremA.S265C.DynE
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open scoped Pointwise


theorem centerQuot_card_ne_360_of_tagLieType_two {L : Type} [Field L] [CharP L 2]
    {X : Type} [Group X] {P : StatedLieTag → Prop}
    (h : TagLieType P (ringChar L) X) :
    Nat.card (X ⧸ Subgroup.center X) ≠ 360 := by
  obtain ⟨t, r, e, -, hm⟩ := h
  have h2 : ringChar L = 2 := ringChar.eq L 2
  rw [h2] at hm
  exact CFSG.ComponentClassification.CatFC.lieModel_two_card_ne_360
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hm.admissible hm

theorem T171ToralLangComp.centerQuot_ne_360_of_tagLie {n : ℕ} {K : Type} [Field K] [Finite K]
    {S : LangSetup Tag.E6 (AlgebraicClosure K) 5}
    {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ}
    {G : Type} [Group G] {φ : G →* G} {Kc : Subgroup G}
    {hnorm : ∀ x ∈ Kc, φ x ∈ Kc} [CharP (AlgebraicClosure K) 2]
    (D : T171ToralLangComp n K S a G φ Kc hnorm)
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) :
    Nat.card (↥Kc ⧸ Subgroup.center ↥Kc) ≠ 360 := by
  have htag := tagLie_rationalComponent_E6 S Nat.prime_three hT hap h1 D.i D.hQS
  have hne := centerQuot_card_ne_360_of_tagLieType_two (L := AlgebraicClosure K) htag
  exact fun h => hne (by rw [← D.card_centerQuot_eq]; exact h)

theorem e6ToralLangSetupH360_holds : E6ToralLangSetupH360 := by
  intro n K _ _ _ hn hKcard h3 wd wb hwd3 hwd1 hwb3 w g0 hg0 hF htorus Kc hKc hnorm
  obtain ⟨S, a, D, -, hT, hap, -, h1, -⟩ :=
    nonempty_e6ToralLangComp n K hn hKcard h3 wd wb hwd3 hwd1 hwb3 w g0 hg0 hF htorus Kc hKc
      hnorm
  exact D.centerQuot_ne_360_of_tagLie hT hap h1

theorem twE6ToralLangSetupH360_holds : TwE6ToralLangSetupH360 := by
  intro n K _ _ hn hKcard h3 σ hσ ε wd wb hwd3 hwd1 hwb3 Fr hFr g hg hn0 htorus Kc hKc hnorm
  haveI hcharK : CharP K 2 :=
    CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hKcard, pow_mul])
  haveI hcharL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨S, a, D, -, hT, hap, -, h1, -⟩ :=
    nonempty_twE6ToralLangComp n K hn hKcard h3 σ hσ ε wd wb hwd3 hwd1 hwb3 Fr hFr g hg hn0
      htorus Kc hKc hnorm
  exact D.centerQuot_ne_360_of_tagLie hT hap h1

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
