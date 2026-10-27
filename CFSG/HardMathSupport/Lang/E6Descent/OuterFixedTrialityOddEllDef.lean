module

public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerLangCurves
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4FixedLine
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnA2Fam
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

@[expose] def rotElt {L : Type} [Field L] (b : Lˣ) : ModGL TwistTag.D4.tag L :=
  rootDiagUnit TwistTag.D4.tag (![1, 1, b, 1] : Fin TwistTag.D4.tag.rank → Lˣ) *
    (diagramMap TwistTag.D4 L)⁻¹

@[expose] def twistHomOpp {L : Type} [Field L] (Fr : L →+* L) (g : ModGL TwistTag.D4.tag L) :
    ModGL TwistTag.D4.tag L :=
  trialityOpposition L * twistHom TwistTag.D4 L Fr g * (trialityOpposition L)⁻¹

@[expose] def RotLang : Prop :=
  ∀ (p f : ℕ) [Fact p.Prime], 5 ≤ p → 1 ≤ f →
    ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L p] (b : Lˣ), b ^ 3 = 1 → b ≠ 1 →
    ∀ ζ ∈ graphCentralizer TwistTag.D4.tag L (rotElt b),
      (∃ t ∈ torusGroup TwistTag.D4.tag L, ∃ q ∈ rootSpan TwistTag.D4.tag L d4LongA2,
        ζ = t * q) →
      (∃ hm : ζ ∈ monomialSubgroup TwistTag.D4.tag L,
        (∀ x, weylQuotientHom TwistTag.D4.tag L ⟨ζ, hm⟩ • x = d4MatThreeA *ᵥ x) ∨
          (∀ x, weylQuotientHom TwistTag.D4.tag L ⟨ζ, hm⟩ • x = d4MatThreeB *ᵥ x)) →
      ((p ^ f) % 3 = 1 →
        ∃ z ∈ graphCentralizer TwistTag.D4.tag L (rotElt b),
          z⁻¹ * twistHom TwistTag.D4 L (iterateFrobenius L p f) z = ζ) ∧
      ((p ^ f) % 3 = 2 →
        ∃ z ∈ graphCentralizer TwistTag.D4.tag L (rotElt b),
          z⁻¹ * twistHomOpp (iterateFrobenius L p f) z = ζ)

end CFSG.HardMathSupport.Lang.E6Descent
