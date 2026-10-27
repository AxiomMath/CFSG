module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitMaximal
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedLieTag)

@[expose] def FooteCoreOddLieInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K], SectionRank.IsKGroupCat K → ∀ a : K, orderOf a = 2 →
    ∀ Y : Subgroup K, IsPComponent 2 Y → OddLieType (Y ⧸ Open.fusionZStar Y) →
    (¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      LieModel (Y ⧸ Open.fusionZStar Y) .PSL 2 p f) →
    (¬ ∃ n : ℕ, Nonempty ((Y ⧸ Open.fusionZStar Y) ≃* alternatingGroup (Fin n))) →
    ¬ Nonempty ((Y ⧸ Open.fusionZStar Y) ≃* NativeSporadic.He) →
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K

@[expose] def EvenLieMultiplierOuterInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    EvenLieType S → ¬ LieModel S .PSL 3 2 2 →
    RankTwoSporadic.OddMultiplier S ∨ Nat.card (OuterAutomorphisms.Outer S) ≤ 8

@[expose] def EvenLieExceptionalOuterInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (t : StatedLieTag) (n f : ℕ),
    (t, n, f) ∈ [(.G2, 0, 2), (.F4, 0, 1), (.twistedE6, 0, 1)] → LieModel S t n 2 f →
    Nat.card (OuterAutomorphisms.Outer S) ≤ 8

end CFSG.ComponentClassification.Foote5
