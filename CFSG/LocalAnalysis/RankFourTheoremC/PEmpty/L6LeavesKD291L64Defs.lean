module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODCore
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212Inputs
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofCoverLie
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofSUData
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt odC l212in_descend l212in_suPhi
  l212in_projectiveSLEquivStated)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (conjAut)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry (Uid)

@[expose] def KD291OuterLie : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal],
    IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) → ¬ IsLinearOrUnitaryAt p L →
    (∃ d : TauCeti.ValidLieTypeIndex, Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group)) →
    centralizer (L : Set Y) = ⊥ → 3 ≤ Open.pRank p (⊤ : Subgroup Y) →
    ∀ x : Y, x ∉ L → orderOf x = p → Open.pRank p (centralizer ({x} : Set Y)) ≤ 2 →
      P64IsL2pp p ↥L

@[expose] def KD291OuterLin : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal],
    CFSG.Open.IsQuasisimple ↥L → IsPGroup p (center ↥L) →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K], p ∣ n → p ∣ Nat.card K - 1 →
    ∀ (e : ↥L ⧸ center ↥L ≃* StatedProj (StatedSL n K)) (x : Y), orderOf x = p →
      (¬ ∃ B : GL (Fin n) K, conjAut n K B =
        l212in_descend (e.trans (l212in_projectiveSLEquivStated n K).symm) (odC L x)) →
      3 ≤ Open.pRank p (centralizer ({x} : Set Y))

@[expose] def KD291OuterUni : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal],
    CFSG.Open.IsQuasisimple ↥L → IsPGroup p (center ↥L) →
    ∀ (n r f : ℕ) [Fact r.Prime] (K : Type) [Field K] [Finite K] [CharP K r],
    p ∣ n → ∀ (hK : Nat.card K = (r ^ f) ^ 2), p ∣ r ^ f + 1 →
    ∀ (e : ↥L ⧸ center ↥L ≃* StatedProj (StatedSU n (r ^ f) K)) (x : Y), orderOf x = p →
      (¬ ∃ B : Uid (unitaryInvolution K r f) n, l212in_suPhi hK B = l212in_descend e (odC L x)) →
      3 ≤ Open.pRank p (centralizer ({x} : Set Y))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
