module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms

@[expose] def i5CentreOrder : TauCeti.LieTypeIndex → ℕ
  | .A n q => Nat.gcd (n + 1) (q.card - 1)
  | .twistedA n q => Nat.gcd (n + 1) (q.card + 1)
  | .E6 q => Nat.gcd 3 (q.card - 1)
  | .twistedE6 q => Nat.gcd 3 (q.card + 1)
  | _ => 1

@[expose] def IsI5UniversalCover (e : TauCeti.ValidLieTypeIndex) (L : Type) [Group L] : Prop :=
  CFSG.Open.IsQuasisimple L ∧ Nonempty (L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie e).Group) ∧
    IsCyclic (Subgroup.center L) ∧ Nat.card (Subgroup.center L) = i5CentreOrder e.1

@[expose] def KD264I5CoverLift : Prop :=
  ∀ (e : TauCeti.ValidLieTypeIndex) (k : ℕ), i5FieldBound e.1 k →
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
      Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie e).Group) →
      ∀ β : MulAut K, β ^ 3 = 1 →
        onCenterQuotient β ∉ innAutDerived (K ⧸ Subgroup.center K) →
        ∃ (L : Type) (_ : Group L) (_ : Finite L) (π : L →* K) (βL : MulAut L),
          Function.Surjective π ∧ (∀ x : L, π x = 1 → x ∈ Subgroup.center L) ∧
            IsI5UniversalCover e L ∧ βL ^ 3 = 1 ∧ ∀ x : L, π (βL x) = β (π x)

@[expose] def KD264I5Universal : Prop :=
  ∀ (e : TauCeti.ValidLieTypeIndex) (k : ℕ), i5FieldBound e.1 k →
    ∀ (L : Type) [Group L] [Finite L], IsI5UniversalCover e L →
      ∀ β : MulAut L, β ^ 3 = 1 →
        onCenterQuotient β ∉ innAutDerived (L ⧸ Subgroup.center L) →
        ∃ E : Subgroup L, E ≤ fixSubgroup β ∧ IsElemAbelian 3 E ∧
          k + CFSG.Open.pRank 3 (Subgroup.center L) ≤ CFSG.Open.pRank 3 E

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
