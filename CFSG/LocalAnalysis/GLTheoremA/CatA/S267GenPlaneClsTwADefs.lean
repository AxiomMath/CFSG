module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def TwADvd (p : ℕ) (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ (r : ℕ) (Q : TauCeti.PrimePower), d = .twistedA r Q ∧ p ∣ Q.card + 1

@[expose] def GenPlaneTwANotDvd : Prop :=
  ∀ (p : ℕ) (T : Type) [Group T] [Finite T] (d : TauCeti.ValidLieTypeIndex), OddLie p T d →
    PlaneIdxTwA d.1 → ¬ TwADvd p d.1 → ∀ P : Subgroup (MulAut T), IsElemAbelian p P →
      Nat.card P = p ^ 2 → ∀ J : Subgroup T, ¬ ∀ x ∈ P, x ≠ 1 → GLAPComponent p (fixSubgroup x) J

@[expose] def GenPlaneTwADvd : Prop :=
  ∀ (p : ℕ) (T : Type) [Group T] [Finite T] (d : TauCeti.ValidLieTypeIndex), OddLie p T d →
    TwADvd p d.1 → ∀ P : Subgroup (MulAut T), IsElemAbelian p P →
      Nat.card P = p ^ 2 → ∀ J : Subgroup T, ¬ ∀ x ∈ P, x ≠ 1 → GLAPComponent p (fixSubgroup x) J

theorem genPlaneCompOn_twA_of_halves (ha : GenPlaneTwANotDvd) (hb : GenPlaneTwADvd) :
    GenPlaneCompOn PlaneIdxTwA := by
  intro p T _ _ d hd hQ
  by_cases h : TwADvd p d.1
  · exact hb p T d hd h
  · exact ha p T d hd hQ h

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
