module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.ClassS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.ProperFixed
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LeavesV

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification CFSG.Open

@[expose] def ClosureFieldExp : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (σ : MulAut S) (P : Subgroup S), ProperFixedComp σ P →
    ∀ (τ : StatedLieTag) (n c : ℕ), LieModel S τ n 3 c →
    ∀ (τ' : StatedLieTag) (n' d : ℕ), LieModel (P ⧸ center P) τ' n' 3 d →
      c = 2 * d ∨ d = c ∨ d = 2 * c ∨ d = 4 * c ∨ d = 3 * c

@[expose] def ClosureSmallCases : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (LieModel S .PSL 3 2 2 ∨ NativeSporadic.IsSporadic S .He ∨ NativeSporadic.IsSporadic S .M12 ∨
      NativeSporadic.IsSporadic S .J2) →
    ∀ (σ : MulAut S) (P : Subgroup S), ProperFixedComp σ P →
      Nat.card (P ⧸ center P) < 20160 ∨ LieModel (P ⧸ center P) .PSL 3 2 2

@[expose] def OmegaEightMinIndexWeak : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (H : Subgroup S), H ≠ ⊤ →
    (LieModel S .POmegaPlus 4 3 1 → 36 ≤ H.index) ∧
      (LieModel S .POmegaMinus 4 3 1 → 72 ≤ H.index)

@[expose] def ChevThreeInter : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (r : ℕ), r.Prime → r ≠ 2 → r ≠ 3 →
    HarrisLit.IsSimpleChevalleyOver 3 S → HarrisLit.IsSimpleChevalleyOver r S →
      Nat.card S ≤ 25920

structure ClosureLeaves : Prop where
  cl1 : CatLeaf.GLS3OddLieAutComponentsInput
  cl2 : ClosureFieldExp
  cl3 : ClosureSmallCases
  cl4 : OmegaEightMinIndexWeak
  cl5 : ChevThreeInter

@[expose] def ResidualTwoRank : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → IsPGroup 2 ↥(center K) →
    IsResidualA2 K → 2 ≤ CFSG.pRank 2 K ∧ (center K ≠ ⊥ → 3 ≤ CFSG.pRank 2 K)

@[expose] def ResidualNotChevOdd : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (r : ℕ), r.Prime → r ≠ 2 →
    HarrisLit.IsSimpleChevalleyOver r S →
      ¬ ((∃ n : ℕ, 8 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∨
        NativeSporadic.IsSporadic S .HS ∨ LieModel S .PSp 2 2 2 ∨ LieModel S .PSL 5 2 1 ∨
        LieModel S .PSU 5 2 1 ∨ LieModel S .G2 0 2 2 ∨ LieModel S .PSL 4 2 2)

@[expose] def TwoAnSL25 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), 7 ≤ n → GH74.GLS.IsDoubleCoverOfAlt Y n →
    ∃ N : Subgroup Y, center Y ≤ N ∧ HarrisLit.IsSLTwoOver 5 ↥N

@[expose] def Chev3DatumEnd : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → IsPGroup 2 ↥(center K) →
    InSB (K ⧸ center K) → (¬ ∃ e : ℕ, LieModel (K ⧸ center K) .PSL 2 3 e) → KDatum K

structure Leaves2 : Prop where
  closure : ClosureLeaves
  residualRank : ResidualTwoRank
  residualNotChevOdd : ResidualNotChevOdd
  twoAnSL25 : TwoAnSL25
  chev3End : Chev3DatumEnd

end CFSG.OddStandard.SmallF3.HypA2
