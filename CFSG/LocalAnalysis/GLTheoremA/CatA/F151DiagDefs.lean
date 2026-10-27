module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151Defs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInOmGen
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup PerfectInLayer)

@[expose] def BlockAnalysisAt (R : Type) [Group R] [Finite R] (p : ℕ) : Prop :=
  ∀ x y : R, x ^ p = 1 → y ^ p = 1 → x * y = y * x → x ≠ 1 →
    ∀ J : Subgroup R, CFSG.Assembly.IsComponentOf J (fixSubgroup (MulAut.conj x)) →
      ∀ hN : y ∈ Subgroup.normalizer (J : Set R),
        (catalogIs (PSimple p J) (onLie T171Sh.isLinearCharTwoIdx) ∧
            MI.indAut p J y hN ∈
              CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived (PSimple p J)) ∨
          (catalogIs (PSimple p J) (onLie T171Sh.isUnitaryCharTwoIdx) ∧
            MI.indAut p J y hN ∈
              CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived (PSimple p J)) ∨
          MI.indAut p J y hN ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p J)

@[expose] def CatLayer : Prop :=
  ∀ (R : Type) [Group R] [Finite R] (p : ℕ), p.Prime → p ≠ 2 →
    catalogIs R (onLie fun d => d.characteristic = 2) →
      ∀ x : R, x ≠ 1 → x ^ p = 1 → PerfectInLayer (MulAut.conj x)

@[expose] def CatChevComps : Prop :=
  ∀ (R : Type) [Group R] [Finite R] (p : ℕ), p.Prime → p ≠ 2 →
    catalogIs R (onLie fun d => d.characteristic = 2) →
      ∀ x : R, x ≠ 1 → x ^ p = 1 → ∀ J : Subgroup R,
        GLAPComponent p (Subgroup.centralizer ({x} : Set R)) J → IsChevSimple 2 (PSimple p J)

@[expose] def DiagOfBlock : Prop :=
  ∀ (R : Type) [Group R] [Finite R] (p : ℕ), p.Prime → p ≠ 2 →
    (∀ x : R, x ≠ 1 → x ^ p = 1 → PerfectInLayer (MulAut.conj x)) →
    (∀ x : R, x ≠ 1 → x ^ p = 1 → ∀ J : Subgroup R,
      GLAPComponent p (Subgroup.centralizer ({x} : Set R)) J → IsChevSimple 2 (PSimple p J)) →
    BlockAnalysisAt R p → ShapeModelDiagAt R p

end CFSG.LocalAnalysis.GLTheoremA.F151

end
