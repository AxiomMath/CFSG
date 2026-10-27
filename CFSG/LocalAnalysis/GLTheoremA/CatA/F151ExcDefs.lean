module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupActions.SubgroupStabilizerOuterBound
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (PerfectInLayer)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)

@[expose] def CompActionAt (R : Type) [Group R] (p : ℕ) : Prop :=
  ∀ x w : R, x ≠ 1 → x ^ p = 1 → w ^ p = 1 → x * w = w * x →
    ∀ Kc : Subgroup R,
      CFSG.Assembly.IsComponentOf Kc
        (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj x)) →
      Nat.card (↥Kc ⧸ Subgroup.center ↥Kc) ≠ 360 →
      ∀ hw : MulAut.conj w ∈ CFSG.GroupActions.subgroupStabAut Kc,
        centerQuotientHom ↥Kc (CFSG.GroupActions.subgroupStabRestrict Kc ⟨MulAut.conj w, hw⟩) ∈
          CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
            (↥Kc ⧸ Subgroup.center ↥Kc)

@[expose] def D4ExitAt (R : Type) [Group R] (p : ℕ) : Prop :=
  ∀ x w : R, x ≠ 1 → x ^ p = 1 → w ^ p = 1 → x * w = w * x →
    ∀ Kc : Subgroup R,
      CFSG.Assembly.IsComponentOf Kc
        (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj x)) →
      catalogIs (↥Kc ⧸ Subgroup.center ↥Kc)
        (onLie fun i : TauCeti.LieTypeIndex => ∃ q : TauCeti.PrimePower, i = .D 4 q ∧ q.p = 2) →
      ∀ hw : MulAut.conj w ∈ CFSG.GroupActions.subgroupStabAut Kc,
        centerQuotientHom ↥Kc (CFSG.GroupActions.subgroupStabRestrict Kc ⟨MulAut.conj w, hw⟩) ∈
            CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
              (↥Kc ⧸ Subgroup.center ↥Kc) →
          centerQuotientHom ↥Kc
              (CFSG.GroupActions.subgroupStabRestrict Kc ⟨MulAut.conj w, hw⟩) ∈
            CFSG.ComponentClassification.OuterAutomorphisms.inner (↥Kc ⧸ Subgroup.center ↥Kc)

@[expose] def DiagOfCompAction : Prop :=
  ∀ (R : Type) [Group R] [Finite R] (p : ℕ), p.Prime → p ≠ 2 →
    (∀ x : R, x ≠ 1 → x ^ p = 1 → PerfectInLayer (MulAut.conj x)) →
    (∀ x : R, x ≠ 1 → x ^ p = 1 → ∀ J : Subgroup R,
      GLAPComponent p (Subgroup.centralizer ({x} : Set R)) J → IsChevSimple 2 (PSimple p J)) →
    CompActionAt R p → D4ExitAt R p → ShapeModelDiagAt R p

@[expose] def ExcAdjD4Inner : Prop :=
  ∀ {τ : CFSG.Blueprint.Chevalley.Tag},
    (τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
      (τ = .E6 → p = 3 → ¬ 3 ∣ Nat.card K - 1) →
      D4ExitAt ↥(CFSG.Blueprint.Chevalley.adjointGroup τ K) p

@[expose] def TwE6D4Inner : Prop :=
  ∀ (q : TauCeti.PrimePower), q.p = 2 →
    ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
      Nat.card K = (q.p ^ q.exponent) ^ 2 → (∀ c, σ c = c ^ (q.p ^ q.exponent)) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → (p = 3 → ¬ 3 ∣ q.p ^ q.exponent + 1) →
        D4ExitAt ↥(CFSG.LieType.Chevalley.twistedE6RootGroup K σ) p

end CFSG.LocalAnalysis.GLTheoremA.F151

end
