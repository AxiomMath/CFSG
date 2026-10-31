module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDesc
public import CFSG.LieType.Chevalley.GraphFixedData
public import CFSG.Open.StatedDefs
public import CFSG.GroupActions.SubgroupStabilizerOuterBound
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)

@[expose] def TriFieldData (f : ℕ) (K : Type) [Field K] (σ : K ≃+* K) : Prop :=
  1 ≤ f ∧ Nat.card K = (2 ^ f) ^ 3 ∧ ∀ c : K, σ c = c ^ (2 ^ f)

abbrev TriGrp (K : Type)
    [Field K] (σ : K ≃+* K) : Type :=
  ↥(CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom)

@[expose] def TriCompClassical : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K), TriFieldData f K σ →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ x : TriGrp K σ, x ^ p = 1 → x ≠ 1 →
      ∀ J : Subgroup (TriGrp K σ),
        CFSG.Assembly.IsComponentOf J
          (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj x)) →
        ∃ (t : StatedLieTag) (ν g : ℕ), (t = .PSL ∨ t = .PSU) ∧ 2 ≤ ν ∧
          StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) t ν 2 g

@[expose] def TriCompAction : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K), TriFieldData f K σ →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ x w : TriGrp K σ, x ^ p = 1 → x ≠ 1 → x * w = w * x →
      ∀ J : Subgroup (TriGrp K σ),
        CFSG.Assembly.IsComponentOf J
          (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj x)) →
        ∀ hw : (MulAut.conj w : MulAut (TriGrp K σ)) ∈ CFSG.GroupActions.subgroupStabAut J,
          centerQuotientHom ↥J
              (CFSG.GroupActions.subgroupStabRestrict J ⟨MulAut.conj w, hw⟩) ∈
            innAutDerived (↥J ⧸ Subgroup.center ↥J)

@[expose] def TriModelData
    {G : Type} [Group G] [Finite G] (p : ℕ) (L J : Subgroup G) (d b : G) : Prop :=
  ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* TriGrp K σ) (x w : TriGrp K σ),
    TriFieldData f K σ ∧
    LargeEvenInduces θ (conjRel d) (MulAut.conj x) ∧
    LargeEvenInduces θ (conjRel b) (MulAut.conj w) ∧
    x ^ p = 1 ∧ x ≠ 1 ∧ x * w = w * x ∧
    CFSG.Assembly.IsComponentOf ((J.subgroupOf L).map (piCenterQuot θ))
      (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj x))

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
