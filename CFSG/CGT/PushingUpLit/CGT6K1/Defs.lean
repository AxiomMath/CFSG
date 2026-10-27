module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndGMS
public import CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootDatum

public section

namespace CFSG.CGT.PushingUpLit.CGT6K1

open CFSG CFSG.Blueprint CFSG.LocalAnalysis.EvenBN.GMSK CFSG.CGT.PushingUpLit.CGT6

@[expose] def StdKernelTwo : Prop :=
  ∀ (D : Type) [Group D] [Finite D], IsSimpleGroup D → CFSG.SectionRank.IsKGroupCat D →
    ∀ (n : ℕ) (A : Subgroup D), StdLinearData D A n →
      CFSG.Open.pRank 2 (Subgroup.centralizer (A : Set D)) ≤ 1 →
        ∀ S : Sylow 2 (Subgroup.centralizer (A : Set D)), Nat.card S = 2

@[expose] def CatSelector : Prop :=
  FixedRootSelector fun D _ => Catalog D

@[expose] def InnerSurvivorsInV : Prop :=
  ∀ (D : Type) [Group D] [Finite D], IsSimpleGroup D → ∀ (n : ℕ) (K : Type) [Field K] [Fintype K]
    (α : MulAut D) (S : Subgroup D), FixedRootDatum D n K α S →
      α ∈ (MulAut.conj : D →* MulAut D).range → FixedRootSurvivors D n → n = 2 ∧ GMSVList D

@[expose] def Rank2Std : Prop :=
  ∀ (D : Type) [Group D] [Finite D], IsSimpleGroup D → CFSG.SectionRank.IsKGroupCat D →
    ∀ (n : ℕ) (A : Subgroup D), StdLinearData D A n →
      2 ≤ CFSG.Open.pRank 2 (Subgroup.centralizer (A : Set D)) → n = 2 ∧ GMSVList D

@[expose] def SimpleStd : Prop :=
  ∀ (D : Type) [Group D] [Finite D], IsSimpleGroup D → CFSG.SectionRank.IsKGroupCat D →
    ∀ (n : ℕ) (A : Subgroup D), StdLinearData D A n → n = 2 ∧ GMSVList D

structure AlmostSimple (Q : Type) [Group Q] [Finite Q] (n : ℕ) (A T₀ : Subgroup Q) : Prop where
  kgroup : CFSG.SectionRank.IsKGroupCat Q
  std : StdLinearData Q A n
  simple : IsSimpleGroup ↥(CFSG.layer Q)
  cen : Subgroup.centralizer (CFSG.layer Q : Set Q) = ⊥
  le : A ≤ CFSG.layer Q
  sylow : ABGLocalTools.IsSylowOf 2 T₀ (Subgroup.centralizer (A : Set Q))
  ne : T₀ ≠ ⊥

@[expose] def SimpleOuterOutcome (Q : Type) [Group Q] (n : ℕ) (T₀ : Subgroup Q) : Prop :=
  (n = 2 ∧ GMSVList ↥(CFSG.layer Q)) ∨
    (T₀ ⊓ CFSG.layer Q = ⊥ ∧
      (LieModel ↥(CFSG.layer Q) .PSL 2 2 (2 * n) ∨ LieModel ↥(CFSG.layer Q) .PSU 3 2 n ∨
        LieModel ↥(CFSG.layer Q) .PSL 3 2 n ∨ (n = 3 ∧ LieModel ↥(CFSG.layer Q) .G2 0 3 1)))

end CFSG.CGT.PushingUpLit.CGT6K1
