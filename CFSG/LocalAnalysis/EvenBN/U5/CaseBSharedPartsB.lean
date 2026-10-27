module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedParts

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K}

abbrev OD (d : Data G h) : Subgroup (Bar d.D) := standardComponentOddCore (Bar d.D)

structure Sec39Input (d : Data G h) : Prop where
  t_mem : d.t ∈ normalizer (d.D : Set G)
  kgroup : CFSG.SectionRank.IsKGroupCat (Bar d.D)
  field : ∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ (2 * f) ∧
    Nonempty (↥(bar d.D d.N₁) ≃* SL(2, k))
  order_two : orderOf (proj d.D ⟨d.t, t_mem⟩) = 2
  centralizes : proj d.D ⟨d.t, t_mem⟩ ∈
    centralizer ((bar d.D d.N₁ : Subgroup (Bar d.D)) : Set (Bar d.D))
  normal : ((bar d.D d.N₁).subgroupOf
    (centralizer ({proj d.D ⟨d.t, t_mem⟩} : Set (Bar d.D)))).Normal
  rank : ∀ P : Subgroup (Bar d.D),
    P ≤ centralizer ((bar d.D d.N₁ : Subgroup (Bar d.D)) : Set (Bar d.D)) → IsPGroup 2 P →
      Nat.card P ≤ 2

@[expose] def Sec39NotNormal (d : Data G h) : Prop :=
  ¬ ((bar d.D d.N₁).map (QuotientGroup.mk' (OD d))).Normal

abbrev AbarD (d : Data G h) : Subgroup (Bar d.D ⧸ OD d) :=
  (bar d.D d.N₁).map (QuotientGroup.mk' (OD d))

@[expose] def Sec39Outcome (d : Data G h) : Prop :=
  ∃ ht : d.t ∈ normalizer (d.D : Set G),
    GMSK.LayerOutcome (Bar d.D ⧸ OD d) (AbarD d) (2 * f) ∧
      SteinbergBV.OneOrTwoLayerConclusion (AbarD d)
        (QuotientGroup.mk' (OD d) (proj d.D ⟨d.t, ht⟩))

structure Sec39Reduced (d : Data G h) : Prop where
  layer_type :
    Nonempty (CFSG.layer (Bar d.D ⧸ OD d) ≃* ↥(AbarD d) × ↥(AbarD d)) ∨
      LieModel (CFSG.layer (Bar d.D ⧸ OD d)) .PSL 2 2 (2 * (2 * f))
  M₁_le : d.M₁ ≤ normalizer (d.D : Set G)
  map_eq : (bar d.D d.M₁).map (QuotientGroup.mk' (OD d)) = CFSG.layer (Bar d.D ⧸ OD d)

structure Sec39Layer (d : Data G h) : Prop where
  normalClosure_eq :
    normalClosure ((bar d.D d.N₁ : Subgroup (Bar d.D)) : Set (Bar d.D)) = bar d.D d.M₁
  centralizer_eq :
    centralizer ((bar d.D d.M₁ : Subgroup (Bar d.D)) : Set (Bar d.D)) = OD d

@[expose] def Sec3101A1 (d : Data G h) (S : Subgroup G) : Prop :=
  d.V = S ⊓ centralizer (d.I₃ : Set G) ∧
    (d.W = d.V ⊔ (S ⊓ centralizer (d.I₄ : Set G)) ∧
      d.V ⊓ (S ⊓ centralizer (d.I₄ : Set G)) = ⊥)

@[expose] def Sec3101A2 (d : Data G h) (S : Subgroup G) : Prop :=
  (d.F = d.W ⊔ (S ⊓ centralizer (d.I₆ : Set G)) ∧
      d.W ⊓ (S ⊓ centralizer (d.I₆ : Set G)) = ⊥) ∧
    (d.F = (S ⊓ centralizer (d.I₄ : Set G)) ⊔
        (S ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G)) ∧
      (S ⊓ centralizer (d.I₄ : Set G)) ⊓
        (S ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G)) = ⊥)

@[expose] def Sec3101A (d : Data G h) (S : Subgroup G) : Prop :=
  d.Sec3101A1 S ∧ d.Sec3101A2 S

@[expose] def Sec3101E (d : Data G h) (S : Subgroup G) : Prop :=
  (d.E = (d.E ⊓ d.D) ⊔ (S ⊓ centralizer (d.I₁ : Set G)) ∧
      (d.E ⊓ d.D) ⊓ (S ⊓ centralizer (d.I₁ : Set G)) = ⊥) ∧
    d.E = d.W ⊔ d.W.map (MulAut.conj d.s).toMonoidHom ⊔ (S ⊓ centralizer (d.I₅ : Set G)) ∧
    d.E ⊓ d.D = d.W ⊔ (S ⊓ centralizer (d.I₅ : Set G))

@[expose] def Sec3101B (d : Data G h) (S : Subgroup G) : Prop :=
  (d.D = (d.E ⊓ d.D) ⊔ (S ⊓ centralizer (d.I₂ : Set G)) ∧
      (d.E ⊓ d.D) ⊓ (S ⊓ centralizer (d.I₂ : Set G)) = ⊥) ∧
    d.D = d.F ⊔ (S ⊓ centralizer (d.I₂ : Set G)) ⊔ (S ⊓ centralizer (d.I₅ : Set G)) ∧
    d.F ⊔ (d.E ⊓ d.D) = d.F ⊔ (S ⊓ centralizer (d.I₅ : Set G)) ∧
    (S = d.E ⊔ (S ⊓ centralizer (d.I₂ : Set G)) ∧ d.E ⊓ (S ⊓ centralizer (d.I₂ : Set G)) = ⊥) ∧
    (S = d.D ⊔ (S ⊓ centralizer (d.I₁ : Set G)) ∧ d.D ⊓ (S ⊓ centralizer (d.I₁ : Set G)) = ⊥)

@[expose] def Sec311Trans (d : Data G h) : Prop :=
  ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S → ¬ d.Sec3_11 →
    ∃ J : Subgroup G, Odd (Nat.card J) ∧
      J ≤ normalizer (S : Set G) ⊓ normalizer (d.F : Set G) ⊓ normalizer (d.E : Set G) ⊓
        normalizer (d.D : Set G) ∧
      ∀ x ∈ d.D, x ∉ (d.E ⊓ d.D) ⊔ d.F → ∀ y ∈ d.D, y ∉ (d.E ⊓ d.D) ⊔ d.F →
        ∃ j ∈ J, (j * x * j⁻¹) * y⁻¹ ∈ (d.E ⊓ d.D) ⊔ d.F

@[expose] def Sec311NotTrans (d : Data G h) : Prop :=
  ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S →
    ∀ J : Subgroup G, Odd (Nat.card J) →
      J ≤ normalizer (S : Set G) ⊓ normalizer (d.F : Set G) ⊓ normalizer (d.E : Set G) ⊓
        normalizer (d.D : Set G) →
        ¬ (∀ x ∈ d.D, x ∉ (d.E ⊓ d.D) ⊔ d.F → ∀ y ∈ d.D, y ∉ (d.E ⊓ d.D) ⊔ d.F →
          ∃ j ∈ J, (j * x * j⁻¹) * y⁻¹ ∈ (d.E ⊓ d.D) ⊔ d.F)

@[expose] def Sec313Trans (d : Data G h) : Prop :=
  ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S →
    ∀ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = (2 ^ f) ^ 2 →
      ∀ ψ : d.M₁ ≃* SL(2, k) × SL(2, k),
        Nat.card (CFSG.centerIn (d.Uc S (Common.prodFactorOne ψ))) ≤ (2 ^ f) ^ 4 →
          ∃ J : Subgroup G, Odd (Nat.card J) ∧
            J ≤ normalizer (S : Set G) ⊓ normalizer (d.F : Set G) ⊓ normalizer (d.W : Set G) ∧
            ∀ x ∈ d.F, x ∉ d.W → ∀ y ∈ d.F, y ∉ d.W → ∃ j ∈ J, (j * x * j⁻¹) * y⁻¹ ∈ d.W

@[expose] def Sec313NotTrans (d : Data G h) : Prop :=
  ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S →
    ∀ J : Subgroup G, Odd (Nat.card J) →
      J ≤ normalizer (S : Set G) ⊓ normalizer (d.F : Set G) ⊓ normalizer (d.W : Set G) →
        ¬ (∀ x ∈ d.F, x ∉ d.W → ∀ y ∈ d.F, y ∉ d.W → ∃ j ∈ J, (j * x * j⁻¹) * y⁻¹ ∈ d.W)

@[expose] def Sec312A (d : Data G h) : Prop :=
  ∀ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = (2 ^ f) ^ 2 →
    ∀ ψ : d.M₁ ≃* SL(2, k) × SL(2, k),
      (d.F ⊔ d.Kc (Common.prodFactorOne ψ)) ⊔
          (d.F ⊔ (d.Kc (Common.prodFactorOne ψ)).map (MulAut.conj d.t).toMonoidHom) = d.L₁ ∧
        (d.F ⊔ d.Kc (Common.prodFactorOne ψ)) ⊓
          (d.F ⊔ (d.Kc (Common.prodFactorOne ψ)).map (MulAut.conj d.t).toMonoidHom) = d.F

@[expose] def Sec312B (d : Data G h) : Prop :=
  ∀ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = (2 ^ f) ^ 2 →
    ∀ ψ : d.M₁ ≃* SL(2, k) × SL(2, k),
      IsNaturalSection (d.M₁ ⊓ d.Kc (Common.prodFactorOne ψ))
        ((d.F ⊔ d.Kc (Common.prodFactorOne ψ)) ⊓ d.D) d.F k

end Data

namespace CaseBParts

open Data

@[expose] def Sec39eStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know92 → d.Sec39e

@[expose] def Sec39InputStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know92 → d.Sec39e →
      d.Sec39Input

@[expose] def Sec39NotNormalStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know92 → d.Sec39e →
      d.Sec39Input → d.Sec39NotNormal

@[expose] def Sec39ReducedStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know92 → d.Sec39e →
      d.Sec39Input → d.Sec39NotNormal → d.Sec39Outcome → d.Sec39Reduced

@[expose] def Sec39LayerStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know92 → d.Sec39e →
      d.Sec39Input → d.Sec39NotNormal → d.Sec39Outcome → d.Sec39Reduced → d.Sec39Layer

@[expose] def Sec39LOneStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know92 → d.Sec39e →
      d.Sec39Reduced → d.Sec39Layer → d.L₁ = d.D ⊔ d.M₁

@[expose] def Sec39OddStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know92 → d.Sec39e →
      d.Sec39Reduced → d.Sec39Layer →
        Odd (d.D.relIndex (centralizerSection (d.D ⊔ d.M₁) d.D))

@[expose] def Sec3101A1Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know93 → d.Sec3_10_two →
      ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S → d.Sec3101Orders S → d.Sec3101A1 S

@[expose] def Sec3101A2Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know93 → d.Sec3_10_two →
      ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S → d.Sec3101Orders S → d.Sec3101A1 S →
        d.Sec3101A2 S

@[expose] def Sec3101EStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know93 → d.Sec3_10_two →
      ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S → d.Sec3101Orders S → d.Sec3101A S →
        d.Sec3101E S

@[expose] def Sec3101BStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know93 → d.Sec3_10_two →
      ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S → d.Sec3101Orders S → d.Sec3101A S →
        d.Sec3101E S → d.Sec3101B S

@[expose] def Sec3101OrdersStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know93 →
      d.Sec3101OrdersAll

@[expose] def Sec3102Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know93 →
      d.Sec3101OrdersAll → d.Sec3_10_two

@[expose] def Sec310ThreeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know93 →
      d.Sec3_10_one → d.Sec3_10_two → d.Sec310Three

@[expose] def Sec311TransStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know10 → d.Sec311Trans

@[expose] def Sec311NotTransStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know10 → d.Sec311NotTrans

@[expose] def Sec312AStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know11 → d.Sec312A

@[expose] def Sec312BStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know11 → d.Sec312A →
      d.Sec312B

@[expose] def Sec313TransStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know12 → d.Sec313Trans

@[expose] def Sec313NotTransStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know12 → d.Sec313NotTrans

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
