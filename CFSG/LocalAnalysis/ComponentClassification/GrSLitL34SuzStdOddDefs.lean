module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSwap
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

structure L34SuzOddSetting (A : Subgroup G) (t : G) : Prop where
  base : L34BaseSetting G
  standard : IsStandardSubgroup A
  suz : Blueprint.NativeSporadic.IsSporadic (↥A ⧸ center ↥A) .Suz
  odd_card_center : Odd (Nat.card (center ↥A))
  card_sylow : ∀ S : Sylow 2 ↥(centralizer (A : Set G)), Nat.card S = 2
  orderOf_t : orderOf t = 2
  t_mem : t ∈ centralizer (A : Set G)

structure L34SuzOddData (A V K : Subgroup G) (y : G) : Prop where
  le_A : V ≤ A
  card_V : Nat.card V = 4
  mul_self : ∀ v ∈ V, v * v = 1
  card_centralizer : ∀ v (hv : v ∈ V), v ≠ 1 →
    Nat.card (centralizer ({((⟨v, le_A hv⟩ : ↥A) : ↥A ⧸ center ↥A)} : Set (↥A ⧸ center ↥A))) =
      161280
  K_eq : K = ⁅A ⊓ centralizer (V : Set G), A ⊓ centralizer (V : Set G)⁆
  perfect : ⁅K, K⁆ = K
  l34 : IsL34Type (↥K ⧸ center ↥K)
  card_image : Nat.card ↥((K.subgroupOf A).map (QuotientGroup.mk' (center ↥A))) = 20160
  y_mem : y ∈ A
  y_centralizes : y ∈ centralizer (K : Set G)
  odd_orderOf_y : Odd (orderOf y)
  y_normalizes : y ∈ normalizer (V : Set G)
  y_moves : ∀ v ∈ V, v ≠ 1 → y * v * y⁻¹ ≠ v

@[expose] def L34SuzSwappedAt (t : G) (K : Subgroup G) (u : G) : Prop :=
  ∃ (P : Subgroup G)
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)),
    P ≤ centralizer ({u} : Set G) ∧ IsComponent (P.subgroupOf (centralizer ({u} : Set G))) ∧
      P.map (MulAut.conj t).toMonoidHom ≠ P ∧ K = (HarrisLit.swapDiag P t hc).range

@[expose] def L34SuzOddDichotomy : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A V K : Subgroup G) (t y : G),
    L34SuzOddSetting A t → L34SuzOddData A V K y → ∀ u ∈ V, u ≠ 1 →
      IsComponent (K.subgroupOf (centralizer ({u} : Set G))) ∨ L34SuzSwappedAt t K u

@[expose] def L34SuzOddNormalizerControl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A V K : Subgroup G) (t y : G),
    L34SuzOddSetting A t → L34SuzOddData A V K y → ∀ u ∈ V, u ≠ 1 →
      IsComponent (K.subgroupOf (centralizer ({u} : Set G))) →
        centralizer ({u} : Set G) ≤ normalizer (A : Set G)

@[expose] def L34SuzOddSwappedExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A V K : Subgroup G) (t y : G),
    L34SuzOddSetting A t → L34SuzOddData A V K y → (∀ u ∈ V, u ≠ 1 → L34SuzSwappedAt t K u) →
      False

end CFSG.ComponentClassification.GrSLit.L34Sec5S
