module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBInputs

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

structure CaseHyp (d : Data G h) : Prop where
  gms : GMSK.GMSUnitarySharpKRankOneStatement
  gmsL : GMSK.GMSLinearStandardLayerListKRankOneStatement
  hyp : d.Hyp

structure ProductCaseHyp (d : Data G h) : Prop extends CaseHyp d where
  caseB : ¬ d.M₂Linear

instance {d : Data G h} : CoeOut d.ProductCaseHyp d.CaseHyp := ⟨ProductCaseHyp.toCaseHyp⟩

@[expose] def Sec310Three (d : Data G h) : Prop :=
  ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S →
    S ⊓ centralizerSection S d.F = (d.E ⊓ d.D) ⊔ d.F

structure Sec39a1 (d : Data G h) (S : Subgroup G) : Prop where
  sylow₂ : IsSylowOf 2 (S ⊓ centralizer (d.I₂ : Set G)) d.M₂
  inter₂ : d.D ⊓ centralizer (d.I₂ : Set G) ⊓ d.M₂ = S ⊓ centralizer (d.I₂ : Set G)
  sylowE₅ : IsSylowOf 2 (d.E ⊓ centralizer (d.I₅ : Set G)) d.M₅
  inter₅ : d.D ⊓ centralizer (d.I₅ : Set G) ⊓ d.M₅ = d.E ⊓ centralizer (d.I₅ : Set G)

structure Sec39a (d : Data G h) (S : Subgroup G) : Prop where
  S_eq : S = d.E ⊔ d.D
  cD₂ : d.D ⊓ centralizer (d.I₂ : Set G) = S ⊓ centralizer (d.I₂ : Set G)
  cD₅ : d.D ⊓ centralizer (d.I₅ : Set G) = S ⊓ centralizer (d.I₅ : Set G)
  sylow₂ : IsSylowOf 2 (S ⊓ centralizer (d.I₂ : Set G)) d.M₂
  sylow₅ : IsSylowOf 2 (S ⊓ centralizer (d.I₅ : Set G)) d.M₅
  B₆_eq : d.B₆ = d.D ⊔ zpowers d.t
  S_eq₂ : S = d.E ⊔ (S ⊓ centralizer (d.I₂ : Set G))
  E_inf₂ : d.E ⊓ (S ⊓ centralizer (d.I₂ : Set G)) = ⊥
  D_eq : d.D = d.F ⊔ (S ⊓ centralizer (d.I₂ : Set G)) ⊔ (S ⊓ centralizer (d.I₅ : Set G))

structure Sec39e (d : Data G h) : Prop where
  maximal : ∀ X : Subgroup G,
    Maximal (fun Y : Subgroup G => d.F ≤ Y ∧ Y ≤ d.B₆ ∧ ElemAbMod d.F Y) X ↔
      X = d.F ⊔ d.B₃ ∨ X = d.D
  normalizer_eq : normalizer (d.B₆ : Set G) = normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G)
  t_not_mem_D : d.t ∉ d.D
  card_D : Nat.card d.D = (2 ^ f) ^ 16
  centralizer_I₁ : d.D ⊓ centralizer (d.I₁ : Set G) = ⊥

structure Know8 (d : Data G h) : Prop where
  s8 : d.Sec3_8

structure Know92 (d : Data G h) : Prop extends Know8 d where
  s9_1 : d.Sec3_9_one
  s9_2 : d.Sec3_9_two
  s9a : ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S → d.Sec39a S

structure Know93 (d : Data G h) : Prop extends Know92 d where
  s9_3 : d.Sec3_9_three
  s9e : d.Sec39e

structure Sec3101Orders (d : Data G h) (S : Subgroup G) : Prop where
  card_S : Nat.card S = (2 ^ f) ^ 20
  c₁ : Nat.card (S ⊓ centralizer (d.I₁ : Set G) : Subgroup G) = (2 ^ f) ^ 4
  c₂ : Nat.card (S ⊓ centralizer (d.I₂ : Set G) : Subgroup G) = (2 ^ f) ^ 6
  c₃ : Nat.card (S ⊓ centralizer (d.I₃ : Set G) : Subgroup G) = (2 ^ f) ^ 2
  c₄ : Nat.card (S ⊓ centralizer (d.I₄ : Set G) : Subgroup G) = (2 ^ f) ^ 4
  c₅ : Nat.card (S ⊓ centralizer (d.I₅ : Set G) : Subgroup G) = (2 ^ f) ^ 6
  c₆ : Nat.card (S ⊓ centralizer (d.I₆ : Set G) : Subgroup G) = (2 ^ f) ^ 2
  c₃₆ : Nat.card (S ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G) : Subgroup G) =
    (2 ^ f) ^ 4
  cF₅ : Nat.card (d.F ⊓ centralizer (d.I₅ : Set G) : Subgroup G) = (2 ^ f) ^ 2

@[expose] def Sec3101OrdersAll (d : Data G h) : Prop :=
  ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S → d.Sec3101Orders S

structure Know10 (d : Data G h) : Prop extends Know93 d where
  s10_1 : d.Sec3_10_one
  s10_2 : d.Sec3_10_two
  s10_3 : d.Sec310Three
  s10_o : d.Sec3101OrdersAll

structure Know11 (d : Data G h) : Prop extends Know10 d where
  s11 : d.Sec3_11

structure Know12 (d : Data G h) : Prop extends Know11 d where
  s12 : d.Sec3_12

abbrev OE (d : Data G h) : Subgroup (Bar d.E) := standardComponentOddCore (Bar d.E)

structure Sec38a1 (d : Data G h) : Prop where
  secondCenter :
    (Subgroup.upperCentralSeries ↥(d.E ⊔ zpowers d.t) 2).map (d.E ⊔ zpowers d.t).subtype = d.V
  maximal : ∀ X : Subgroup G,
    Maximal (fun Y : Subgroup G => d.V ≤ Y ∧ Y ≤ d.E ⊔ zpowers d.t ∧ ElemAbMod d.V Y) X ↔
      X = d.E ∨ X = d.V ⊔ d.B₂
  notSylow : IsPGroup 2 ↥(d.E ⊔ d.T) ∧ ¬ IsSylowOf 2 (d.E ⊔ d.T) ⊤

@[expose] def Sec38a2 (d : Data G h) : Prop :=
  ∀ Y : Subgroup G, d.V ≤ Y → Y ≤ d.E ⊔ d.T → ElemAbMod d.V Y →
    Nat.card Y ≤ (2 ^ f) ^ 14 ∧ (Nat.card Y = (2 ^ f) ^ 14 → Y = d.E)

structure Sec38a (d : Data G h) : Prop extends Sec38a1 d where
  jr : d.Sec38a2

structure Sec38Input (d : Data G h) : Prop where
  t_mem : d.t ∈ normalizer (d.E : Set G)
  kgroup : CFSG.SectionRank.IsKGroupCat (Bar d.E)
  quasisimple : CFSG.Open.IsQuasisimple (bar d.E d.N₂)
  model : LieModel (↥(bar d.E d.N₂) ⧸ center ↥(bar d.E d.N₂)) .PSU 3 2 f
  centre_le : (center ↥(bar d.E d.N₂)).map (bar d.E d.N₂).subtype ≤ OE d
  order_two : orderOf (proj d.E ⟨d.t, t_mem⟩) = 2
  centralizes : proj d.E ⟨d.t, t_mem⟩ ∈
    centralizer ((bar d.E d.N₂ : Subgroup (Bar d.E)) : Set (Bar d.E))
  normal : ((bar d.E d.N₂).subgroupOf
    (centralizer ({proj d.E ⟨d.t, t_mem⟩} : Set (Bar d.E)))).Normal
  rank : ∀ P : Subgroup (Bar d.E),
    P ≤ centralizer ((bar d.E d.N₂ : Subgroup (Bar d.E)) : Set (Bar d.E)) → IsPGroup 2 P →
      Nat.card P ≤ 2

@[expose] def Sec38NotNormal (d : Data G h) : Prop :=
  ¬ ((bar d.E d.N₂).map (QuotientGroup.mk' (OE d))).Normal

@[expose] def Sec38Outcome (d : Data G h) : Prop :=
  ∃ ht : d.t ∈ normalizer (d.E : Set G),
    GMSK.SharpOutcome (fun D _ => LieModel D .PSL 3 2 (2 * f))
      (Bar d.E ⧸ OE d) ((bar d.E d.N₂).map (QuotientGroup.mk' (OE d)))
      (QuotientGroup.mk' (OE d) (proj d.E ⟨d.t, ht⟩))

structure Sec38Odd (d : Data G h) : Prop where
  comm_le : ⁅d.L₂, d.I₂⁆ ≤ d.E
  oddCore_le : (standardComponentOddCore (centralizer (d.I₂ : Set G))).map
    (centralizer (d.I₂ : Set G)).subtype ≤ centralizer (d.N₂ : Set G)

structure Sec38Layer (d : Data G h) : Prop where
  L₂_eq : d.L₂ = d.E ⊔ d.M₂
  V_le : d.V ≤ CFSG.centerIn d.L₂
  odd : Odd (d.E.relIndex (centralizerSection d.L₂ d.E))

@[expose] def Sec39b (d : Data G h) : Prop :=
  CFSG.centerIn d.D = d.F ∧ ∀ x ∈ d.D, x * x ∈ d.F

@[expose] def Sec39c (d : Data G h) (S : Subgroup G) : Prop :=
  CFSG.centerIn S = d.V ∧ (Subgroup.upperCentralSeries ↥S 2).map S.subtype = d.W ∧
    d.D = S ⊓ centralizer (d.W : Set G)

@[expose] def Sec39d (d : Data G h) (S : Subgroup G) : Prop :=
  (d.E.subgroupOf S).Characteristic ∧ (d.D.subgroupOf S).Characteristic

end Data

namespace CaseBParts

open Data

@[expose] def SU3SylowTIStatement : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K), 1 ≤ f →
    ∀ P Q : Subgroup (hypSU h 1 1), IsSylowOf 2 P ⊤ → IsSylowOf 2 Q ⊤ → P ≠ Q → P ⊓ Q = ⊥

@[expose] def L3AutOddStatement : Prop :=
  ∀ (f : ℕ), 2 ≤ f → ∀ (X : Type) [Group X] (A : Subgroup X),
    LieModel X .PSL 3 2 (2 * f) → LieModel A .PSU 3 2 f →
      ∀ τ : MulAut X, orderOf τ = 2 → (∀ a ∈ A, τ a = a) →
        τ ∉ (MulAut.conj : X →* MulAut X).range →
        ∀ σ : MulAut X, (∀ a ∈ A, σ a = a) → Odd (orderOf σ) → σ = 1

@[expose] def L3DihedralStatement : Prop :=
  ∀ (f : ℕ), 2 ≤ f → ∀ (X : Type) [Group X] (A : Subgroup X),
    LieModel X .PSL 3 2 (2 * f) → LieModel A .PSU 3 2 f →
      ∀ τ : MulAut X, orderOf τ = 2 → (∀ a ∈ A, τ a = a) →
        τ ∉ (MulAut.conj : X →* MulAut X).range →
        ∃ u : X, u * u = 1 ∧ u * τ u ≠ 1 ∧ (u * τ u) * (u * τ u) = 1 ∧ u * τ u ∈ A

@[expose] def Sec38a1Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Sec38a1

@[expose] def Sec38a2Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Sec38a1 → d.Sec38a2

@[expose] def Sec38InputStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Sec38a → d.Sec38Input

@[expose] def Sec38NotNormalStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Sec38a → d.Sec38Input →
      d.Sec38NotNormal

@[expose] def Sec38OddStatement : Prop :=
  L3AutOddStatement → L3DihedralStatement →
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Sec38a → d.Sec38Input →
      d.Sec38NotNormal → d.Sec38Outcome → d.Sec38Odd

@[expose] def Sec38LayerStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Sec38a → d.Sec38Input →
      d.Sec38NotNormal → d.Sec38Outcome → d.Sec38Odd → d.Sec38Layer

@[expose] def Sec39a1Statement : Prop :=
  SU3SylowTIStatement →
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know8 →
      ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S → d.Sec39a1 S

@[expose] def Sec39aStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know8 →
      ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S → d.Sec39a1 S → d.Sec39a S

@[expose] def Sec39bStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know8 →
      ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S → d.Sec39a S → d.Sec39b

@[expose] def Sec39cStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know8 →
      ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S → d.Sec39a S → d.Sec39b → d.Sec39c S

@[expose] def Sec39dStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (d : Data G h), d.ProductCaseHyp → d.Know8 →
      ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S → d.Sec39a S → d.Sec39b → d.Sec39c S →
        d.Sec39d S

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
