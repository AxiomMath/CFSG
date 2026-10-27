module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullAutomorphisms
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma37Core
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.LocalAnalysis.ComponentClassification.AS76bHypII
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Open.QuasithinDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open scoped Matrix

section Matrices

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  {H : Subgroup (GL ι K)}

@[expose] def Represents (e : rankTwoQuot A ≃* StatedProj H) (x : G) (M : GL ι K) : Prop :=
  ∃ (hx : x ∈ A) (hM : M ∈ H), e (QuotientGroup.mk ⟨x, hx⟩) = QuotientGroup.mk ⟨M, hM⟩

@[expose] noncomputable def commRank (M : GL ι K) : ℕ := ((M : Matrix ι ι K) - 1).rank

@[expose] def IsInvolutionOfRank (e : rankTwoQuot A ≃* StatedProj H) (x : G) (ℓ : ℕ) : Prop :=
  orderOf x = 2 ∧ ∃ M : GL ι K, Represents e x M ∧ orderOf M = 2 ∧ commRank M = ℓ

@[expose] def IsSingularRankTwo (e : rankTwoQuot A ≃* StatedProj H) (Q : (ι → K) → K) (x : G) :
    Prop :=
  orderOf x = 2 ∧ ∃ M : GL ι K, Represents e x M ∧ orderOf M = 2 ∧ commRank M = 2 ∧
    ∀ v : ι → K, Q (((M : Matrix ι ι K) - 1) *ᵥ v) = 0

@[expose] def alphaGroup (e : rankTwoQuot A ≃* StatedProj H) (x : G) : Subgroup G :=
  closure {y | (∃ k : ℕ, y ^ 2 ^ k = 1) ∧ ∃ M N : GL ι K, Represents e x M ∧ orderOf M = 2 ∧
    Represents e y N ∧ ∃ a : K, (N : Matrix ι ι K) - 1 = a • ((M : Matrix ι ι K) - 1)}

end Matrices

inductive ClassicalModel {G : Type} [Group G] (A : Subgroup G) : Type 1
  | linear (n m : ℕ) (hn : 4 ≤ n) (hm : 1 ≤ m) (hnm : (n, m) ≠ (4, 1)) (K : Type) [Field K]
      [Finite K] (hK : Nat.card K = 2 ^ m) (e : rankTwoQuot A ≃* StatedProj (StatedSL n K))
  | unitary (n m : ℕ) (hn : 4 ≤ n) (hm : 1 ≤ m) (K : Type) [Field K] [Finite K]
      (hK : Nat.card K = (2 ^ m) ^ 2) (e : rankTwoQuot A ≃* StatedProj (StatedSU n (2 ^ m) K))
  | symplectic (n m : ℕ) (hn : 2 ≤ n) (hm : 1 ≤ m) (hnm : (n, 2 ^ m) ≠ (2, 2)) (K : Type)
      [Field K] [Finite K] (hK : Nat.card K = 2 ^ m)
      (e : rankTwoQuot A ≃* StatedProj (StatedSp n K))
  | orthPlus (n m : ℕ) (hn : 4 ≤ n) (hm : 1 ≤ m) (K : Type) [Field K] [Finite K]
      (hK : Nat.card K = 2 ^ m)
      (e : rankTwoQuot A ≃* StatedProj (StatedOmega (StatedQuadPlus n K)))
  | orthMinus (n m : ℕ) (hn : 4 ≤ n) (hm : 1 ≤ m) (K : Type) [Field K] [Finite K]
      (hK : Nat.card K = 2 ^ m) (b c : K) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
      (e : rankTwoQuot A ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)))

inductive Family
  | linear
  | unitary
  | symplectic
  | orthPlus
  | orthMinus
  deriving DecidableEq

namespace ClassicalModel

variable {G : Type} [Group G] {A : Subgroup G}

@[expose] def family : ClassicalModel A → Family
  | @linear .. => .linear
  | @unitary .. => .unitary
  | @symplectic .. => .symplectic
  | @orthPlus .. => .orthPlus
  | @orthMinus .. => .orthMinus

@[expose] def q : ClassicalModel A → ℕ
  | @linear _ _ _ _ m _ _ _ _ _ _ _ _ => 2 ^ m
  | @unitary _ _ _ _ m _ _ _ _ _ _ _ => 2 ^ m
  | @symplectic _ _ _ _ m _ _ _ _ _ _ _ _ => 2 ^ m
  | @orthPlus _ _ _ _ m _ _ _ _ _ _ _ => 2 ^ m
  | @orthMinus _ _ _ _ m _ _ _ _ _ _ _ _ _ _ => 2 ^ m

@[expose] def IsPrimary : ClassicalModel A → G → Prop
  | @linear _ _ _ _ _ _ _ _ _ _ _ _ e, x => IsInvolutionOfRank e x 1
  | @unitary _ _ _ _ _ _ _ _ _ _ _ e, x => IsInvolutionOfRank e x 1
  | @symplectic _ _ _ _ _ _ _ _ _ _ _ _ e, x => IsInvolutionOfRank e x 1
  | @orthPlus _ _ _ n _ _ _ K _ _ _ e, x => IsSingularRankTwo e (StatedQuadPlus n K) x
  | @orthMinus _ _ _ n _ _ _ K _ _ _ b c _ e, x =>
      IsSingularRankTwo e (StatedQuadMinus n K b c) x

@[expose] def alpha : ClassicalModel A → G → Subgroup G
  | @linear _ _ _ _ _ _ _ _ _ _ _ _ e => alphaGroup e
  | @unitary _ _ _ _ _ _ _ _ _ _ _ e => alphaGroup e
  | @symplectic _ _ _ _ _ _ _ _ _ _ _ _ e => alphaGroup e
  | @orthPlus _ _ _ _ _ _ _ _ _ _ _ e => alphaGroup e
  | @orthMinus _ _ _ _ _ _ _ _ _ _ _ _ _ _ e => alphaGroup e

@[expose] def LeviType : ClassicalModel A → Subgroup G → Prop
  | @linear _ _ _ n m _ _ _ _ _ _ _ _, L => StatedClassicalModel (rankTwoQuot L) .PSL (n - 2) 2 m
  | @unitary _ _ _ n m _ _ _ _ _ _ _, L =>
      (5 ≤ n ∧ StatedClassicalModel (rankTwoQuot L) .PSU (n - 2) 2 m) ∨
        (n = 4 ∧ StatedClassicalModel (rankTwoQuot L) .PSL 2 2 m)
  | @symplectic _ _ _ n m _ _ _ _ _ _ _ _, L =>
      (3 ≤ n ∧ StatedClassicalModel (rankTwoQuot L) .PSp (n - 1) 2 m) ∨
        (n = 2 ∧ StatedClassicalModel (rankTwoQuot L) .PSL 2 2 m)
  | @orthPlus _ _ _ n m _ _ _ _ _ _ _, L =>
      (6 ≤ n ∧ StatedClassicalModel (rankTwoQuot L) .POmegaPlus (n - 2) 2 m) ∨
        (n = 5 ∧ StatedClassicalModel (rankTwoQuot L) .PSL 4 2 m) ∨
        (n = 4 ∧ StatedClassicalModel (rankTwoQuot L) .PSL 2 2 m)
  | @orthMinus _ _ _ n m _ _ _ _ _ _ _ _ _ _, L =>
      (6 ≤ n ∧ StatedClassicalModel (rankTwoQuot L) .POmegaMinus (n - 2) 2 m) ∨
        (n = 5 ∧ StatedClassicalModel (rankTwoQuot L) .PSU 4 2 m) ∨
        (n = 4 ∧ StatedClassicalModel (rankTwoQuot L) .PSL 2 2 m)

@[expose] def IsLinearFiveFour : ClassicalModel A → Prop
  | @linear _ _ _ n m _ _ _ _ _ _ _ _ => n = 5 ∧ m = 2
  | _ => False

@[expose] def IsLTwoFour : ClassicalModel A → Prop
  | @linear _ _ _ n m _ _ _ _ _ _ _ _ => n = 4 ∧ m = 2
  | @unitary _ _ _ n m _ _ _ _ _ _ _ => n = 4 ∧ m = 2
  | @symplectic _ _ _ n m _ _ _ _ _ _ _ _ => n = 2 ∧ m = 2
  | @orthPlus _ _ _ n m _ _ _ _ _ _ _ => n = 4 ∧ m = 2
  | @orthMinus _ _ _ n m _ _ _ _ _ _ _ _ _ _ => n = 4 ∧ m = 2

end ClassicalModel

section Stages

variable {G : Type} [Group G] {A : Subgroup G}

@[expose] def NoInvolutoryCentralizing (A X : Subgroup G) : Prop :=
  ∀ σ : MulAut ↥A, σ * σ = 1 → (∀ x : ↥A, (x : G) ∈ X → σ x = x) → σ = 1

structure Choice74 (D : ClassicalModel A) (R T : Subgroup G) (g : G) : Prop where
  sylowR : IsSylowOf 2 R (centralizer (A : Set G))
  not_mem : g ∉ normalizer (A : Set G)
  sylowT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)
  le_centralizer : T ≤ centralizer (R : Set G)
  inf_eq_bot : T ⊓ A = ⊥
  primary : ∀ t ∈ T, t ≠ 1 → ∀ p ∈ A, t⁻¹ * p ∈ R → D.IsPrimary p
  not_le : ∀ x : G, ¬ rightConjugate R x ≤ A
  oddCenter : Odd (Nat.card (center A))
  four_le : 4 ≤ D.q

structure Levi75 (D : ClassicalModel A) (T Y W L : Subgroup G) : Prop where
  W_le : W ≤ Y
  Y_le : Y ≤ A
  T_le : T ≤ centralizer (Y : Set G)
  L_le : L ≤ A ⊓ centralizer (Y : Set G)
  W_type : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = D.q ∧
    Nonempty (↥W ≃* Matrix.SpecialLinearGroup (Fin 2) F)
  levi : D.LeviType L
  quasisimple : CFSG.Open.IsQuasisimple ↥L
  oddCenter : Odd (Nat.card (center ↥L))
  standard : standardComponentIsStandard (L.subgroupOf (centralizer (Y : Set G)))
  not_normal : ¬ (L.subgroupOf (centralizer (Y : Set G))).Normal
  L_eq : L = AS76b.layerCentralizer A Y
  diag : D.IsLinearFiveFour → ∃ y ∈ A ⊓ centralizer (Y : Set G), (∃ k : ℕ, y ^ 3 ^ k = 1) ∧
    ¬ ∃ l ∈ L, ∀ x ∈ L, y * x * y⁻¹ * (l * x * l⁻¹)⁻¹ ∈ (center ↥L).map L.subtype
  noInv : NoInvolutoryCentralizing A (Y ⊔ L)
  outerFree : D.IsLTwoFour → ∀ σ : MulAut ↥A, σ * σ = 1 → (∀ y : ↥A, (y : G) ∈ Y → σ y = y) →
    ∃ l ∈ L, ∀ z : ↥A, (z : G) ∈ L → ((σ z : ↥A) : G) = l * z * l⁻¹
  sym : D.IsLTwoFour → ∃ (D' : Subgroup G) (s x : G), Y = D' ⊔ W ∧ s ∈ A ∧
    rightConjugate W s = L ∧ rightConjugate L s = W ∧ rightConjugate D' s = D' ∧ x ∈ L ∧
    orderOf x = 5 ∧ AS76b.layerCentralizer A (D' ⊔ zpowers x) = W ∧
    NoInvolutoryCentralizing A (D' ⊔ zpowers x ⊔ W)

end Stages

@[expose] def Step74 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A), AS76b.Hyp31 A →
    RankTwoClassicalEvenType (rankTwoQuot A) → ∃ R T : Subgroup G, ∃ g : G, Choice74 D R T g

@[expose] def Step75 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A) (R T : Subgroup G)
    (g : G), AS76b.Hyp31 A → RankTwoClassicalEvenType (rankTwoQuot A) → Choice74 D R T g →
      ∃ Y W L : Subgroup G, Levi75 D T Y W L

@[expose] def Step76 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A)
    (R T Y W L : Subgroup G) (g : G), RankTwoHyp G A → AS76b.Hyp31 A →
    RankTwoClassicalEvenType (rankTwoQuot A) → Choice74 D R T g → Levi75 D T Y W L →
    (∀ (G' : Type) [Group G'] [Finite G'] (A' : Subgroup G'), Nat.card G' < Nat.card G →
      RankTwoHyp G' A' → standardComponentOddCore G' = ⊥ →
        ¬ RankTwoClassicalEvenType (rankTwoQuot A')) → False

@[expose] def ClassicalHypII : Prop :=
  ∀ (A : Type) [Group A] [Finite A], commutator A = ⊤ →
    RankTwoClassicalEvenType (A ⧸ center A) → AS76b.HypII A

@[expose] def OrthogonalHypIIOdd : Prop :=
  ∀ (A : Type) [Group A] [Finite A], commutator A = ⊤ → Odd (Nat.card (center A)) →
    ∀ n m : ℕ, 4 ≤ n → (StatedClassicalModel (A ⧸ center A) .POmegaPlus n 2 m ∨
      StatedClassicalModel (A ⧸ center A) .POmegaMinus n 2 m) → AS76b.HypII A

@[expose] def ClassicalHypIICover : Prop :=
  ∀ (A : Type) [Group A] [Finite A], commutator A = ⊤ →
    (StatedClassicalModel (A ⧸ center A) .PSU 4 2 1 ∨
      StatedClassicalModel (A ⧸ center A) .PSU 6 2 1 ∨
      StatedClassicalModel (A ⧸ center A) .POmegaPlus 4 2 1) → AS76b.HypII A

@[expose] def ClassicalEvenMultiplier : Prop :=
  ∀ (A : Type) [Group A] [Finite A], commutator A = ⊤ →
    RankTwoClassicalEvenType (A ⧸ center A) → Even (Nat.card (center A)) →
      StatedClassicalModel (A ⧸ center A) .PSU 4 2 1 ∨
        StatedClassicalModel (A ⧸ center A) .PSU 6 2 1 ∨
        StatedClassicalModel (A ⧸ center A) .PSp 3 2 1 ∨
        StatedClassicalModel (A ⧸ center A) .POmegaPlus 4 2 1

@[expose] def ClassicalOutCommOdd : Prop :=
  ∀ (A : Type) [Group A] [Finite A], commutator A = ⊤ →
    RankTwoClassicalEvenType (A ⧸ center A) →
      Odd (Nat.card (commutator (outerAutomorphismGroup A)))

@[expose] def ClassicalCentralizerCharTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X], RankTwoClassicalEvenType X → ∀ u : X, orderOf u = 2 →
    CFSG.IsCharacteristicP 2 (centralizer ({u} : Set X))

@[expose] def ClassicalPrimaryPerfect : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    CFSG.Open.IsQuasisimple ↥A →
    Odd (Nat.card (center A)) → 4 ≤ D.q → ∀ x : G, D.IsPrimary x →
      x ∈ CFSG.Quasithin.perfectCore (A ⊓ centralizer ({x} : Set G))

section Levi

variable {G : Type} [Group G] {A : Subgroup G}

@[expose] def NoNormalTwo (H : Subgroup G) : Prop :=
  ∀ Q : Subgroup G, Q ≤ H → IsPGroup 2 ↥Q → H ≤ normalizer (Q : Set G) → Q = ⊥

structure LeviChoice (D : ClassicalModel A) (p : G) (W Y : Subgroup G) : Prop where
  W_le : W ≤ Y
  Y_le : Y ≤ A ⊓ centralizer (D.alpha p : Set G)
  W_type : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = D.q ∧
    Nonempty (↥W ≃* Matrix.SpecialLinearGroup (Fin 2) F)
  alpha_le : D.alpha p ≤ AS76b.layerCentralizer A Y
  quasisimple : CFSG.Open.IsQuasisimple ↥(AS76b.layerCentralizer A Y)
  oddCenter : Odd (Nat.card (center ↥(AS76b.layerCentralizer A Y)))
  levi : D.LeviType (AS76b.layerCentralizer A Y)
  noInv : NoInvolutoryCentralizing A (Y ⊔ AS76b.layerCentralizer A Y)
  diag : D.IsLinearFiveFour → ∃ y ∈ A ⊓ centralizer (Y : Set G), (∃ k : ℕ, y ^ 3 ^ k = 1) ∧
    ¬ ∃ l ∈ AS76b.layerCentralizer A Y, ∀ x ∈ AS76b.layerCentralizer A Y,
      y * x * y⁻¹ * (l * x * l⁻¹)⁻¹ ∈
        (center ↥(AS76b.layerCentralizer A Y)).map (AS76b.layerCentralizer A Y).subtype
  outerFree : D.IsLTwoFour → ∀ σ : MulAut ↥A, σ * σ = 1 → (∀ y : ↥A, (y : G) ∈ Y → σ y = y) →
    ∃ l ∈ AS76b.layerCentralizer A Y, ∀ z : ↥A, (z : G) ∈ AS76b.layerCentralizer A Y →
      ((σ z : ↥A) : G) = l * z * l⁻¹
  sym : D.IsLTwoFour → ∃ (D' : Subgroup G) (s x : G), Y = D' ⊔ W ∧ s ∈ A ∧
    rightConjugate W s = AS76b.layerCentralizer A Y ∧
    rightConjugate (AS76b.layerCentralizer A Y) s = W ∧ rightConjugate D' s = D' ∧
    x ∈ AS76b.layerCentralizer A Y ∧ orderOf x = 5 ∧
    AS76b.layerCentralizer A (D' ⊔ zpowers x) = W ∧
    NoInvolutoryCentralizing A (D' ⊔ zpowers x ⊔ W)

@[expose] def LeviChoiceFor (fam : Family) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A), D.family = fam →
    CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) → 4 ≤ D.q →
      ∀ p : G, D.IsPrimary p → ∃ W Y : Subgroup G, LeviChoice D p W Y

@[expose] def LeviRigid (A : Subgroup G) (p : G) (Y : Subgroup G) : Prop :=
  ∀ h p' : G, p' ∈ rightConjugate A h → orderOf p' = 2 →
    Y ≤ normalizer (rightConjugate A h : Set G) →
    CFSG.Quasithin.perfectCore (A ⊓ centralizer ({p} : Set G)) =
      CFSG.Quasithin.perfectCore (rightConjugate A h ⊓ centralizer ({p'} : Set G)) →
    NoNormalTwo (rightConjugate A h ⊓ centralizer (Y : Set G))

@[expose] def LeviRigidFor (fam : Family) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A), D.family = fam →
    CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) → 4 ≤ D.q →
      ∀ (p : G) (W Y : Subgroup G), D.IsPrimary p → LeviChoice D p W Y → LeviRigid A p Y

end Levi

@[expose] def LinearLeviChoice : Prop := LeviChoiceFor .linear

@[expose] def UnitaryLeviChoice : Prop := LeviChoiceFor .unitary

@[expose] def SymplecticLeviChoice : Prop := LeviChoiceFor .symplectic

@[expose] def OrthPlusLeviChoice : Prop := LeviChoiceFor .orthPlus

@[expose] def OrthMinusLeviChoice : Prop := LeviChoiceFor .orthMinus

end CFSG.ComponentClassification.RankTwoClassical
