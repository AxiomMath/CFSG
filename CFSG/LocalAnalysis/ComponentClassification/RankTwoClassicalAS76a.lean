module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDefs
public import CFSG.LocalAnalysis.ABGTheoremB.Basic
public import Mathlib.GroupTheory.Frattini

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped Matrix

section Groups

variable {G : Type} [Group G]

@[expose] def conjCommuting (A : Subgroup G) (p : G) : Set G :=
  {x | ∃ b ∈ A, x = b * p * b⁻¹ ∧ Commute x p}

@[expose] def jGroup (A : Subgroup G) (p : G) : Subgroup G :=
  CFSG.ABGTheoremB.pCoreIn 2 (A ⊓ centralizer ({p} : Set G)) ⊓
    centralizer (conjCommuting A p)

@[expose] def IsAPart (A : Subgroup G) (t p : G) : Prop :=
  p ∈ A ∧ (∃ k : ℕ, p ^ 2 ^ k = 1) ∧ t⁻¹ * p ∈ centralizer (A : Set G)

@[expose] def APartsFused (A T : Subgroup G) : Prop :=
  ∀ t ∈ T, t ≠ 1 → ∀ t' ∈ T, t' ≠ 1 → ∀ p p' : G, IsAPart A t p → IsAPart A t' p' →
    ∃ a ∈ A, a * p * a⁻¹ = p'

@[expose] def APartsLe (A T J : Subgroup G) : Prop :=
  ∀ t ∈ T, ∀ p : G, IsAPart A t p → p ∈ J

abbrev nonidentity (J : Subgroup G) : Set G := {j | j ∈ J ∧ j ≠ 1}

@[expose] def RegularOn (A J : Subgroup G) (S : Set G) : Prop :=
  (∀ j ∈ S, ∀ j' ∈ S, ∃ a ∈ A ⊓ normalizer (J : Set G), a * j * a⁻¹ = j') ∧
    ∀ a ∈ A ⊓ normalizer (J : Set G), ∀ j ∈ S, a * j * a⁻¹ = j → a ∈ centralizer (J : Set G)

@[expose] def AutCyclic (A J : Subgroup G) (n : ℕ) : Prop :=
  (A ⊓ centralizer (J : Set G)).relIndex (A ⊓ normalizer (J : Set G)) = n ∧
    ∃ y ∈ A ⊓ normalizer (J : Set G), Odd (orderOf y) ∧
      ∀ a ∈ A ⊓ normalizer (J : Set G), ∃ k : ℕ, (y ^ k)⁻¹ * a ∈ centralizer (J : Set G)

@[expose] def AutDiagonal (A J U W : Subgroup G) (n : ℕ) : Prop :=
  (A ⊓ centralizer (J : Set G)).relIndex (A ⊓ normalizer (J : Set G)) = n * n ∧
    ∃ y₁ ∈ A ⊓ normalizer (J : Set G), ∃ y₂ ∈ A ⊓ normalizer (J : Set G),
      y₁ ∈ centralizer (U : Set G) ∧ y₂ ∈ centralizer (W : Set G) ∧
      ∀ a ∈ A ⊓ normalizer (J : Set G), ∃ k₁ k₂ : ℕ,
        (y₁ ^ k₁ * y₂ ^ k₂)⁻¹ * a ∈ centralizer (J : Set G)

@[expose] def JSylowAt (A : Subgroup G) (p : G) : Prop :=
  ∀ x ∈ A ⊓ centralizer ({p} : Set G), x ∈ centralizer (conjCommuting A p) →
    (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ CFSG.ABGTheoremB.pCoreIn 2 (A ⊓ centralizer ({p} : Set G))

end Groups

inductive Letter
  | a
  | b
  | c

section Types

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  {H : Subgroup (GL ι K)}

@[expose] def LetterHolds (L : Letter) (ℓ : ℕ) (φ : (ι → K) → K) : Prop :=
  match L with
  | .a => Even ℓ ∧ ∀ v, φ v = 0
  | .b => Odd ℓ
  | .c => Even ℓ ∧ ∃ v, φ v ≠ 0

@[expose] def HasSuzukiType (e : rankTwoQuot A ≃* StatedProj H) (Φ : GL ι K → (ι → K) → K)
    (x : G) (L : Letter) (ℓ : ℕ) : Prop :=
  orderOf x = 2 ∧ ∃ M : GL ι K, Represents e x M ∧ orderOf M = 2 ∧ commRank M = ℓ ∧
    LetterHolds L ℓ (Φ M)

end Types

@[expose] def sympForm (n : ℕ) (K : Type) [Field K] (v w : Fin n ⊕ Fin n → K) : K :=
  v ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 *ᵥ w)

namespace ClassicalModel

variable {G : Type} [Group G] {A : Subgroup G}

@[expose] def HasRank : ClassicalModel A → G → ℕ → Prop
  | @linear _ _ _ _ _ _ _ _ _ _ _ _ e, x, ℓ => IsInvolutionOfRank e x ℓ
  | @unitary _ _ _ _ _ _ _ _ _ _ _ e, x, ℓ => IsInvolutionOfRank e x ℓ
  | @symplectic _ _ _ _ _ _ _ _ _ _ _ _ e, x, ℓ => IsInvolutionOfRank e x ℓ
  | @orthPlus _ _ _ _ _ _ _ _ _ _ _ e, x, ℓ => IsInvolutionOfRank e x ℓ
  | @orthMinus _ _ _ _ _ _ _ _ _ _ _ _ _ _ e, x, ℓ => IsInvolutionOfRank e x ℓ

@[expose] def SuzukiType : ClassicalModel A → G → Letter → ℕ → Prop
  | @linear .., _, _, _ => False
  | @unitary .., _, _, _ => False
  | @symplectic _ _ _ n _ _ _ _ K _ _ _ e, x, L, ℓ =>
      HasSuzukiType e (fun (M : GL (Fin n ⊕ Fin n) K) v =>
        sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)) x L ℓ
  | @orthPlus _ _ _ n _ _ _ K _ _ _ e, x, L, ℓ =>
      HasSuzukiType e (fun (M : GL (Fin n ⊕ Fin n) K) v => StatedQuadPlus n K
        (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ v)) x L ℓ
  | @orthMinus _ _ _ n _ _ _ K _ _ _ b c _ e, x, L, ℓ =>
      HasSuzukiType e (fun (M : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) v =>
        StatedQuadMinus n K b c (((M : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) - 1) *ᵥ v)) x L ℓ

end ClassicalModel

section Hyp

variable {G : Type} [Group G]

structure Hyp221 (A T : Subgroup G) : Prop where
  quasisimple : CFSG.Open.IsQuasisimple ↥A
  le_normalizer : T ≤ normalizer (A : Set G)
  le_sup : T ≤ A ⊔ centralizer (A : Set G)
  centralizer_two : ∀ c ∈ (T ⊔ A) ⊓ centralizer (A : Set G), (∃ k : ℕ, c ^ 2 ^ k = 1) →
    c ^ 2 = 1
  inf_eq_bot : T ⊓ centralizer (A : Set G) = ⊥
  elem : IsElemAbelian 2 T
  four_le : 4 ≤ Nat.card T
  tight : TightlyEmbedded (T.subgroupOf (T ⊔ A))
  normalizer_cond : Nat.card T = 4 ∨ ∀ x ∈ T ⊔ A,
    rightConjugate T x ⊓ normalizer (T : Set G) ≤ centralizer (T : Set G)

variable {A : Subgroup G}

@[expose] def Case1 (D : ClassicalModel A) (p : G) : Prop :=
  jGroup A p = D.alpha p ∧ RegularOn A (jGroup A p) (nonidentity (jGroup A p)) ∧
    AutCyclic A (jGroup A p) (D.q - 1)

@[expose] def Case23 (D : ClassicalModel A) (p : G) : Prop :=
  ∃ (ℓ : ℕ) (a b : G),
    ((1 < ℓ ∧ D.SuzukiType p .b ℓ ∧ D.SuzukiType a .a (ℓ - 1)) ∨
      (D.SuzukiType p .c ℓ ∧ D.SuzukiType a .a ℓ)) ∧ D.SuzukiType b .b 1 ∧
    jGroup A p = D.alpha a ⊔ D.alpha b ∧ p ∉ D.alpha a ∧ p ∉ D.alpha b ∧
    RegularOn A (jGroup A p) {j | j ∈ jGroup A p ∧ j ∉ D.alpha a ∧ j ∉ D.alpha b} ∧
    AutDiagonal A (jGroup A p) (D.alpha a) (D.alpha b) (D.q - 1)

@[expose] def Case4 (D : ClassicalModel A) (p : G) : Prop :=
  (∃ ℓ : ℕ, D.SuzukiType p .c ℓ) ∧ RegularOn A (jGroup A p) (nonidentity (jGroup A p)) ∧
    AutCyclic A (jGroup A p) (D.q - 1)

@[expose] def CaseII (D : ClassicalModel A) (T : Subgroup G) : Prop :=
  T ≤ A ∧ Nat.card T = 4 ∧ D.q = 2

end Hyp

@[expose] def Conclusion222 {G : Type} [Group G] (A T : Subgroup G) (q : ℕ) (I : G → Prop)
    (II : G → Prop) : Prop :=
  Odd (Nat.card (center A)) ∧ APartsFused A T ∧
    ∀ t ∈ T, t ≠ 1 → ∀ p : G, IsAPart A t p →
      (APartsLe A T (jGroup A p) ∧ Nat.card T ≤ q ∧ I p) ∨ II t

@[expose] def Linear222 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A T : Subgroup G) (D : ClassicalModel A),
    D.family = .linear → Hyp221 A T →
    Conclusion222 A T D.q (Case1 D) fun t => CaseII D T ∧ D.HasRank t 2 ∧
      ∀ S : Subgroup G, IsSylowOf 2 S (A ⊓ centralizer ({t} : Set G)) → T ≤ S →
        T ≤ (frattini ↥S).map S.subtype

@[expose] def Unitary222 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A T : Subgroup G) (D : ClassicalModel A),
    D.family = .unitary → Hyp221 A T → Conclusion222 A T D.q (Case1 D) fun _ => False

@[expose] def Symplectic222 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A T : Subgroup G) (D : ClassicalModel A),
    D.family = .symplectic → Hyp221 A T →
    Conclusion222 A T D.q (fun p => Case1 D p ∨ Case23 D p) fun t =>
      CaseII D T ∧ D.SuzukiType t .c 2 ∧ ∃ a ∈ A ⊓ centralizer ({t} : Set G),
        a ∈ normalizer (T : Set G) ∧ a ∉ centralizer (T : Set G)

@[expose] def OrthPlus222 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A T : Subgroup G) (D : ClassicalModel A),
    D.family = .orthPlus → Hyp221 A T →
    Conclusion222 A T D.q (fun p => Case1 D p ∨ Case4 D p) fun _ => False

@[expose] def OrthMinus222 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A T : Subgroup G) (D : ClassicalModel A),
    D.family = .orthMinus → Hyp221 A T →
    Conclusion222 A T D.q (fun p => Case1 D p ∨ Case4 D p) fun _ => False

@[expose] def SymplecticJSylow (L : Letter) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = .symplectic → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) →
      4 ≤ D.q → ∀ (p : G) (ℓ : ℕ), D.SuzukiType p L ℓ → JSylowAt A p

@[expose] def OrthPlusJSylow (L : Letter) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = .orthPlus → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) →
      4 ≤ D.q → ∀ (p : G) (ℓ : ℕ), D.SuzukiType p L ℓ → JSylowAt A p

@[expose] def OrthMinusJSylow (L : Letter) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = .orthMinus → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) →
      4 ≤ D.q → ∀ (p : G) (ℓ : ℕ), D.SuzukiType p L ℓ → JSylowAt A p

@[expose] def Classical222 : Prop :=
  Linear222 ∧ Unitary222 ∧ Symplectic222 ∧ OrthPlus222 ∧ OrthMinus222

@[expose] def ClassicalJSylow : Prop :=
  (∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A), D.family = .linear →
      CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) → 4 ≤ D.q → ∀ (p : G) (ℓ : ℕ),
      D.HasRank p ℓ → JSylowAt A p) ∧ (∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
      D.family = .unitary → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) → 4 ≤ D.q → ∀ (p
      : G) (ℓ : ℕ), D.HasRank p ℓ → JSylowAt A p) ∧ (∀ L : Letter, SymplecticJSylow L) ∧
    (∀ L : Letter, OrthPlusJSylow L) ∧ ∀ L : Letter, OrthMinusJSylow L

end CFSG.ComponentClassification.RankTwoClassical
