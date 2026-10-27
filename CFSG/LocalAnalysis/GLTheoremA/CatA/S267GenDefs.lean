module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

structure GenHyp (Q : TauCeti.LieTypeIndex → Prop) (p q : ℕ) {Ω : Type} [Group Ω] [Finite Ω]
    (S B : Subgroup Ω) : Prop where
  pPrime : p.Prime
  pOdd : p ≠ 2
  qPrime : q.Prime
  qOdd : q ≠ 2
  qp : q ≠ p
  kGroup : CFSG.Open.IsKGroup Ω
  normal : S.Normal
  perfect : ⁅S, S⁆ = S
  core : GLAPPrimeCore p ↥S = ⊥
  lie : ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = q ∧ Q d.1 ∧
    Nonempty (PSimple p S ≃* (TauCeti.CFSGIndex.lie d).Group)
  elem : IsElemAbelian p B
  sup : S ⊔ B = ⊤
  twoLocal : p ^ GLATwoLocalRank p Ω ≤ Nat.card B
  four : p ^ 4 ≤ Nat.card B
  cent : Nat.card ↥(B ⊓ centModSubgroup p S) = p
  not81 : ¬ (p = 3 ∧ Nat.card B = 3 ^ 4)

@[expose] def S267FactGenOn (Q : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (p q : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B : Subgroup Ω), GenHyp Q p q S B →
    S267ConcA12 p S B

variable {Ω : Type} [Group Ω] [Finite Ω]

@[expose] def InFrakB (p : ℕ) (S B B' : Subgroup Ω) : Prop :=
  IsElemAbelian p B' ∧ Nat.card ↥(B' ⊓ centModSubgroup p S) = p ∧
    (B' = B ∨ (Nat.card B ≤ Nat.card B' ∧ ∃ R : Subgroup Ω, R ≠ ⊥ ∧ IsPGroup 2 R ∧
      B' ≤ Subgroup.normalizer (R : Set Ω)))

@[expose] def InTriple (p : ℕ) (S B B' : Subgroup Ω) (d : Ω) (J : Subgroup Ω) : Prop :=
  InFrakB p S B B' ∧ d ∈ B' ∧ d ∉ centModSubgroup p S ∧
    GLAPComponent p (S ⊓ Subgroup.centralizer ({d} : Set Ω)) J

@[expose] def IsMaxTriple (p : ℕ) (S B B' : Subgroup Ω) (d : Ω) (J : Subgroup Ω) : Prop :=
  InTriple p S B B' d J ∧ ∀ (B'' : Subgroup Ω) (d' : Ω) (J' : Subgroup Ω),
    InTriple p S B B'' d' J' → Nat.card J' ≤ Nat.card J

@[expose] def GenI112 (p : ℕ) (S B : Subgroup Ω) : Prop :=
  ∀ (B' : Subgroup Ω) (b : Ω) (L : Subgroup Ω), IsElemAbelian p B' → Nat.card B ≤ Nat.card B' →
    b ∈ B' → b ∉ centModSubgroup p S →
    GLAPComponent p (S ⊓ Subgroup.centralizer ({b} : Set Ω)) L →
    ¬ B' ≤ Subgroup.normalizer (L : Set Ω) →
    p = 3 ∧ (Subgroup.normalizer (L : Set Ω)).relIndex B' = 3 ∧
      Nat.card ↥(B' ⊓ Subgroup.normalizer (L : Set Ω)) ≤
        9 * Nat.card ↥(B' ⊓ Subgroup.centralizer (L : Set Ω)) ∧
      (∃ e ∈ L, e ^ 3 = 1 ∧ e ∉ Subgroup.centralizer (L : Set Ω) ∧
        ∃ R : Subgroup Ω, R ≤ L ∧ R ≠ ⊥ ∧ IsPGroup 2 R ∧ e ∈ Subgroup.normalizer (R : Set Ω)) ∧
      ∀ y ∈ B', y ∉ Subgroup.normalizer (L : Set Ω) → ∀ K : Subgroup Ω,
        GLAPComponent 3 (closureIn L B' ⊓ Subgroup.centralizer ({y} : Set Ω)) K →
          Nat.card K < Nat.card L

structure OddLie (p : ℕ) (T : Type) [Group T] (d : TauCeti.ValidLieTypeIndex) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  iso : Nonempty (T ≃* (TauCeti.CFSGIndex.lie d).Group)
  charOdd : d.1.characteristic ≠ 2
  ne : p ≠ d.1.characteristic

@[expose] def GenGood : Prop :=
  ∀ (p : ℕ) (T : Type) [Group T] [Finite T] (d : TauCeti.ValidLieTypeIndex), OddLie p T d →
    p ∣ Nat.card T → ∀ A : Subgroup (MulAut T), IsElemAbelian p A → p ^ 2 ≤ Nat.card A →
      (∃ a ∈ A, a ≠ 1 ∧ GLAPLayer p (fixSubgroup a) ≠ ⊥) ∨
        (KD264Lie.lpEpsIdx p d.1 ∧ Nat.card A = p ^ 2)

@[expose] def GenCompQuasiOn (Q : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (p : ℕ) (T : Type) [Group T] [Finite T] (d : TauCeti.ValidLieTypeIndex), OddLie p T d →
    Q d.1 → ∀ x : MulAut T, x ^ p = 1 → x ≠ 1 → ∀ J : Subgroup T,
      GLAPComponent p (fixSubgroup x) J → CFSG.Open.IsComponentOf J (fixSubgroup x)

@[expose] def GenCompChevOn (Q : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (p : ℕ) (T : Type) [Group T] [Finite T] (d : TauCeti.ValidLieTypeIndex), OddLie p T d →
    Q d.1 → ∀ x : MulAut T, x ^ p = 1 → x ≠ 1 → ∀ J : Subgroup T,
      GLAPComponent p (fixSubgroup x) J → IsChevSimple d.1.characteristic (↥J ⧸ Subgroup.center ↥J)

@[expose] def GenPlaneCompOn (Q : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (p : ℕ) (T : Type) [Group T] [Finite T] (d : TauCeti.ValidLieTypeIndex), OddLie p T d →
    Q d.1 → ∀ P : Subgroup (MulAut T), IsElemAbelian p P → Nat.card P = p ^ 2 →
      ∀ J : Subgroup T, ¬ ∀ x ∈ P, x ≠ 1 → GLAPComponent p (fixSubgroup x) J

@[expose] def GenLpEpsLocal : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ e : TauCeti.ValidLieTypeIndex, KD264Lie.lpEpsIdx p e.1 → e.1.characteristic ≠ 2 →
      Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie e).Group) →
        (p - 2) + CFSG.Open.pRank p (⊤ : Subgroup (Subgroup.center K)) ≤ GLATwoLocalRank p K

@[expose] def GenChevThreeLocal : Prop :=
  ∀ (r : ℕ), r.Prime → r ≠ 2 → r ≠ 3 → ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
    IsChevSimple r L → 1 ≤ GLATwoLocalRank 3 L

@[expose] def GenStep1On (Q : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (p q : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B : Subgroup Ω), GenHyp Q p q S B →
    ∃ (d : Ω) (J : Subgroup Ω), InTriple p S B B d J

@[expose] def GenStepCentOn (Q : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (p q : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B : Subgroup Ω), GenHyp Q p q S B →
    ∀ (d : Ω) (J : Subgroup Ω), d ^ p = 1 → d ∉ centModSubgroup p S →
      GLAPComponent p (S ⊓ Subgroup.centralizer ({d} : Set Ω)) J →
      ∀ b : Ω, CentMod p J b → b ∈ Subgroup.centralizer (J : Set Ω)

@[expose] def GenStepI112On (Q : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (p q : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B : Subgroup Ω), GenHyp Q p q S B → GenI112 p S B

@[expose] def GenStep3On (Q : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (p q : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B : Subgroup Ω), GenHyp Q p q S B →
    GenI112 p S B → ∀ (B' : Subgroup Ω) (d : Ω) (J : Subgroup Ω), InTriple p S B B' d J →
      ¬ B' ≤ Subgroup.normalizer (J : Set Ω) →
      ∃ B'' : Subgroup Ω, InTriple p S B B'' d J ∧ B'' ≤ Subgroup.normalizer (J : Set Ω)

@[expose] def GenStep4On (Q : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (p q : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B : Subgroup Ω), GenHyp Q p q S B →
    GenI112 p S B → ∀ (B' : Subgroup Ω) (d : Ω) (J : Subgroup Ω), IsMaxTriple p S B B' d J →
      B' ≤ Subgroup.normalizer (J : Set Ω) → ∀ d₁ ∈ B', CentMod p J d₁ →
        d₁ ∉ centModSubgroup p S → GLAPComponent p (S ⊓ Subgroup.centralizer ({d₁} : Set Ω)) J

@[expose] def GenStep5On (Q : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (p q : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B : Subgroup Ω), GenHyp Q p q S B →
    ∀ (B' : Subgroup Ω) (d : Ω) (J : Subgroup Ω), InTriple p S B B' d J →
      B' ≤ Subgroup.normalizer (J : Set Ω) →
      (∀ d₁ ∈ B', CentMod p J d₁ → d₁ ∉ centModSubgroup p S →
        GLAPComponent p (S ⊓ Subgroup.centralizer ({d₁} : Set Ω)) J) →
      Nat.card ↥(B' ⊓ centModSubgroup p J) = p ^ 2

@[expose] def GenStep6On (Q : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (p q : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B : Subgroup Ω), GenHyp Q p q S B →
    ∀ (B' : Subgroup Ω) (d : Ω) (J : Subgroup Ω), InTriple p S B B' d J →
      B' ≤ Subgroup.normalizer (J : Set Ω) → Nat.card ↥(B' ⊓ centModSubgroup p J) = p ^ 2 →
      ∃ E : Subgroup Ω, E ≤ B' ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
        B' ⊓ centModSubgroup p J ≤ E ∧
        GLAPLayer p (J ⊓ Subgroup.centralizer (E : Set Ω)) ≠ ⊥

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
