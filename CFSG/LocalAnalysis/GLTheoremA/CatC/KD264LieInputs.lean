module

public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.GroupActions.SubgroupStabilizerOuterBound
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms

@[expose] def IsGood (p : ℕ) {S : Type*} [Group S] [Finite S] (F : Subgroup (MulAut S)) : Prop :=
  GLAPLayer p (⨅ f ∈ F, fixSubgroup f) ≠ ⊥

@[expose] def fieldSize : TauCeti.LieTypeIndex → ℕ
  | .A _ q | .twistedA _ q | .B _ q | .C _ q | .D _ q | .twistedD _ q
  | .E6 q | .E7 q | .E8 q | .F4 q | .G2 q | .twistedE6 q | .trialityD4 q => q.card
  | .suzuki k => 2 ^ (2 * k + 1)
  | .reeG2 k => 3 ^ (2 * k + 1)
  | .reeF4 k => 2 ^ (2 * k + 1)
  | .tits => 2

@[expose] def ov2Idx (e : TauCeti.LieTypeIndex) : Prop :=
  fieldSize e = 2

@[expose] def suzRee : TauCeti.LieTypeIndex → Prop
  | .suzuki _ | .reeG2 _ | .reeF4 _ | .tits => True
  | _ => False

@[expose] def lpEpsIdx (p : ℕ) (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower,
    (e = .A (p - 1) q ∧ p ∣ q.card - 1) ∨ (e = .twistedA (p - 1) q ∧ p ∣ q.card + 1)

@[expose] def sameShape : TauCeti.LieTypeIndex → TauCeti.LieTypeIndex → Prop
  | .A n _, .A m _ => n = m
  | .twistedA n _, .twistedA m _ => n = m
  | .B n _, .B m _ => n = m
  | .C n _, .C m _ => n = m
  | .D n _, .D m _ => n = m
  | .twistedD n _, .twistedD m _ => n = m
  | .E6 _, .E6 _ => True
  | .E7 _, .E7 _ => True
  | .E8 _, .E8 _ => True
  | .F4 _, .F4 _ => True
  | .G2 _, .G2 _ => True
  | .twistedE6 _, .twistedE6 _ => True
  | .trialityD4 _, .trialityD4 _ => True
  | .suzuki _, .suzuki _ => True
  | .reeG2 _, .reeG2 _ => True
  | .reeF4 _, .reeF4 _ => True
  | .tits, .tits => True
  | _, _ => False

@[expose] def compRel (d e : TauCeti.LieTypeIndex) : Prop :=
  (e.characteristic = d.characteristic ∧
    (∃ j : ℕ, 1 ≤ j ∧ fieldSize e = fieldSize d ^ j) ∧ (suzRee e → suzRee d)) ∨
  (fieldSize d = 2 ∧
    ((∃ q : TauCeti.PrimePower, e = .A 1 q ∧ q.card = 7) ∨
      (∃ q : TauCeti.PrimePower, e = .twistedA 2 q ∧ q.card = 3))) ∨
  (fieldSize d = 3 ∧ ∃ q : TauCeti.PrimePower, e = .twistedA 3 q ∧ q.card = 2)

@[expose] def compRelC (d : TauCeti.LieTypeIndex) : TauCeti.CFSGIndex → Prop
  | .lie e => compRel d e.1
  | .alternating n _ =>
      (n = 5 ∧ (fieldSize d = 2 ∨ fieldSize d = 4 ∨ fieldSize d = 5)) ∨
      (n = 6 ∧ (fieldSize d = 2 ∨ fieldSize d = 3 ∨ fieldSize d = 9)) ∨
      (n = 8 ∧ fieldSize d = 2)
  | _ => False

@[expose] def subRel (p : ℕ) (d e : TauCeti.LieTypeIndex) : Prop :=
  (sameShape d e ∧ fieldSize e ^ p = fieldSize d) ∨
  ((∃ q : TauCeti.PrimePower, d = .D 4 q) ∧
    (∃ q : TauCeti.PrimePower, e = .trialityD4 q) ∧ fieldSize e ^ p = fieldSize d) ∨
  ((∃ q : TauCeti.PrimePower, e = .A 1 q ∧ q.card = 7) ∧
    (∃ q : TauCeti.PrimePower, d = .A 2 q) ∧ fieldSize d = 2 ^ p) ∨
  ((∃ q : TauCeti.PrimePower, e = .twistedA 2 q ∧ q.card = 3) ∧
    (∃ q : TauCeti.PrimePower, d = .G2 q) ∧ fieldSize d = 2 ^ p) ∨
  ((∃ q : TauCeti.PrimePower, e = .twistedA 3 q ∧ q.card = 2) ∧
    (∃ q : TauCeti.PrimePower, d = .B 2 q) ∧ fieldSize d = 3 ^ p) ∨
  (e = .tits ∧ (∃ k : ℕ, d = .reeF4 k) ∧ fieldSize d = 2 ^ p) ∨
  ((∃ q : TauCeti.PrimePower, e = .A 1 q ∧ q.card = 8) ∧
    (∃ k : ℕ, d = .reeG2 k) ∧ fieldSize d = 3 ^ p)

@[expose] def subRelC (p : ℕ) (d : TauCeti.LieTypeIndex) : TauCeti.CFSGIndex → Prop
  | .lie e => subRel p d e.1
  | .alternating n _ =>
      (n = 5 ∧ (∃ q : TauCeti.PrimePower, d = .A 1 q) ∧
        (fieldSize d = 4 ^ p ∨ fieldSize d = 5 ^ p)) ∨
      (n = 6 ∧ (((∃ q : TauCeti.PrimePower, d = .A 1 q) ∧ fieldSize d = 9 ^ p) ∨
        ((∃ q : TauCeti.PrimePower, d = .B 2 q) ∧ fieldSize d = 2 ^ p))) ∨
      (n = 8 ∧ (∃ q : TauCeti.PrimePower, d = .A 3 q) ∧ fieldSize d = 2 ^ p)
  | _ => False

@[expose] def overEight : TauCeti.LieTypeIndex → Prop
  | .A _ q | .twistedA _ q | .B _ q | .C _ q | .D _ q | .twistedD _ q | .E6 q | .E7 q
  | .E8 q | .F4 q | .G2 q | .twistedE6 q | .trialityD4 q => q.card = 8
  | .reeF4 1 => True
  | _ => False

@[expose] def KD264OutCyc : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ 2 → p ≠ d.1.characteristic →
    ∀ D : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group),
      IsElemAbelian p D →
      Nat.card D ≤ p * Nat.card ↥(D ⊓ innAutDerived (TauCeti.CFSGIndex.lie d).Group)

@[expose] def KD264OuterIdx : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ 2 → p ≠ d.1.characteristic →
    p ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group →
    ¬ (p = 3 ∧
      ((∃ q : TauCeti.PrimePower, (d.1 = .A 1 q ∨ d.1 = .twistedA 2 q) ∧ q.card = 8) ∨
        (∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q))) →
    ¬ (p = 5 ∧ d.1 = .suzuki 2) →
    ∀ β : MulAut (TauCeti.CFSGIndex.lie d).Group, β ^ p = 1 →
      β ∉ innAutDerived (TauCeti.CFSGIndex.lie d).Group →
      ∃ J : Subgroup (TauCeti.CFSGIndex.lie d).Group,
        GLAPComponent p (fixSubgroup β) J ∧ p ∣ Nat.card J ∧
        ∃ i : TauCeti.CFSGIndex, Nonempty (↥J ⧸ Subgroup.center ↥J ≃* i.Group) ∧ subRelC p d.1 i

@[expose] def KD264InnGood : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ 2 → p ≠ d.1.characteristic →
    ¬ (p = 3 ∧ ov2Idx d.1) →
    ¬ (p = 5 ∧ d.1 = .tits) →
    ∀ D : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group),
      IsElemAbelian p D → Nat.card D = p ^ 2 →
      D ≤ innAutDerived (TauCeti.CFSGIndex.lie d).Group →
      (∃ β ∈ D, β ≠ 1 ∧ ∃ P : Subgroup (TauCeti.CFSGIndex.lie d).Group,
        P ≤ fixSubgroup β ∧ ⁅P, P⁆ = P ∧ p ∣ Nat.card P) ∨
      (lpEpsIdx p d.1 ∧
        innAutDerived (TauCeti.CFSGIndex.lie d).Group ⊓
          Subgroup.centralizer (D : Set (MulAut (TauCeti.CFSGIndex.lie d).Group)) = D)

@[expose] def KD264TriInnGood : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex),
    (∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q ∧ 2 < q.card) →
    3 ≠ d.1.characteristic →
    ∀ β ∈ innAutDerived (TauCeti.CFSGIndex.lie d).Group,
      β ^ 3 = 1 → β ≠ 1 →
      ∃ P : Subgroup (TauCeti.CFSGIndex.lie d).Group,
        P ≤ fixSubgroup β ∧ ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P

@[expose] def KD264CompIdx : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ 2 → p ≠ d.1.characteristic →
    ∀ β : MulAut (TauCeti.CFSGIndex.lie d).Group,
      β ∈ innAutDerived (TauCeti.CFSGIndex.lie d).Group → β ^ p = 1 → β ≠ 1 →
      ∀ J : Subgroup (TauCeti.CFSGIndex.lie d).Group,
        GLAPComponent p (fixSubgroup β) J →
        ∃ i : TauCeti.CFSGIndex, Nonempty (↥J ⧸ Subgroup.center ↥J ≃* i.Group) ∧
          compRelC d.1 i ∧
          (p = 3 → ∀ e : TauCeti.ValidLieTypeIndex, i = .lie e →
            (∃ q : TauCeti.PrimePower, (e.1 = .A 1 q ∨ e.1 = .twistedA 2 q) ∧ q.card = 8) →
            fieldSize d.1 = 8 →
            ∀ x ∈ innAutDerived (TauCeti.CFSGIndex.lie d).Group, x ^ 3 = 1 → β * x = x * β →
              ∀ hx : x ∈ CFSG.GroupActions.subgroupStabAut J,
                centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J ⟨x, hx⟩) ∈
                  innAutDerived (↥J ⧸ Subgroup.center ↥J))

@[expose] def i5FieldBound : TauCeti.LieTypeIndex → ℕ → Prop
  | .A n q, k => 3 ∣ n + 1 ∧ 3 ∣ q.card - 1 ∧ k = n - 1
  | .twistedA n q, k => 3 ∣ n + 1 ∧ 3 ∣ q.card + 1 ∧ k = n - 1
  | .E6 q, k => 3 ∣ q.card - 1 ∧ k = 5
  | .twistedE6 q, k => 3 ∣ q.card + 1 ∧ k = 5
  | _, _ => False

@[expose] def KD264I5Field : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ (e : TauCeti.ValidLieTypeIndex) (k : ℕ), i5FieldBound e.1 k →
      Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie e).Group) →
      ∀ β : MulAut K, β ^ 3 = 1 →
        (onCenterQuotient β ∉ innAutDerived (K ⧸ Subgroup.center K)) →
        ∃ E : Subgroup K, E ≤ fixSubgroup β ∧ IsElemAbelian 3 E ∧
          k + CFSG.Open.pRank 3 (Subgroup.center K) ≤ CFSG.Open.pRank 3 E

@[expose] def i5LowBound (p : ℕ) : TauCeti.LieTypeIndex → ℕ → Prop
  | .A n q, k => p ∣ q.card - 1 ∧ k = n - 1
  | .twistedA n q, k => p ∣ q.card + 1 ∧ k = n - 1
  | .E6 q, k => p = 3 ∧ 3 ∣ q.card - 1 ∧ k = 5
  | .twistedE6 q, k => p = 3 ∧ 3 ∣ q.card + 1 ∧ k = 5
  | _, _ => False

@[expose] def KD264I5Low : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 →
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
      ∀ (e : TauCeti.ValidLieTypeIndex) (k : ℕ), i5LowBound p e.1 k →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie e).Group) →
        k + CFSG.Open.pRank p (Subgroup.center K) ≤ CFSG.Open.pRank p (⊤ : Subgroup K)

@[expose] def KD264I5Aut : Prop :=
  ∀ (e : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie e).Group],
    ((∃ q : TauCeti.PrimePower, e.1 = .trialityD4 q ∧ q.p ≠ 3) →
        CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (TauCeti.CFSGIndex.lie e).Group)) ≤ 3) ∧
    ((∃ q : TauCeti.PrimePower, e.1 = .A 1 q ∧ q.card = 8) →
        CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (TauCeti.CFSGIndex.lie e).Group)) ≤ 2) ∧
    ((∃ q : TauCeti.PrimePower, e.1 = .twistedA 2 q ∧ q.card = 8) →
        CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (TauCeti.CFSGIndex.lie e).Group)) ≤ 3)

@[expose] def KD264X1Row : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group],
    ¬ IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group → ¬ k2Lie 3 d.1 → ¬ k3Lie d.1 →
    ov2Idx d.1 →
    ¬ (∃ n : ℕ, ∃ q : TauCeti.PrimePower, d.1 = .twistedA n q ∧ 3 ∣ n + 1) →
    ¬ (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q) →
    ∀ A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group),
      IsElemAbelian 3 A →
      CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) ≤ CFSG.Open.pRank 3 A →
      ∃ F ≤ A, IsElemAbelian 3 F ∧ min 2 (CFSG.Open.pRank 3 A - 1) ≤ CFSG.Open.pRank 3 F ∧
        IsGood 3 F

@[expose] def KD264XUnRow : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group]
    (n : ℕ) (q : TauCeti.PrimePower),
    ¬ IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group → ¬ k2Lie 3 d.1 → ¬ k3Lie d.1 →
    d.1 = .twistedA n q → q.card = 2 → 3 ∣ n + 1 → 8 ≤ n →
    ∀ A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group),
      IsElemAbelian 3 A → n - 1 ≤ CFSG.Open.pRank 3 A →
      ∃ F ≤ A, IsElemAbelian 3 F ∧ 2 ≤ CFSG.Open.pRank 3 F ∧ IsGood 3 F

@[expose] def KD264X2E6Row : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group]
    (q : TauCeti.PrimePower),
    ¬ IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group → ¬ k2Lie 3 d.1 → ¬ k3Lie d.1 →
    d.1 = .twistedE6 q → q.card = 2 →
    ∀ A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group),
      IsElemAbelian 3 A → 5 ≤ CFSG.Open.pRank 3 A →
      ∃ F ≤ A, IsElemAbelian 3 F ∧ CFSG.Open.pRank 3 F = 2 ∧ IsGood 3 F

@[expose] def KD264Y1Row : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group],
    ¬ IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group → ¬ k2Lie 3 d.1 → ¬ k3Lie d.1 →
    CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) ≤ 3 →
    ∀ A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group),
      A ≤ innAutDerived (TauCeti.CFSGIndex.lie d).Group →
      IsElemAbelian 3 A → Nat.card A = 27 →
      ∃ F ≤ A, Nat.card F = 9 ∧ IsGood 3 F

@[expose] def KD264F8Row : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group],
    ¬ IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group → ¬ k2Lie 3 d.1 → ¬ k3Lie d.1 →
    overEight d.1 →
    ¬ (∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q) →
    ¬ (∃ n : ℕ, ∃ q : TauCeti.PrimePower, d.1 = .twistedA n q ∧ 3 ∣ n + 1) →
    ¬ (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q) →
    ∀ A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group),
      IsElemAbelian 3 A → 3 ≤ CFSG.Open.pRank 3 A → CFSG.Open.pRank 3 A ≤ 4 →
      CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) ≤ CFSG.Open.pRank 3 A →
      (∀ a ∈ A, a ∉ (MulAut.conj :
          (TauCeti.CFSGIndex.lie d).Group →* MulAut (TauCeti.CFSGIndex.lie d).Group).range →
        ∀ E : Subgroup (TauCeti.CFSGIndex.lie d).Group,
          E ≤ fixSubgroup a → IsElemAbelian 3 E → CFSG.Open.pRank 3 E + 1 ≤ CFSG.Open.pRank 3 A) →
      ¬ A ≤ innAutDerived (TauCeti.CFSGIndex.lie d).Group →
      ∃ F ≤ A, Nat.card F = 9 ∧ IsGood 3 F

structure KD264LieInputs : Prop where
  outCyc : KD264OutCyc
  outerIdx : KD264OuterIdx
  innGood : KD264InnGood
  triInnGood : KD264TriInnGood
  compIdx : KD264CompIdx
  i5Field : KD264I5Field
  i5Low : KD264I5Low
  i5Aut : KD264I5Aut
  x1Row : KD264X1Row
  xUnRow : KD264XUnRow
  x2E6Row : KD264X2E6Row
  y1Row : KD264Y1Row
  f8Row : KD264F8Row

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
