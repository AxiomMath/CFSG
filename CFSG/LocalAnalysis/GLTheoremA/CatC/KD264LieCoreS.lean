module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms

@[expose] def multIdx (p : ℕ) : TauCeti.LieTypeIndex → Prop
  | .A n q => p ∣ n + 1 ∧ p ∣ q.card - 1
  | .twistedA n q => p ∣ n + 1 ∧ p ∣ q.card + 1
  | .E6 q => p = 3 ∧ 3 ∣ q.card - 1
  | .twistedE6 q => p = 3 ∧ 3 ∣ q.card + 1
  | _ => False

@[expose] def KD264MultLie (p : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ d : TauCeti.ValidLieTypeIndex,
      Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      p ≠ d.1.characteristic → IsPGroup p (Subgroup.center K) →
      Subgroup.center K ≠ ⊥ → multIdx p d.1

structure KD264CoreHyp (p : ℕ) (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    (A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)) (m c : ℕ) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  elem : IsElemAbelian p A
  card : Nat.card A = p ^ m
  one_le_c : 1 ≤ c
  c_le_two : c ≤ 2
  four_le : 4 ≤ m + c
  notChev : ¬ IsChevSimple p (TauCeti.CFSGIndex.lie d).Group
  notK2 : ¬ k2Lie p d.1
  notK3 : ¬ (p = 3 ∧ k3Lie d.1)
  dvd : p ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group
  low : ∀ k, i5LowBound p d.1 k → k ≤ m
  noMult : ¬ multIdx p d.1 →
    CFSG.Open.pRank p (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) ≤ m ∧
    ∀ a ∈ A, a ∉ (MulAut.conj :
        (TauCeti.CFSGIndex.lie d).Group →* MulAut (TauCeti.CFSGIndex.lie d).Group).range →
      ∀ E : Subgroup (TauCeti.CFSGIndex.lie d).Group, E ≤ fixSubgroup a → IsElemAbelian p E →
        CFSG.Open.pRank p E + 1 ≤ m
  field : p = 3 → ∀ a ∈ A, a ∉ innAutDerived (TauCeti.CFSGIndex.lie d).Group →
    ∀ k, i5FieldBound d.1 k → k + 1 ≤ m
  mrj : ∀ β ∈ A, β ≠ 1 → ∀ J : Subgroup (TauCeti.CFSGIndex.lie d).Group,
    GLAPComponent p (fixSubgroup β) J →
    ∀ e : TauCeti.ValidLieTypeIndex,
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* (TauCeti.CFSGIndex.lie e).Group) →
      lpEpsIdx p e.1 → p - 1 ≤ m

@[expose] def KD264CoreGoal (p : ℕ) (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    (A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)) (m c : ℕ) : Prop :=
  (∃ F ≤ A, IsGood p F ∧ p ^ 3 ≤ Nat.card F * p ^ c) ∨
    (p = 3 ∧ isTrialityD4Big d.1 ∧ m = 3 ∧ c = 1 ∧
      ∃ a ∈ A, a ∉ innAutDerived (TauCeti.CFSGIndex.lie d).Group)

@[expose] def KD264CoreS (p : ℕ) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group]
    (A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)) (m c : ℕ),
    KD264CoreHyp p d A m c → KD264CoreGoal p d A m c

@[expose] def KD264PL (p : ℕ) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group],
    p ≠ d.1.characteristic →
    ∀ β : MulAut (TauCeti.CFSGIndex.lie d).Group, β ^ p = 1 → β ≠ 1 →
      ∀ P : Subgroup (TauCeti.CFSGIndex.lie d).Group, P ≤ fixSubgroup β → ⁅P, P⁆ = P →
        p ∣ Nat.card P →
        ∃ J : Subgroup (TauCeti.CFSGIndex.lie d).Group,
          GLAPComponent p (fixSubgroup β) J ∧ p ∣ Nat.card J

@[expose] def KD264BS (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (A : Subgroup (MulAut S)),
    IsElemAbelian p A → p ^ 3 ≤ Nat.card A →
    (∀ F ≤ A, Nat.card F = p ^ 2 → ¬ IsGood p F) →
    ∀ β ∈ A, β ≠ 1 → ∀ J : Subgroup S, GLAPComponent p (fixSubgroup β) J → p ∣ Nat.card J →
      ∀ i : TauCeti.CFSGIndex, Nonempty (↥J ⧸ Subgroup.center ↥J ≃* i.Group) →
        A ≤ CFSG.GroupActions.subgroupStabAut J ∧
        (∃ D : Subgroup (MulAut i.Group), IsElemAbelian p D ∧ Nat.card A = p * Nat.card D) ∧
        ∀ e : TauCeti.ValidLieTypeIndex, i = .lie e → p ≠ e.1.characteristic →
          (p = 3 ∧ ov2Idx e.1) ∨
          (p = 3 ∧
            (∃ q : TauCeti.PrimePower, (e.1 = .A 1 q ∨ e.1 = .twistedA 2 q) ∧ q.card = 8) ∧
            ∃ a ∈ A, ∃ ha : a ∈ CFSG.GroupActions.subgroupStabAut J,
              centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J ⟨a, ha⟩) ∉
                innAutDerived (↥J ⧸ Subgroup.center ↥J)) ∨
          (p = 5 ∧ (e.1 = .suzuki 2 ∨ e.1 = .tits)) ∨
          (lpEpsIdx p e.1 ∧ Nat.card A = p ^ 3)

@[expose] def KD264ExcNoGood (p : ℕ) : Prop :=
  ∀ (e : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie e).Group],
    p ≠ e.1.characteristic → p ∣ Nat.card (TauCeti.CFSGIndex.lie e).Group →
    ∀ D : Subgroup (MulAut (TauCeti.CFSGIndex.lie e).Group),
      IsElemAbelian p D → p ^ 2 ≤ Nat.card D →
      (∀ a ∈ D, a ≠ 1 → GLAPLayer p (fixSubgroup a) = ⊥) →
      (p = 3 ∧ ov2Idx e.1) ∨
      (p = 3 ∧ (∃ q : TauCeti.PrimePower, (e.1 = .A 1 q ∨ e.1 = .twistedA 2 q) ∧ q.card = 8) ∧
        ∃ a ∈ D, a ∉ innAutDerived (TauCeti.CFSGIndex.lie e).Group) ∨
      (p = 5 ∧ (e.1 = .suzuki 2 ∨ e.1 = .tits)) ∨
      (lpEpsIdx p e.1 ∧ Nat.card D = p ^ 2)

@[expose] def KD264Amb (p : ℕ) : Prop :=
  (∀ (n : ℕ) (hn : 5 ≤ n), (n = 5 ∨ n = 6 ∨ n = 8) → ¬ (p = 3 ∧ (n = 6 ∨ n = 8)) →
    ∀ D : Subgroup (MulAut (TauCeti.CFSGIndex.alternating n hn).Group),
      IsElemAbelian p D → Nat.card D ≤ p) ∧
  (p = 7 → ∀ e : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, e.1 = .A 1 q ∧ q.card = 7) →
    ∀ D : Subgroup (MulAut (TauCeti.CFSGIndex.lie e).Group), IsElemAbelian p D → Nat.card D ≤ p)

@[expose] def KD264CaseY1 : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group]
    (A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)),
    KD264CoreHyp 3 d A 3 1 → ¬ ov2Idx d.1 →
    ((∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q) →
      A ≤ innAutDerived (TauCeti.CFSGIndex.lie d).Group) →
    ∃ F ≤ A, Nat.card F = 9 ∧ IsGood 3 F

@[expose] def KD264CaseY2 : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group]
    (A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)) (m : ℕ),
    KD264CoreHyp 3 d A m 1 → ¬ ov2Idx d.1 →
    ((∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q) →
      A ≤ innAutDerived (TauCeti.CFSGIndex.lie d).Group) →
    ∀ β ∈ A, ∀ J : Subgroup (TauCeti.CFSGIndex.lie d).Group, GLAPComponent 3 (fixSubgroup β) J →
    ∀ e : TauCeti.ValidLieTypeIndex,
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* (TauCeti.CFSGIndex.lie e).Group) →
      compRel d.1 e.1 →
      (∃ q : TauCeti.PrimePower, (e.1 = .A 1 q ∨ e.1 = .twistedA 2 q) ∧ q.card = 8) →
      (∀ x ∈ innAutDerived (TauCeti.CFSGIndex.lie d).Group, x ^ 3 = 1 → β * x = x * β →
        ∀ hx : x ∈ CFSG.GroupActions.subgroupStabAut J,
          centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J ⟨x, hx⟩) ∈
            innAutDerived (↥J ⧸ Subgroup.center ↥J)) →
      A ≤ CFSG.GroupActions.subgroupStabAut J →
      (∃ D : Subgroup (MulAut (TauCeti.CFSGIndex.lie e).Group),
        IsElemAbelian 3 D ∧ Nat.card A = 3 * Nat.card D) →
      (∃ a ∈ A, ∃ ha : a ∈ CFSG.GroupActions.subgroupStabAut J,
        centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J ⟨a, ha⟩) ∉
          innAutDerived (↥J ⧸ Subgroup.center ↥J)) →
      ∃ F ≤ A, Nat.card F = 9 ∧ IsGood 3 F

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
