module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Triple

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

structure Red113 {Q : Type} [Group Q] [Finite Q] (B L : Subgroup Q) (x : Q) (T : Subgroup Q) :
    Prop where
  tri : Triple113 B L x
  hO : GLAPPrimeCore 3 Q = ⊥
  isL2 : IsL2TwoPowOdd ↥L
  hidx_all : ∀ M : Subgroup Q, IsComponentOf M ⊤ →
    (Subgroup.normalizer (M : Set Q)).relIndex B ∣ 3
  hmax : ∀ E : Subgroup Q, IsElemAbelian 3 E →
    (∃ S : Subgroup Q, S ≠ ⊥ ∧ IsPGroup 2 S ∧ E ≤ Subgroup.normalizer (S : Set Q)) →
      Nat.card E ≤ Nat.card B
  hR1 : ∀ R : Subgroup Q, IsPGroup 2 R → B ≤ Subgroup.normalizer (R : Set Q) →
    R ≤ Subgroup.centralizer ((t113K B L : Subgroup Q) : Set Q) → R = ⊥
  T_ne : T ≠ ⊥
  T_two : IsPGroup 2 T
  T_norm : B ≤ Subgroup.normalizer (T : Set Q)
  T_min : ∀ T' : Subgroup Q, T' ≤ T → B ≤ Subgroup.normalizer (T' : Set Q) → T' = ⊥ ∨ T' = T
  T_elem : IsElemAbelian 2 T
  T_card : Nat.card T ≤ 4

@[expose] def MinT113 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (B S : Subgroup Q), IsElemAbelian 3 B → S ≠ ⊥ → IsPGroup 2 S →
    B ≤ Subgroup.normalizer (S : Set Q) →
    ∃ T : Subgroup Q, T ≠ ⊥ ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set Q) ∧
      (∀ T' : Subgroup Q, T' ≤ T → B ≤ Subgroup.normalizer (T' : Set Q) → T' = ⊥ ∨ T' = T) ∧
      IsElemAbelian 2 T ∧ Nat.card T ≤ 4

@[expose] def CaseJK113 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (B L : Subgroup Q) (x : Q) (T : Subgroup Q),
    Red113 B L x T → T ≤ Subgroup.normalizer ((t113K B L : Subgroup Q) : Set Q) → False

@[expose] def CaseJgt113 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (B L : Subgroup Q) (x : Q) (T : Subgroup Q),
    Red113 B L x T → ¬ T ≤ Subgroup.normalizer ((t113K B L : Subgroup Q) : Set Q) → False

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
