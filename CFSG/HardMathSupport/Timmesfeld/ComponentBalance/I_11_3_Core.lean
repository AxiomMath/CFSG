module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Defs
public import CFSG.Open.GLBDefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

@[expose] def NoL2RankBound : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], GLAPPrimeCore 3 Q = ⊥ → ∀ B L : Subgroup Q,
    IsElemAbelian 3 B → IsComponentOf L ⊤ → IsL2TwoPowOdd ↥L →
    (Subgroup.normalizer (L : Set Q)).relIndex B = 3 →
    (∀ E : Subgroup Q, IsElemAbelian 3 E → E ≤ (⨆ g ∈ B, GLBConj g L) ⊔ B →
      Nat.card E ≤ Nat.card B) → False

@[expose] def NoL2Reduced : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], GLAPPrimeCore 3 Q = ⊥ → ∀ B L : Subgroup Q,
    IsElemAbelian 3 B → IsComponentOf L ⊤ → IsL2TwoPowOdd ↥L →
    (Subgroup.normalizer (L : Set Q)).relIndex B = 3 →
    (∀ M : Subgroup Q, IsComponentOf M ⊤ → (Subgroup.normalizer (M : Set Q)).relIndex B ∣ 3) →
    (∀ E : Subgroup Q, IsElemAbelian 3 E →
      (∃ S : Subgroup Q, S ≠ ⊥ ∧ IsPGroup 2 S ∧ E ≤ Subgroup.normalizer (S : Set Q)) →
        Nat.card E ≤ Nat.card B) →
    (∃ S : Subgroup Q, S ≠ ⊥ ∧ IsPGroup 2 S ∧ B ≤ Subgroup.normalizer (S : Set Q)) →
    (∀ R : Subgroup Q, IsPGroup 2 R → B ≤ Subgroup.normalizer (R : Set Q) →
      R ≤ Subgroup.centralizer ((⨆ g ∈ B, GLBConj g L : Subgroup Q) : Set Q) → R = ⊥) →
    False

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
