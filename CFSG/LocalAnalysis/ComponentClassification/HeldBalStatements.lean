module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeEnd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKNormalMain

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

@[expose] def BalancedInv (X : Type) [Group X] : Prop :=
  ∀ z : X, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set X)) = ⊥

@[expose] def HeldKComponentStepBal : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldEndSetting X L → BalancedInv X →
    ∀ u : X, HeldTwoA L u →
      ((gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X))).IsSubnormal

@[expose] def HeldKNormalStepBal : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldEndSetting X L → BalancedInv X →
    HeldKNormalAt L

@[expose] def HeldEndStepBal : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldSetting X L → BalancedInv X →
    (∀ A : Subgroup X, A ≤ normalizer (L : Set X) → IsFourGroup A → wGroup A = ⊥) →
    IsStandardSubgroup L → Nonempty (L ≃* Blueprint.NativeSporadic.He) →
    pRank 2 ↥(centralizer (L : Set X)) = 1 → False

@[expose] def HeldKStableProper : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldEndSetting X L → BalancedInv X →
    ∀ u : X, HeldTwoA L u → ∀ (a : X) (ha : a ∈ centralizer ({u} : Set X)), orderOf a = 2 →
      a ∈ centralizer (L : Set X) →
      ∀ M : Subgroup ↥(centralizer ({u} : Set X)), IsPComponent 2 M →
        conjugate M ⟨a, ha⟩ = M →
        (gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X)) ≤ M →
        IsPComponent 2 (((gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X))).subgroupOf
          (M ⊓ centralizer ({⟨a, ha⟩} : Set ↥(centralizer ({u} : Set X))))) →
        (pPrimeCore 2 ((gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X)))).index <
          (pPrimeCore 2 M).index → False

@[expose] def HeldKStableCentre : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H → pPrimeCore 2 H = ⊥ →
    ∀ t : H, orderOf t = 2 → ∀ M T : Subgroup H, IsPComponent 2 M → conjugate M t = M →
      T ≤ M ⊓ centralizer ({t} : Set H) →
      IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({t} : Set H))) →
      (pPrimeCore 2 T).index < (pPrimeCore 2 M).index → IsHeldKType ↥T →
      T ⊓ (center ↥M).map M.subtype = ⊥

@[expose] def HeldKSwapped : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldEndSetting X L → BalancedInv X →
    ∀ u : X, HeldTwoA L u → ∀ (a : X) (ha : a ∈ centralizer ({u} : Set X)), orderOf a = 2 →
      a ∈ centralizer (L : Set X) →
      ∀ M : Subgroup ↥(centralizer ({u} : Set X)), IsPComponent 2 M →
        conjugate M ⟨a, ha⟩ ≠ M →
        (gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X)) ≤ M ⊔ conjugate M ⟨a, ha⟩ →
        IsPComponent 2 (((gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X))).subgroupOf
          ((M ⊔ conjugate M ⟨a, ha⟩) ⊓
            centralizer ({⟨a, ha⟩} : Set ↥(centralizer ({u} : Set X))))) → False

end CFSG.ComponentClassification.GrSLit
