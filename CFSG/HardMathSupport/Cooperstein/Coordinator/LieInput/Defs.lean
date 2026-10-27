module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.Open CFSG.AGLEmbedding

@[expose] def centerIn {Γ : Type} [Group Γ] (L : Subgroup Γ) : Subgroup Γ :=
  (Subgroup.center ↥L).map L.subtype

@[expose] def LeviStructure {Γ : Type} [Group Γ] (L R : Subgroup Γ) : Prop :=
  ∃ (n : ℕ) (C : Fin n → Subgroup Γ) (D : Subgroup Γ),
    R ≤ D ∧ D ≤ L ⊓ Subgroup.normalizer (R : Set Γ) ∧ Group.IsSolvable ↥D ∧
    (∀ i, C i ≤ L ⊓ Subgroup.normalizer (R : Set Γ) ∧ CFSG.IsQuasisimple ↥(C i) ∧
      IsClassicalTwoOrG2 (↥(C i) ⧸ Subgroup.center ↥(C i)) ∧
      D ≤ Subgroup.normalizer ((C i ⊔ R : Subgroup Γ) : Set Γ)) ∧
    (∀ i j, i ≠ j → C i ≤ Subgroup.centralizer (C j : Set Γ)) ∧
    L ⊓ Subgroup.normalizer (R : Set Γ) = D ⊔ ⨆ i, C i

@[expose] def IsChevOver {Γ : Type} [Group Γ] (Yi R : Subgroup Γ) : Prop :=
  ∃ (Q : Type) (_ : Group Q) (φ : ↥Yi →* Q), Function.Surjective φ ∧
    φ.ker = R.subgroupOf Yi ∧ CFSG.IsQuasisimple Q ∧ IsClassicalTwoOrG2 (Q ⧸ Subgroup.center Q)

@[expose] def LeviModR {Γ : Type} [Group Γ] (L R : Subgroup Γ) : Prop :=
  ∃ (n : ℕ) (Yc : Fin n → Subgroup Γ) (D : Subgroup Γ),
    R ≤ D ∧ D ≤ L ⊓ Subgroup.normalizer (R : Set Γ) ∧ Group.IsSolvable ↥D ∧
    (∀ i, R ≤ Yc i ∧ Yc i ≤ L ⊓ Subgroup.normalizer (R : Set Γ) ∧ IsChevOver (Yc i) R ∧
      D ≤ Subgroup.normalizer (Yc i : Set Γ)) ∧
    (∀ i j, i ≠ j → ⁅Yc i, Yc j⁆ ≤ R) ∧
    L ⊓ Subgroup.normalizer (R : Set Γ) = D ⊔ ⨆ i, Yc i

@[expose] def CentralizerInRadical {Γ : Type} [Group Γ] (L R : Subgroup Γ) : Prop :=
  ∀ x ∈ L, (∀ r ∈ R, x * r = r * x) → x ∈ R ⊔ centerIn L

@[expose] def LieInputStatement : Prop := (∀ (Γ : Type) [Group Γ] [Finite Γ] (L R : Subgroup Γ),
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → R = pCoreOf 2 (L ⊓ Subgroup.normalizer (R : Set
    Γ)) → LeviStructure L R ∧ LeviModR L R) ∧ (∀ (Γ : Type) [Group Γ] [Finite Γ] (L R :
    Subgroup Γ), IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → R = pCoreOf 2 (L ⊓
    Subgroup.normalizer (R : Set Γ)) → L ⊓ Subgroup.normalizer (R : Set Γ) ≠ L →
    CentralizerInRadical L R)

@[expose] def LieInputSimple : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsClassicalTwoOrG2 Y → ∀ R : Subgroup Y,
    R = pCoreOf 2 ((⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y)) →
      LeviStructure (⊤ : Subgroup Y) R ∧
        ((⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y) ≠ ⊤ →
          ∀ x : Y, (∀ r ∈ R, x * r = r * x) → x ∈ R)

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
