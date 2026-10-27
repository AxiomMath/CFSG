module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def E6FourAutRank5 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (J B : Subgroup Γ) (lab : GLALabel),
    LabelOf J lab → lab.tag = .E6 → lab.n = 2 → Subgroup.center ↥J = ⊥ →
    B ≤ Subgroup.normalizer (J : Set Γ) → IsElemAbelian 5 B →
      Nat.card B ≤ 5 ^ 4 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set Γ))

@[expose] def E6FourLocal5 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (J : Subgroup Γ) (lab : GLALabel),
    LabelOf J lab → lab.tag = .E6 → lab.n = 2 → Subgroup.center ↥J = ⊥ →
      ∃ E U : Subgroup Γ, E ≤ J ∧ U ≤ J ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set Γ) ∧
        IsElemAbelian 5 E ∧ 5 ^ 4 ≤ Nat.card E

@[expose] def E6FourCent5 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (J K B : Subgroup Γ) (x : Γ) (lab : GLALabel),
    LabelOf J lab → lab.tag = .E6 → lab.n = 2 → Subgroup.center ↥J = ⊥ →
    B ≤ Subgroup.normalizer (J : Set Γ) → IsElemAbelian 5 B → x ∈ B →
    x ∉ Subgroup.centralizer (J : Set Γ) →
    IsComponentOf K (J ⊓ Subgroup.centralizer ({x} : Set Γ)) → B ≤ Subgroup.normalizer (K : Set Γ) →
    5 ^ 3 * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Γ)) ≤ Nat.card B →
      LabelOf K ⟨.twD, 4, 2⟩ ∨ LabelOf K ⟨.A, 5, 2⟩

@[expose] def SubcompField : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (L K : Subgroup Γ) (y : Γ) (labL labK : GLALabel) (p : ℕ),
    p.Prime → p ≠ 2 → y ^ p = 1 → y ∈ Subgroup.normalizer (L : Set Γ) →
    y ∉ Subgroup.centralizer (L : Set Γ) → MarkedInnDiag L y labL →
    IsComponentOf K (L ⊓ Subgroup.centralizer ({y} : Set Γ)) → LabelOf K labK →
    (labK.tag = .twD → 3 ≤ labK.rank) → labL.n ∣ labK.n

@[expose] def UnitaryNo5 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (L K : Subgroup Γ) (y : Γ) (labL : GLALabel),
    y ∈ Subgroup.normalizer (L : Set Γ) → y ^ 5 = 1 → y ∉ Subgroup.centralizer (L : Set Γ) →
    labL.tag = .twA → labL.n = 2 → MarkedInnDiag L y labL →
    IsComponentOf K (L ⊓ Subgroup.centralizer ({y} : Set Γ)) →
      ¬ LabelOf K ⟨.twD, 4, 2⟩ ∧ ¬ LabelOf K ⟨.A, 5, 2⟩

@[expose] def OmegaMinus4Comp : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (L K : Subgroup Γ) (y : Γ) (labL : GLALabel),
    y ∈ Subgroup.normalizer (L : Set Γ) → y ^ 5 = 1 → y ∉ Subgroup.centralizer (L : Set Γ) →
    labL.tag = .twD → labL.n = 2 → MarkedInnDiag L y labL →
    IsComponentOf K (L ⊓ Subgroup.centralizer ({y} : Set Γ)) →
      (LabelOf K ⟨.twD, 4, 2⟩ → 6 ≤ labL.rank) ∧ ¬ LabelOf K ⟨.A, 5, 2⟩

@[expose] def TwE6Rank5 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (L : Subgroup Γ) (lab : GLALabel),
    LabelOf L lab → lab.tag = .twE6 → lab.n = 2 →
      ∃ E U : Subgroup Γ, E ≤ L ∧ U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set Γ) ∧
        IsElemAbelian 5 E ∧ 5 ^ 5 * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set Γ)) ≤ Nat.card E

@[expose] def OmegaMinusRank5 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (L : Subgroup Γ) (lab : GLALabel),
    LabelOf L lab → lab.tag = .twD → lab.n = 2 → 6 ≤ lab.rank →
      ∃ E U : Subgroup Γ, E ≤ L ∧ U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set Γ) ∧
        IsElemAbelian 5 E ∧ 5 ^ 5 * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set Γ)) ≤ Nat.card E

structure E6FourFacts : Prop where
  aut : E6FourAutRank5
  loc : E6FourLocal5
  cent : E6FourCent5
  field : SubcompField
  uni : UnitaryNo5
  omega : OmegaMinus4Comp
  twE6 : TwE6Rank5
  omegaRank : OmegaMinusRank5

structure E6FourResidualFacts : Prop where
  cent : E6FourCent5
  field : SubcompField
  uni : UnitaryNo5
  omega : OmegaMinus4Comp
  twE6 : TwE6Rank5
  omegaRank : OmegaMinusRank5

end CFSG.LocalAnalysis.GLTheoremA
