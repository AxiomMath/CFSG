module

public import CFSG.LargeExtraspecial.S12Main

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CFSG.Open

@[expose] def Insp5Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
    g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ≠ S.z → 5 ≤ S.width → t ∈ S.Lbar g →
    IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 → S.S12Standing g t → ¬ S.IsReducible12 →
    ((S.IsNondeg12 g ∧ CFSG.Timmesfeld.Outcome (S.Xbar12 g)) ∨
      (¬ S.IsNondeg12 g ∧
        S12FischerConclusion (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g))) →
    S.S12Case1 g t ∨ (S.IsNondeg12 g ∧ S.S12Case2 g t) ∨ S.S12IndexCert g ∨
      (¬ S.IsNondeg12 g ∧ S.S12FuseCert g t) ∨ S.S12GenCert g ∨ Nat.card (S.Lbar g) ≤ 4 ∨
      S.S12SpSixSpin g

@[expose] def Insp4Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
    g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ≠ S.z → S.width = 4 →
    (∀ P : Subgroup S.Mbar, IsPGroup 2 P → Nat.card P ≤ 2 ^ 7) → 25920 ∣ Nat.card S.Mbar →
    t ∈ S.Lbar g → IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 → S.S12Standing g t →
    ¬ S.IsReducible12 →
    ((S.IsNondeg12 g ∧ CFSG.Timmesfeld.Outcome (S.Xbar12 g)) ∨
      (¬ S.IsNondeg12 g ∧
        S12FischerConclusion (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g))) →
    S.S12Case1 g t ∨ (S.IsNondeg12 g ∧ S.S12Case2 g t) ∨ S.S12IndexCert g ∨
      (¬ S.IsNondeg12 g ∧ S.S12FuseCert g t) ∨ S.S12GenCert g ∨ Nat.card (S.Lbar g) ≤ 4 ∨
      S.S12SpSixSpin g

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G} [IsSimpleGroup G]

theorem timmesfeld_12_16_of_inspAt (hRI : RootInvolutionComponentsInput.{0})
    (hARS : CFSG.Timmesfeld.ARSInput) (hTri : FischerTrialityInput)
    (hFischer : S12FischerStatement) (h36 : Timmesfeld36Input) (hSL : S12SL4ModuleInput)
    {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 4 ≤ S.width)
    {t : S.O} (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hInsp : S.S12Standing g t → ¬ S.IsReducible12 →
      ((S.IsNondeg12 g ∧ CFSG.Timmesfeld.Outcome (S.Xbar12 g)) ∨
        (¬ S.IsNondeg12 g ∧
          S12FischerConclusion (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g))) →
      S.S12Case1 g t ∨ (S.IsNondeg12 g ∧ S.S12Case2 g t) ∨ S.S12IndexCert g ∨
        (¬ S.IsNondeg12 g ∧ S.S12FuseCert g t) ∨ S.S12GenCert g ∨ Nat.card (S.Lbar g) ≤ 4 ∨
        S.S12SpSixSpin g) :
    S.IsReducible12 ∨ S.S12OmegaPlusEight ∨ S.S12GammaLResidual g t ∨ S.S12SpSixSpin g := by
  by_cases hred : S.IsReducible12
  · exact Or.inl hred
  have hS := (s12Standing_or hRI haQ hne hn ht htA).resolve_left hred
  have hcls :=
    (timmesfeld_12_3_classification hRI hARS hTri hFischer haQ hne hn ht htA).resolve_left hred
  have hn3 : 3 ≤ S.width := by omega
  rcases hInsp hS hred hcls with hC1 | ⟨-, hC2⟩ | hI | ⟨hdeg, hF⟩ | hG | hL4 | hSp
  · rcases timmesfeld_12_15 hSL haQ hne hn hS hC1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases timmesfeld_12_14 h36 haQ hne hn hS hC2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inl (isReducible12_of_indexCert haQ hne hn3 ht htA hI)
  · exact Or.inl (isReducible12_of_fuseCert haQ hne hn3 ht htA hdeg hF)
  · exact Or.inl (isReducible12_of_genCert haQ hne hn hG)
  · exact (false_of_card_Lbar_le haQ hne hn hL4).elim
  · exact Or.inr (Or.inr (Or.inr hSp))

theorem timmesfeld_12_16_of_insp5 (hRI : RootInvolutionComponentsInput.{0})
    (hARS : CFSG.Timmesfeld.ARSInput) (hTri : FischerTrialityInput)
    (hFischer : S12FischerStatement) (hInsp : Insp5Input)
    (h36 : Timmesfeld36Input) (hSL : S12SL4ModuleInput)
    {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 5 ≤ S.width)
    {t : S.O} (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) :
    S.IsReducible12 ∨ S.S12OmegaPlusEight ∨ S.S12GammaLResidual g t ∨ S.S12SpSixSpin g :=
  timmesfeld_12_16_of_inspAt hRI hARS hTri hFischer h36 hSL haQ hne (by omega) ht htA
    (hInsp G S g t haQ hne hn ht htA)

theorem timmesfeld_12_16_of_insp4 (hRI : RootInvolutionComponentsInput.{0})
    (hARS : CFSG.Timmesfeld.ARSInput) (hTri : FischerTrialityInput)
    (hFischer : S12FischerStatement) (hInsp : Insp4Input)
    (h36 : Timmesfeld36Input) (hSL : S12SL4ModuleInput) (hw : S.width = 4)
    (hP : ∀ P : Subgroup S.Mbar, IsPGroup 2 P → Nat.card P ≤ 2 ^ 7)
    (hM : 25920 ∣ Nat.card S.Mbar)
    {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    {t : S.O} (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) :
    S.IsReducible12 ∨ S.S12OmegaPlusEight ∨ S.S12GammaLResidual g t ∨ S.S12SpSixSpin g :=
  timmesfeld_12_16_of_inspAt hRI hARS hTri hFischer h36 hSL haQ hne (by omega) ht htA
    (hInsp G S g t haQ hne hw hP hM ht htA)

end Setting

end CFSG.LargeExtraspecial
