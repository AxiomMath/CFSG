module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Not9

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section LemL

variable {Y : Type} [Group Y] [Finite Y]

@[expose] def p23SecFamV (R V : Subgroup Y) : Set (Subgroup (SecQuot (rLayerSub (Om R) V))) :=
  {L | ∃ R' ∈ RSet (Om R), R' ≤ Subgroup.centralizer (V : Set Y) ∧ L = secImage (rLayerSub (Om R) V) R'}

@[expose] def P23E7LemL (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
        ∀ Z : Subgroup Y, P23ZData t u e Z → ∀ V : Subgroup Y, V ≤ Z → V ≠ ⊥ →
          ∀ f₁ ∈ p23Orb Z t e, ∀ f₂ ∈ p23Orb Z t e, f₁ ≠ f₂ → V ≤ aSub R Z f₁ → V ≤ aSub R Z f₂ →
            TC.Thin.pSpan (p23SecFamV R V) = ⊤ ∧
            ∃ I : TC.Thin.AEIdentOn (p23SecFamV R V) 7 AE.e64Sets AE.e64Sub,
              (∀ x ∈ commutator ↥(TC.Thin.pSpan (p23SecFamV R V)), I.φ x = 1 → x = 1) ∧
              ∀ f ∈ p23Orb Z t e, V ≤ aSub R Z f →
                secImage (rLayerSub (Om R) V) (rLayer (Om R) f ⊓ rLayerSub (Om R) V) ⊓
                  Subgroup.center (SecQuot (rLayerSub (Om R) V)) = ⊥

@[expose] def P23E7LemLId (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
        ∀ Z : Subgroup Y, P23ZData t u e Z → ∀ V : Subgroup Y, V ≤ Z → V ≠ ⊥ →
          ∀ f₁ ∈ p23Orb Z t e, ∀ f₂ ∈ p23Orb Z t e, f₁ ≠ f₂ → V ≤ aSub R Z f₁ → V ≤ aSub R Z f₂ →
            TC.Thin.pSpan (p23SecFamV R V) = ⊤ ∧
            Nonempty (TC.Thin.AEIdentOn (p23SecFamV R V) 7 AE.e64Sets AE.e64Sub) ∧
              ∀ f ∈ p23Orb Z t e, V ≤ aSub R Z f →
                secImage (rLayerSub (Om R) V) (rLayer (Om R) f ⊓ rLayerSub (Om R) V) ⊓
                  Subgroup.center (SecQuot (rLayerSub (Om R) V)) = ⊥

variable {n : ℕ} in
theorem p23E7LemLId_of_lemL (h : P23E7LemL n) : P23E7LemLId n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hE hZ Z hZd V hVZ hV1 f₁ hf₁ f₂ hf₂ hne h₁ h₂
  obtain ⟨hgen, I, -, ha⟩ := h hcit hP Y R S t K' W u e g hc hno hE hZ Z hZd V hVZ hV1 f₁ hf₁ f₂ hf₂ hne h₁ h₂
  exact ⟨hgen, ⟨I⟩, ha⟩

end LemL

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
