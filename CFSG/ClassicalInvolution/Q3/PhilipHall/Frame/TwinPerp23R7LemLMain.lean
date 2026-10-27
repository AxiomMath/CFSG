module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLCen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLFam

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Leaves

structure LemLCtx (n : ℕ) (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K' W : Subgroup Y) (u e g : Y) (Z V : Subgroup Y) (f₁ f₂ : Y) : Prop where
  cfg : P23Cfg n Y R S t K' W u e g
  noExit : ¬ SecNoExit R e
  ecase : ECase1 R W e
  zstar : u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y))
  zdata : P23ZData t u e Z
  vz : V ≤ Z
  v1 : V ≠ ⊥
  hf₁ : f₁ ∈ p23Orb Z t e
  hf₂ : f₂ ∈ p23Orb Z t e
  ne : f₁ ≠ f₂
  h₁ : V ≤ aSub R Z f₁
  h₂ : V ≤ aSub R Z f₂

@[expose] def LemLCoreTwo (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y) (Z V : Subgroup Y) (f₁ f₂ : Y), LemLCtx n Y R S t K' W u e g Z V f₁ f₂ →
      SecCoresTwoGroup (Om R) V

@[expose] def LemLNoW (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y) (Z V : Subgroup Y) (f₁ f₂ : Y), LemLCtx n Y R S t K' W u e g Z V f₁ f₂ →
      ¬ ∃ W' : Subgroup (SecQuot (rLayerSub (Om R) V)), WSet (p23SecFamV R V) = {W'}

@[expose] def LemLNoLong (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y) (Z V : Subgroup Y) (f₁ f₂ : Y), LemLCtx n Y R S t K' W u e g Z V f₁ f₂ →
      ∀ K ∈ p23SecFamV R V, ∀ τ : SecQuot (rLayerSub (Om R) V), IsUniqueInvolution K τ →
        ¬ LongFundSetE3 K τ

@[expose] def LemLEZ (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
        OmegaOneCenter (rLayer (Om R) e) e

@[expose] def E64NoS3 : Prop := ¬ HasS3Quot ↥AE.e64Sub

end Leaves

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
