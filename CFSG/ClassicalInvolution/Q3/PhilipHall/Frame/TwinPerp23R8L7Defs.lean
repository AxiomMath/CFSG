module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemL
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLFam

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

section Leaves

structure L7Ctx (n : ℕ) (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K' W : Subgroup Y) (u e g : Y) (Z : Subgroup Y) (f : Y) : Prop where
  cfg : P23Cfg n Y R S t K' W u e g
  noExit : ¬ SecNoExit R e
  ae5 : SecAE R u 5
  ae6 : SecAE R e 6
  zdata : P23ZData t u e Z
  hf : f ∈ p23Orb Z t e
  ne : f ≠ e
  v1 : aSub R Z e ⊓ aSub R Z f ≠ ⊥

@[expose] def L7CoreTwo (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y) (Z : Subgroup Y) (f : Y), L7Ctx n Y R S t K' W u e g Z f →
      SecCoresTwoGroup (Om R) (aSub R Z e ⊓ aSub R Z f)

@[expose] def L7NoW (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y) (Z : Subgroup Y) (f : Y), L7Ctx n Y R S t K' W u e g Z f →
      ¬ ∃ W' : Subgroup (SecQuot (rLayerSub (Om R) (aSub R Z e ⊓ aSub R Z f))),
        WSet (p23SecFamV R (aSub R Z e ⊓ aSub R Z f)) = {W'}

@[expose] def L7NoLong (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y) (Z : Subgroup Y) (f : Y), L7Ctx n Y R S t K' W u e g Z f →
      ∀ K ∈ p23SecFamV R (aSub R Z e ⊓ aSub R Z f),
        ∀ τ : SecQuot (rLayerSub (Om R) (aSub R Z e ⊓ aSub R Z f)), IsUniqueInvolution K τ →
          ¬ LongFundSetE3 K τ

end Leaves

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7
