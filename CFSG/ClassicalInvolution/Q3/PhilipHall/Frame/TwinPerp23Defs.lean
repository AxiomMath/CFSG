module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPfCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Asc77.AscT7BHyp23

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform

section Vocabulary

variable {Y : Type} [Group Y] [Finite Y]

abbrev Om (R : Subgroup Y) : Set (Subgroup Y) := CoreAssembly.conjClass (tightCore R)

abbrev SecQ (R : Subgroup Y) (c : Y) : Type :=
  ↥(coreHull (Om R) c) ⧸ classicalInvolutionOddCore ↥(coreHull (Om R) c)

@[expose] def SecNoExit (R : Subgroup Y) (c : Y) : Prop :=
  NoExit (SecQ R c) (TwinDisc.secFam (Om R) c)

@[expose] def LieOneComp {X : Type} [Group X] {Z : Set (Subgroup X)} (D : OmegaLieU 3 1 Z) (d : ℕ)
    (ε : Bool) : Prop :=
  ∃ h : D.card = 1, ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsOrthTag d ε t n ∧
    CompIs 3 1 (D.kind ⟨0, by omega⟩) t n

@[expose] def SecOrthLift (R : Subgroup Y) (c : Y) (d : ℕ) (ε : Bool) : Prop :=
  ∃ D : OmegaLieU 3 1 (liftFam (TwinDisc.secFam (Om R) c)), LieOneComp D d ε

@[expose] def SecAE (R : Subgroup Y) (c : Y) (m : ℕ) : Prop :=
  Nonempty (TC.Thin.AEIdent (TwinDisc.secFam (Om R) c) m)

@[expose] def ECase1 (R : Subgroup Y) (W : Subgroup Y) (e : Y) : Prop :=
  rLayer (Om R) e ≤ oddCoreOf (rLayer (Om R) e) ⊔ (rLayer (Om R) e ⊓ Subgroup.normalizer (W : Set Y))

@[expose] def YType (R : Subgroup Y) (u e : Y) : Prop :=
  u * e ∈ zStarOf (rLayer (Om R) u) ∨ SecOrthLift R u 5 true ∨
    SecOrthLift R u 6 (!piSign 3 1) ∨ SecAE R u 5

@[expose] def YOrth (R : Subgroup Y) (u : Y) : Prop :=
  SecOrthLift R u 5 true ∨ SecOrthLift R u 6 (!piSign 3 1)

end Vocabulary

section Std

structure P23Std (n : ℕ) (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K' W : Subgroup Y) : Prop where
  perp : PerpHypS n Y R S t
  two : TwoTwins R
  hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)
  hne : K' ≠ tightCore R
  hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))
  htW : t ∈ W
  hS4 : MuIsoS4 (CoreAssembly.conjClass (tightCore R)) W
  hcen : WCentralNontrivial W
  exit : ¬ TwinE4 Y

structure P23Cfg (n : ℕ) (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K' W : Subgroup Y) (u e g : Y) : Prop where
  std : P23Std n Y R S t K' W
  data : Hyp23bData (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W t u e g

end Std

section Steps

@[expose] def P23Setup (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y),
    P23Std n Y R S t K' W →
      ∃ u e g : Y, Hyp23bData (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W t u e g

@[expose] def P23Members (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g →
      (TwinDisc.secFam (Om R) e).Nonempty ∧ (TwinDisc.secFam (Om R) u).Nonempty

@[expose] def P23Two (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g →
      Subgroup.centralizer ({u} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) = ⊤

@[expose] def P23E4Exit (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e →
      ECase1 R W e ∨ SecAE R e 6

@[expose] def P23E4Ident (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → SecNoExit R e →
      ∀ D : OmegaLieU 3 1 (liftFam (TwinDisc.secFam (Om R) e)), LieOneComp D 6 (piSign 3 1)

@[expose] def P23Y5Exit (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R u →
      u * e ∈ zStarOf (rLayer (Om R) u) ∨ SecAE R u 5

@[expose] def P23Y5Ident (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → SecNoExit R u →
      ∀ D : OmegaLieU 3 1 (liftFam (TwinDisc.secFam (Om R) u)),
        LieOneComp D 5 true ∨ LieOneComp D 6 (!piSign 3 1)

@[expose] def P23Alpha (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → YType R u e →
      Odd (Nat.card ↥(alphaOf (Subgroup.closure ({u, t} : Set Y)))) ∧
        ∀ A : Subgroup Y, A ≤ Subgroup.closure ({u * e, u, t} : Set Y) → IsElemAbelian2 A 2 →
          alphaOf A = alphaOf (Subgroup.closure ({u, t} : Set Y))

end Steps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
