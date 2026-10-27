module

public import CFSG.ClassicalInvolution.Q3.TL4InductDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

section Cit3


@[expose] def PlusLeaf (X : ℕ → ℕ → Prop) (n : ℕ) : Prop :=
  CIT3Below n → TightBelowRPlus 3 n → X 3 n

@[expose] def ThmD2StepR (r n : ℕ) : Prop :=
  CIT3Below n → TightBelowRPlus r n → TC.Thin.ThmDAbsBelow r (n + 1)

@[expose] def ThmD1StepR (r n : ℕ) : Prop :=
  CIT3Below n → TightBelowRPlus r n → TC.Thin.ThmDAbsBelow r (n + 1) → ThmD1RBelow r (n + 1)

@[expose] def Thm6StepR (r n : ℕ) : Prop :=
  CIT3Below n → TightBelowRPlus r n → Thm6RBelow r (n + 1)

@[expose] def Thm5StepR (r n : ℕ) : Prop :=
  CIT3Below n → TightBelowRPlus r n → Thm5RBelowF r (n + 1)

@[expose] def TwinStepR (r n : ℕ) : Prop :=
  CIT3Below n → TightBelowRPlus r n → r = 3 → PhilipHall.Frame.Thm1RTwinLiftSetEBelow (n + 1)

@[expose] def OddLeafStep (n : ℕ) : Prop :=
  CIT3Below n → TightBelowRPlus 3 n → TightOddLeaf n

@[expose] def ConnLeafStep (n : ℕ) : Prop :=
  CIT3Below n → TightBelowRPlus 3 n → TightConnLeaf n

@[expose] def E3LeafStep (n : ℕ) : Prop :=
  CIT3Below n → TightBelowRPlus 3 n → TightE3Leaf n

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
