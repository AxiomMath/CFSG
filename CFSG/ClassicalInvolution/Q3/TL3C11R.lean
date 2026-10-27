module

public import CFSG.ClassicalInvolution.Q3.TL3C11

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

@[expose] def TightClsR (r : ℕ) (Y : Type) [Group Y] (R : Subgroup Y) (S : Sylow 2 R) (_t : Y) :
    Prop :=
  Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))) ∧ TightSelfGen R ∧ TightOddFree Y

theorem tightClsR_three_iff {Y : Type} [Group Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} :
    TightClsR 3 Y R S t ↔ TightCls Y R S t :=
  Iff.rfl

@[expose] def TightBelowR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n → ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → TightClsR r Y R S t → TightEx Y R S t ∨ GoodThreeElement R t

theorem tightBelowR_three_iff {n : ℕ} : TightBelowR 3 n ↔ TightBelow n :=
  Iff.rfl

section Cit3


structure TightLargeHypR (r n : ℕ) (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y)
    (S : Sylow 2 R) (t : Y) : Prop where
  below : CIT3Below n
  tbelow : TightBelowR r n
  card : Nat.card Y = n
  datum : TightDatum R S t
  cls : TightClsR r Y R S t
  notInO2 : ¬ TightInO2 t
  fstar : TightFStarQuasisimple Y
  large : ¬ TwoSubgroupsFourGenerated (genFittingFStar Y)
  edge : ¬ TightEdgeless R
  center : Subgroup.center Y = ⊥

theorem TightLargeHyp.toR {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : TightLargeHyp n Y R S t) : TightLargeHypR 3 n Y R S t :=
  ⟨h.below, h.tbelow, h.card, h.datum, h.cls, h.notInO2, h.fstar, h.large, h.edge, h.center⟩

@[expose] def TightOddLeafR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → TightOddCent t

@[expose] def TightConnLeafR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → TightOddCent t →
      Disconnected.DConnected (CoreAssembly.conjClass (tightCore R))

@[expose] def TightSepLeafR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → TightOddCent t → TC.SepHyp (CoreAssembly.conjClass (tightCore R))

theorem tightOddLeaf_of_R {n : ℕ} (h : TightOddLeafR 3 n) : TightOddLeaf n :=
  fun Y _ _ R S t hL => h Y R S t hL.toR

theorem tightConnLeaf_of_R {n : ℕ} (h : TightConnLeafR 3 n) : TightConnLeaf n :=
  fun Y _ _ R S t hL => h Y R S t hL.toR

theorem tightSepLeaf_of_R {n : ℕ} (h : TightSepLeafR 3 n) : TightSepLeaf n :=
  fun Y _ _ R S t hL => h Y R S t hL.toR

end Cit3

end CFSG.ClassicalInvolution.Q3
