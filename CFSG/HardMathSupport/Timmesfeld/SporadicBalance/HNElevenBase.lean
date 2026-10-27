
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HNElevenInputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PrimeCommute
public import CFSG.Sporadic.HNOddCore.InvDefs
public import CFSG.Sporadic.HNSchreier.ThreeSpec
public import CFSG.Sporadic.HNSchreier.Order
public import Mathlib.GroupTheory.Perm.Centralizer
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions

@[expose] public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open Equiv Subgroup
open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.He.Native
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native

@[expose] def sigma11 : Perm (Fin 12) :=
  List.formPerm [(0 : Fin 12), 1, 11, 4, 2, 3, 6, 8, 9, 10, 5]

theorem sigma11_isCycle : sigma11.IsCycle :=
  List.isCycle_formPerm (by decide) (by decide)

theorem sigma11_support_card : sigma11.support.card = 11 := by
  rw [sigma11, List.support_formPerm_of_nodup _ (by decide) (by decide)]
  decide

theorem sigma11_cycleType : sigma11.cycleType = {11} := by
  rw [sigma11_isCycle.cycleType, sigma11_support_card]

theorem card_centralizer_sigma11 :
    Nat.card (centralizer ({sigma11} : Set (Perm (Fin 12)))) = 11 := by
  rw [Equiv.Perm.nat_card_centralizer, sigma11_cycleType]
  simp

theorem prep_sigma11 : PRep 12 (natArr cyc11) sigma11 := by
  unfold PRep
  decide

@[expose] def elevenJ : JH := hWordJ elevenWord

theorem elevenJ_mem : elevenJ ∈ HJ := hWordJ_mem elevenWord

theorem thetaHom_inj :
    Function.Injective thetaHom :=
  Subtype.val_injective.comp thetaJ.injective

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
