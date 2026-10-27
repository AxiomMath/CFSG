module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Blueprint
open CFSG.Blueprint.NativeSporadic
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.Open
open CFSG.RankThree.PartTwo.Sec4 (IsTripleCover)

@[expose] def KGroupLowRank24_12 (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  p.Prime ∧ p ≠ 2 ∧ CFSG.IsQuasisimple K ∧ CFSG.SectionRank.IsKGroupCat K ∧
  (
   (Nonempty (K ≃* alternatingGroup (Fin (2 * p))) ∨
    Nonempty (K ≃* alternatingGroup (Fin (3 * p))) ∨
    StatedClassicalModel K .PSL 2 p 2 ∨
    StatedClassicalModel K .PSL 2 p 3 ∨
    IsPSLType 3 (ZMod p) K ∨
    StatedClassicalModel K .PSU 3 p 1 ∨
    IsPSLType 4 (ZMod p) K ∨
    StatedClassicalModel K .PSU 4 p 1 ∨
    StatedClassicalModel K .PSp 2 p 1) ∨
   (3 < p ∧ ChevalleyExceptionalModel K .G2 p 1) ∨
   (p = 3 ∧
     (StatedClassicalModel K .PSL 2 2 3 ∨
      StatedClassicalModel K .PSL 3 2 2 ∨
      StatedClassicalModel K .PSp 3 2 1 ∨
      ChevalleyExceptionalModel K .trialityD4 2 1 ∨
      ReeTitsModel K .Tits 2 1 ∨
      Nonempty (K ≃* alternatingGroup (Fin 10)) ∨
      Nonempty (K ≃* alternatingGroup (Fin 11)) ∨
      IsSporadic K .M11 ∨
      IsSporadic K .M12 ∨
      IsSporadic K .J3 ∨
      IsSporadic K .McL ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧ IsSLType 3 F K) ∨
      IsTripleCover K (alternatingGroup (Fin 6)) ∨
      IsTripleCover K McL ∨
      (∃ (Y : Type) (_ : Group Y), StatedClassicalModel Y .PSU 4 3 1 ∧ IsTripleCover K Y) ∨
      (∃ (Y : Type) (_ : Group Y), StatedClassicalModel Y .POmegaOdd 3 3 1 ∧ IsTripleCover K Y) ∨
      (∃ (Y : Type) (_ : Group Y), ChevalleyExceptionalModel Y .G2 3 1 ∧ IsTripleCover K Y))) ∨
   (p = 5 ∧
     (SuzukiModel K 2 5 ∨
      ReeTitsModel K .Tits 2 1 ∨
      IsSporadic K .McL ∨
      IsSporadic K .HS ∨
      IsSporadic K .Fi22 ∨
      IsSporadic K .Co1 ∨
      IsSporadic K .Co2 ∨
      IsSporadic K .Co3 ∨
      IsSporadic K .Ly ∨
      IsSporadic K .Ru ∨
      IsSporadic K .B ∨
      IsSporadic K .HN)) ∨
   (p = 7 ∧
     (IsSporadic K .He ∨
      IsSporadic K .ONan ∨
      IsSporadic K .Fi24Prime ∨
      IsSporadic K .M)) ∨
   (p = 11 ∧ IsSporadic K .J4))

end CFSG.LocalAnalysis.AGL81I.Section3
