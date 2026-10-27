module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open CFSG.GorensteinWalter

variable {F : Type} [Field F] [Finite F]

theorem neg_one_ne_one_of_card_nine (hF : Nat.card F = 9) : (-1 : F) ≠ 1 := by
  apply Ring.neg_one_ne_one_of_char_ne_two
  intro h2
  let : Fintype F := Fintype.ofFinite F
  have h := FiniteField.even_card_of_char_two h2
  rw [← Nat.card_eq_fintype_card, hF] at h
  norm_num at h

theorem card_psl2_nine (hF : Nat.card F = 9) : Nat.card (PSL2 F) = 360 := by
  have h : Nat.card (PSL2 F) *
      Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) =
        Nat.card F * (Nat.card F ^ 2 - 1) :=
    CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center
  rw [CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_ne_one
    (neg_one_ne_one_of_card_nine hF), hF] at h
  norm_num at h
  omega

end CFSG.LocalAnalysis.EvenBN.Tits
