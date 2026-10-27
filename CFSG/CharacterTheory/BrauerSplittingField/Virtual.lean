module

public import CFSG.CharacterTheory.BrauerSplittingField.Descent
public import Mathlib.Order.Interval.Finset.Box
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.Character.Basic

public section

namespace CFSG

open CategoryTheory CategoryTheory.Limits BigOperators

namespace BrauerSplittingField.Virtual

noncomputable section

universe u

variable {k G : Type u} [Field k] [Group G]

abbrev PositiveIndex {ι : Type} (n : ι → ℤ) :=
  Σ i, Fin (n i).toNat

abbrev NegativeIndex {ι : Type} (n : ι → ℤ) :=
  Σ i, Fin (-n i).toNat

noncomputable def positiveRep {ι : Type} [Fintype ι]
    (S : ι → FDRep k G) (n : ι → ℤ) : FDRep k G :=
  Limits.biproduct (fun j : PositiveIndex n => S j.1)

noncomputable def negativeRep {ι : Type} [Fintype ι]
    (S : ι → FDRep k G) (n : ι → ℤ) : FDRep k G :=
  Limits.biproduct (fun j : NegativeIndex n => S j.1)

private lemma character_positiveRep {ι : Type} [Fintype ι]
    (S : ι → FDRep k G) (n : ι → ℤ) :
    (positiveRep S n).character =
      ∑ i, (n i).toNat • (S i).character := by
  rw [positiveRep, FDRep.char_biproduct, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simp

private lemma character_negativeRep {ι : Type} [Fintype ι]
    (S : ι → FDRep k G) (n : ι → ℤ) :
    (negativeRep S n).character =
      ∑ i, (-n i).toNat • (S i).character := by
  rw [negativeRep, FDRep.char_biproduct, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simp

lemma character_baseChange_positiveRep
    {K A G : Type u} [Field K] [Field A] [Algebra K A]
    [Group G] {ι : Type} [Fintype ι]
    (S : ι → FDRep K G) (n : ι → ℤ) :
    (FDRep.baseChange (A := A) (positiveRep S n)).character =
      (positiveRep (fun i => FDRep.baseChange (A := A) (S i)) n).character := by
  ext g
  simp only [FDRep.baseChange_character, character_positiveRep,
    Finset.sum_apply, Pi.smul_apply, map_sum, map_nsmul]

lemma character_baseChange_negativeRep
    {K A G : Type u} [Field K] [Field A] [Algebra K A]
    [Group G] {ι : Type} [Fintype ι]
    (S : ι → FDRep K G) (n : ι → ℤ) :
    (FDRep.baseChange (A := A) (negativeRep S n)).character =
      (negativeRep (fun i => FDRep.baseChange (A := A) (S i)) n).character := by
  ext g
  simp only [FDRep.baseChange_character, character_negativeRep,
    Finset.sum_apply, Pi.smul_apply, map_sum, map_nsmul]

private lemma zsmul_eq_positive_sub_negative (z : ℤ) (x : G → k) :
    z • x = z.toNat • x - (-z).toNat • x := by
  cases z with
  | ofNat n => simp
  | negSucc n =>
      ext g
      simp
      ring

lemma character_biprod_negative_eq_positive
    {ι : Type} [Fintype ι]
    [Finite G] [CharZero k]
    (V : FDRep k G) (S : ι → FDRep k G) (n : ι → ℤ)
    (h : V.character = ∑ i, n i • (S i).character) :
    (V ⊞ negativeRep S n).character = (positiveRep S n).character := by
  rw [FDRep.char_biprod_eq_add, character_negativeRep, character_positiveRep]
  rw [h]
  simp_rw [zsmul_eq_positive_sub_negative]
  rw [Finset.sum_sub_distrib]
  abel

end

end BrauerSplittingField.Virtual

end CFSG
