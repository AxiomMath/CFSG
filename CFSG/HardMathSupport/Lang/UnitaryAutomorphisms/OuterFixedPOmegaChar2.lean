module

public import CFSG.RankThree.PartOne.S11d.OrthSubfieldDickson
public import CFSG.Timmesfeld.Orders.ClassicalOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.ComponentClassification.CatLeaf
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.Timmesfeld.ClassicalOrders

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

variable {K : Type} [Field K] [Finite K] [CharP K 2] (k : Subfield K) (n : ℕ)

private theorem cast_prod_sub_one' (q a b s : ℕ) (hq : 1 ≤ q) :
    ((∏ i ∈ Finset.Icc a b, (q ^ (s * i) - 1) : ℕ) : ℤ) =
      ∏ i ∈ Finset.Icc a b, ((q : ℤ) ^ (s * i) - 1) := by
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  push_cast
  rfl

theorem card_model_plus_eq (hn : 4 ≤ n) :
    Nat.card (matrixProjectiveDerived (coordinateQuadPlus n k)) =
      lieOrderNumerator .POmegaPlus n (Nat.card k) := by
  have := Finite.of_injective (algebraMap k K) (algebraMap k K).injective
  have hq : 1 ≤ Nat.card k := Nat.card_pos
  rw [← Nat.card_congr (coordinatePlusWitnessEquiv k (MulEquiv.refl
    (StatedProj (StatedOmega (StatedQuadPlus n k))))).toEquiv]
  have h3 := card_statedProj_statedOmega_quadPlus (K := k) (n := n) hn
  have h4 := cast_prod_sub_one' (Nat.card k) 1 (n - 1) 2 hq
  have h5 : ((Nat.card k ^ n - 1 : ℕ) : ℤ) = (Nat.card k : ℤ) ^ n - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
    push_cast
    rfl
  apply Nat.cast_injective (R := ℤ)
  rw [h3]
  simp only [lieOrderNumerator]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, h4, h5]

theorem card_model_minus_eq (hn : 4 ≤ n) {b c : k} (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (matrixProjectiveDerived (coordinateQuadMinus n k (by omega) b c)) =
      lieOrderNumerator .POmegaMinus n (Nat.card k) := by
  have := Finite.of_injective (algebraMap k K) (algebraMap k K).injective
  have hq : 1 ≤ Nat.card k := Nat.card_pos
  rw [← Nat.card_congr (coordinateMinusWitnessEquiv k (by omega) b c (MulEquiv.refl
    (StatedProj (StatedOmega (StatedQuadMinus n k b c))))).toEquiv]
  have h3 := card_statedProj_statedOmega_quadMinus (K := k) (n := n) hn hirr
  have h4 := cast_prod_sub_one' (Nat.card k) 1 (n - 1) 2 hq
  apply Nat.cast_injective (R := ℤ)
  rw [h3]
  simp only [lieOrderNumerator]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, h4]
  push_cast
  try ring

variable {Q₀ : QuadraticForm k (Fin (2 * n) → k)}

theorem card_subfieldFixedGroup_dvd_model {Q : QuadraticForm K (Fin (2 * n) → K)}
    (hext : IsExtension k Q₀ Q) (hnd₀ : (QuadraticMap.polarBilin Q₀).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin (2 * n) → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) :
    Nat.card (subfieldFixedGroup k Q₀ Q) ∣ Nat.card (matrixProjectiveDerived Q₀) := by
  have hd : 0 < 2 * n := three_le_of_totallySingular k hT₀
  have hle := CFSG.RankThree.PartOne.FieldFix.subfieldFixedGroup_le_derivedImage hext hnd₀ hT₀ hnd
  have h1 := Subgroup.card_dvd_of_le hle
  refine h1.trans (dvd_of_eq ?_)
  exact (Nat.card_congr (MonoidHom.ofInjective (incl_injective k hext hd)).toEquiv.symm)

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
