module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddCl
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClPSLTools
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClArithA
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerParameters
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionSplitStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveQuadraticMatrix

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (innerDiagonalAction)
open CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open CFSG.ComponentClassification.CatalogueBProjectiveInvolution (positiveMatrixDimension
  negativeMatrixDimension)

theorem u42_card_GL {K : Type} [Field K] [Finite K] (k : ℕ) :
    Nat.card (GL (Fin k) K) = u42GL (Nat.card K) k := by
  letI : Fintype K := Fintype.ofFinite K
  rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, u42GL, Fin.prod_univ_eq_prod_range
    (fun i => Nat.card K ^ k - Nat.card K ^ i) k]

theorem u42_psl_inner {n f : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3 ^ f)
    (hf : 1 ≤ f) (hadm : StatedLieAdmissible .PSL n 3 f) (A : GL (Fin n) K)
    (hσ : orderOf (innerDiagonalAction n K A) = 2)
    {J : Subgroup ↥(fixedSubgroup (innerDiagonalAction n K A))}
    (hJ : U42Hyp (innerDiagonalAction n K A) J) : False := by
  have hn : 2 ≤ n := hadm.2.2.1
  have hne3 : (n, 3 ^ f) ≠ (2, 3) := hadm.2.2.2.2
  have hq9 : n = 2 → 9 ≤ Nat.card K := by
    intro hn2
    rw [hK]
    by_cases hf1 : f = 1
    · exfalso
      subst hf1 hn2
      exact hne3 rfl
    · calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K := by
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · right
      have := hq9 (by omega)
      omega
    · exact Or.inl h3
  have hodd : Odd (Nat.card K) := by rw [hK]; exact Odd.pow (by decide)
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero
    (CFSG.ComponentClassification.CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card K hodd)
  have hne : innerDiagonalAction n K A ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have hsq2 : innerDiagonalAction n K A ^ 2 = 1 := by
    rw [← hσ, pow_orderOf_eq_one]
  obtain ⟨hmk, hmk2, c, hc⟩ :=
    CFSG.ComponentClassification.CatalogueBHigherLinearInner.inner_involution_projective_data n K
      hn hparameter A hne hsq2
  obtain ⟨ε, e, hε, he, heq⟩ := u42_psl_inner_eq (by omega : 1 ≤ n) A hmk2
  have hC₀ : Nat.card ↥(fixedSubgroup (innerDiagonalAction n K A)) = 25920 ∨
      Nat.card ↥(fixedSubgroup (innerDiagonalAction n K A)) = 51840 := hJ.card_mem
  rw [hK] at he
  by_cases hsquare : IsSquare c.val
  · obtain ⟨b, -, hr, hs, hrs, e', -, hsc, -⟩ :=
      CFSG.ComponentClassification.CatalogueBProjectiveInvolution.square_projective_centralizer_structure
        n hn A c h2 hmk hc hsquare
    generalize positiveMatrixDimension A b.val = r at *
    generalize negativeMatrixDimension A b.val = s at *
    have hcardM : Nat.card (Subgroup.centralizer ({A} : Set (GL (Fin n) K))) =
        u42GL (3 ^ f) r * u42GL (3 ^ f) s := by
      rw [Nat.card_congr e'.toEquiv, Nat.card_prod, u42_card_GL, u42_card_GL, hK]
    rw [hcardM, hK] at heq
    rw [← hrs] at he
    rcases hC₀ with h0 | h0
    · rw [h0] at heq
      exact u42_arith_psl_split hf hr hs hε (Or.inl rfl) he heq
    · rw [h0] at heq
      exact u42_arith_psl_split hf hr hs hε (Or.inr rfl) he heq
  · letI : Fact (¬ IsSquare c.val) := ⟨hsquare⟩
    haveI : Finite (extension c.val) := Module.finite_of_finite K
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    have hEcard : Nat.card (extension c.val) = Nat.card K ^ 2 := by
      let _ : Fintype K := Fintype.ofFinite K
      let _ : Fintype (extension c.val) := Fintype.ofFinite _
      have h := Module.card_eq_pow_finrank (K := K) (V := extension c.val)
      rw [extension_finrank c.val, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
      exact h
    have hdim := matrixDimension_twice A c hc
    have hpos := matrixDimension_pos A c hc
    have hnm : n = 2 * matrixDimension A c hc := by simpa using hdim
    have hcardM : Nat.card (Subgroup.centralizer ({A} : Set (GL (Fin n) K))) =
        u42GL ((3 ^ f) ^ 2) (matrixDimension A c hc) := by
      rw [Nat.card_congr (matrixCentralizerQuadraticEquiv A c hc).toEquiv, u42_card_GL, hEcard, hK]
    rw [hcardM, hK] at heq
    rw [hnm] at he
    rcases hC₀ with h0 | h0
    · rw [h0] at heq
      exact u42_arith_psl_quad hf hpos hε (Or.inl rfl) he heq
    · rw [h0] at heq
      exact u42_arith_psl_quad hf hpos hε (Or.inr rfl) he heq

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
