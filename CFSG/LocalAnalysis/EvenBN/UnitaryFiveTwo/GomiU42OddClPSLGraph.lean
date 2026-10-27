module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClPSLGraphSp

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBGraphForm (pureGraphAction isometryGroup)

theorem u42_psl_pureGraph {n f : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3 ^ f)
    (hn : 3 ≤ n) (hadm : StatedLieAdmissible .PSL n 3 f) (A : GL (Fin n) K)
    (hσ : orderOf (pureGraphAction n K A) = 2)
    {J : Subgroup ↥(fixedSubgroup (pureGraphAction n K A))}
    (hJ : U42Hyp (pureGraphAction n K A) J) : False := by
  have hf : 1 ≤ f := hadm.2.1
  have hodd := u42_ringChar_ne_two hf hK
  have hsq2 : pureGraphAction n K A ^ 2 = 1 := by
    rw [← hσ, pow_orderOf_eq_one]
  have hform := CatalogueBGraphForm.pureGraph_involution_form_data n K hn hodd A hsq2
  obtain ⟨h1, h2⟩ := u42_pg_constraints hn A hJ
  obtain ⟨hI1, hI2⟩ := u42_pg_index_dvd (n := n) (A⁻¹)
  have hz1 := u42_card_center_sl_dvd (K := K) (n := n) (by omega)
  have hz2 := u42_card_center_sl_dvd_card (K := K) (n := n) (by omega)
  have hI25920 : 25920 ∣ Nat.card ↥(isometryGroup n K A⁻¹) := h1.trans hI1
  have hIbound : Nat.card ↥(isometryGroup n K A⁻¹) ∣
      2 * Nat.card (center (SpecialLinearGroup (Fin n) K)) * 25920 := by
    have := hI2.trans (Nat.mul_dvd_mul_left 2 h2)
    rwa [← mul_assoc] at this
  rcases hform with hsymm | ⟨halt, hev⟩
  · exact u42_pg_symmetric_false hf hK hn A⁻¹
      (CatalogueBLinearHigherB.transpose_inv_of_transpose_eq A hsymm) hz1 (hK ▸ hz2) hI25920
      hIbound
  · have hz3 : ¬ 3 ∣ Nat.card (center (SpecialLinearGroup (Fin n) K)) :=
      u42_not_three_dvd_of_dvd_pred hf (hK ▸ hz2)
    obtain ⟨hn4, hf1, -⟩ := u42_pg_alt_reduce hf hK hn hev A⁻¹
      (CatalogueBLinearHigherB.transpose_inv_of_transpose_eq_neg A halt) hz3 hIbound
    subst hn4
    subst hf1
    exact u42_pg_alt_four_false (by rw [hK]; norm_num) A halt hJ

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
