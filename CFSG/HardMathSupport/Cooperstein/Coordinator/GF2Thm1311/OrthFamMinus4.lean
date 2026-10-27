module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthMinus
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.MinusSum

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

theorem kleinBigInv_POmegaMinus_four {X : Type} [Group X] {n : ℕ}
    (h : StatedClassicalModel X .POmegaMinus n 2 2) : KleinBigInv X := by
  obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have hn1 : 1 ≤ n := by omega
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaMinus
    (.inr (.inr rfl)) n 2 2 h K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
  have hab' :
      Nat.card (Abelianization (matrixIsometries (coordinateQuadMinus n K hn1 b c))) ≤ 2 := by
    rw [show coordinateQuadMinus n K hn1 b c =
      reindexQuadraticForm (minusIndexEquiv n hn1) (quadMinus n K b c) from rfl,
      card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c
    hirr
  have hS : ∑ v : Fin (2 * n) → K, chi (coordinateQuadMinus n K hn1 b c v) < 0 := by
    have hsum := sum_chi_minus_neg hK4 (n - 1) b c hirr
    refine lt_of_eq_of_lt ?_ hsum
    refine Fintype.sum_equiv (Equiv.arrowCongr (minusIndexEquiv n hn1) (Equiv.refl K)).symm _ _
      (fun v => ?_)
    rw [coordinateQuadMinus_apply]
    rfl
  exact KleinBigInv.of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e).symm
    (kleinBigInv_orth_of_negSum hK4 (coordinateQuadMinus n K hn1 b c) (by omega) hnd hT
      (commutator_coordinateQuadMinus n K b c hn hirr) hab'
      (fun B _ _ _ _ => ⟨1, fun x _ => by simp [htop]⟩) hS)

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
