module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthKlein

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

theorem kleinBigInv_POmegaPlus_ge_five {X : Type} [Group X] {n m : ℕ} (hn : 5 ≤ n) (hm : m ≠ 2 ∨ 6 ≤ n)
    (h : StatedClassicalModel X .POmegaPlus n 2 m) : KleinBigInv X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by
    rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus
    (.inr (.inl rfl)) n 2 m h K hK (quadPlus n K) (coe_quadPlus n K) e
  have hab' : Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus n K))) ≤ 2 := by
    rw [show coordinateQuadPlus n K = reindexQuadraticForm (plusIndexEquiv n) (quadPlus n K)
      from rfl, card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn
  have hK4 : Nat.card K = 4 → m = 2 := by
    intro h4
    rw [hK] at h4
    exact Nat.pow_right_injective (le_refl 2) (by simpa using h4)
  exact KleinBigInv.of_mulEquiv (coordinatePlusWitnessEquiv K e).symm
    (kleinBigInv_orth (coordinateQuadPlus n K) (by omega) (fun h4 => by rcases hm with hm | hm <;> [exact absurd (hK4 h4) hm; omega]) hnd hT
      (commutator_coordinateQuadPlus n K (by omega)) hab'
      (fun B _ _ _ _ => ⟨1, fun b _ => by simp [htop]⟩))

theorem kleinBigInv_POmegaMinus {X : Type} [Group X] {n m : ℕ} (hm : m ≠ 2 ∨ 6 ≤ n)
    (h : StatedClassicalModel X .POmegaMinus n 2 m) : KleinBigInv X := by
  obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have hn1 : 1 ≤ n := by omega
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaMinus
    (.inr (.inr rfl)) n 2 m h K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
  have hab' :
      Nat.card (Abelianization (matrixIsometries (coordinateQuadMinus n K hn1 b c))) ≤ 2 := by
    rw [show coordinateQuadMinus n K hn1 b c =
      reindexQuadraticForm (minusIndexEquiv n hn1) (quadMinus n K b c) from rfl,
      card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c
    hirr
  have hK4 : Nat.card K = 4 → m = 2 := by
    intro h4
    rw [hK] at h4
    exact Nat.pow_right_injective (le_refl 2) (by simpa using h4)
  exact KleinBigInv.of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e).symm
    (kleinBigInv_orth (coordinateQuadMinus n K hn1 b c) (by omega) (fun h4 => by rcases hm with hm | hm <;> [exact absurd (hK4 h4) hm; omega]) hnd hT
      (commutator_coordinateQuadMinus n K b c hn hirr) hab'
      (fun B _ _ _ _ => ⟨1, fun x _ => by simp [htop]⟩))

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
