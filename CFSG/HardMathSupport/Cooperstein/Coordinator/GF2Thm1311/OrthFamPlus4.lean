module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthSwapKlein
import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthFamD4

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open scoped Pointwise

theorem kleinBigInv_POmegaPlus_ge_five_q4 {X : Type} [Group X] {n : ℕ} (hn : 5 ≤ n)
    (h : StatedClassicalModel X .POmegaPlus n 2 2) : KleinBigInv X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus
    (.inr (.inl rfl)) n 2 2 h K hK (quadPlus n K) (coe_quadPlus n K) e
  have hab' : Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus n K))) ≤ 2 := by
    rw [show coordinateQuadPlus n K = reindexQuadraticForm (plusIndexEquiv n) (quadPlus n K)
      from rfl, card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  exact KleinBigInv.of_mulEquiv (coordinatePlusWitnessEquiv K e).symm
    (kleinBigInv_orth_swap hK4 (coordinateQuadPlus n K) (by omega) hnd hT
      (commutator_coordinateQuadPlus n K (by omega)) hab'
      (fun B _ _ _ _ => ⟨1, fun b _ => by simp [htop]⟩))

theorem kleinBigInv_POmegaPlus_four_q4 {X : Type} [Group X]
    (h : StatedClassicalModel X .POmegaPlus 4 2 2) : KleinBigInv X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus
    (.inr (.inl rfl)) 4 2 2 h K hK (quadPlus 4 K) (coe_quadPlus 4 K) e
  have hab' : Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus 4 K))) ≤ 2 := by
    rw [coordinateQuadPlus, card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have hEA := (orthogonal_geometry_plus_model_stabilizer_preserving_image h K hK e).1
  have hsub := coordinate_plus_pointFamily_orbit_subset (n := 4) (K := K) rfl
  obtain ⟨κ, hκF, hκy, hκz, hyz⟩ := CFSG.RankThree.PartOne.KLC.swap_data_coordinate K
  have hst : (projectivePointFamilyAut (coordinateQuadPlus 4 K)).index =
      (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
        (projectivePointFamily (coordinateQuadPlus 4 K))).ncard :=
    MulAction.index_stabilizer _ _
  have hodd : Odd (matrixProjectiveImage (coordinateQuadPlus 4 K)).index := by
    rw [← hEA, hst]
    refine ncard_orbit_odd (y := plusCX 4 K) (z := plusCXstar 4 K (by omega)) ?_ hκF hκy hκz hyz
    intro a
    have := hsub (MulAction.mem_orbit _ a)
    simpa using this
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have : Finite (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) := inferInstance
  exact KleinBigInv.of_mulEquiv (coordinatePlusWitnessEquiv K e).symm
    (kleinBigInv_orth_swap hK4 (coordinateQuadPlus 4 K) (by omega) hnd hT
      (commutator_coordinateQuadPlus 4 K (by omega)) hab'
      (fun B _ hsq _ _ => exists_conj_mem_of_odd_index hodd (B := B) hsq))

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
