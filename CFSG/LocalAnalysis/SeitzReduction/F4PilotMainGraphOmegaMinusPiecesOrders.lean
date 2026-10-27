module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMismatchTables
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFourExtract
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSixExtract

public section

namespace CFSG.SeitzReduction.F4Pilot

open Module QuadraticMap
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadMinus)
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

omit [Finite K] [CharP K 2] in
theorem finrank_minusSpace {n : ℕ} (hn : 1 ≤ n) :
    finrank K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) = 2 * n := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin]
  omega

omit [CharP K 2] in
theorem exists_quadMinus_ne_zero (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    (U : Submodule K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)) (hU : finrank K U = n) :
    ∃ u ∈ U, quadMinus n K b c u ≠ 0 := by
  by_contra h
  push Not at h
  refine CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus hn hirr ⟨U, ?_, h⟩
  rw [hU, finrank_minusSpace hn]

omit [Finite K] [CharP K 2] in
theorem statedOmega_quadMinus_eq_map (n : ℕ) (b c : K) :
    StatedOmega (StatedQuadMinus n K b c) =
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c),
          TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c)⁆.map
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          K).symm.toMonoidHom := by
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (coe_quadMinus n K b c),
    Subgroup.comap_equiv_eq_map_symm']

omit [Finite K] [CharP K 2] in
theorem commutator_and_natCard_statedOmega_quadMinus (n : ℕ) (b c : K)
    (hperf : Group.IsPerfect ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c)⁆) :
    ⁅StatedOmega (StatedQuadMinus n K b c), StatedOmega (StatedQuadMinus n K b c)⁆ =
        StatedOmega (StatedQuadMinus n K b c) ∧
      Nat.card (StatedOmega (StatedQuadMinus n K b c)) =
        Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c),
          TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c)⁆ := by
  rw [statedOmega_quadMinus_eq_map n b c]
  refine ⟨?_, Subgroup.card_map_of_injective (MulEquiv.injective _)⟩
  rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.1 hperf]

theorem commutator_statedOmega_quadMinus_three (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ⁅StatedOmega (StatedQuadMinus 3 K b c), StatedOmega (StatedQuadMinus 3 K b c)⁆ =
      StatedOmega (StatedQuadMinus 3 K b c) := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, -, hperf, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction (quadMinus 3 K b c)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr)
      (finrank_minusSpace (n := 3) (by norm_num))
      (fun U hU => exists_quadMinus_ne_zero hirr (by norm_num) U hU)
  rw [← hcomm] at hperf
  exact (commutator_and_natCard_statedOmega_quadMinus 3 b c hperf).1

theorem natCard_statedOmega_quadMinus_three (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (StatedOmega (StatedQuadMinus 3 K b c)) = ordSU 4 (Nat.card K) := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, -, hperf, -, hcard, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction (quadMinus 3 K b c)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr)
      (finrank_minusSpace (n := 3) (by norm_num))
      (fun U hU => exists_quadMinus_ne_zero hirr (by norm_num) U hU)
  rw [← hcomm] at hperf hcard
  rw [(commutator_and_natCard_statedOmega_quadMinus 3 b c hperf).2, hcard, ordSU_four]
  ring

theorem commutator_statedOmega_quadMinus_two (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ⁅StatedOmega (StatedQuadMinus 2 K b c), StatedOmega (StatedQuadMinus 2 K b c)⁆ =
      StatedOmega (StatedQuadMinus 2 K b c) := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, -, hperf, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction (quadMinus 2 K b c)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr)
      (finrank_minusSpace (n := 2) (by norm_num))
      (fun U hU => exists_quadMinus_ne_zero hirr (by norm_num) U hU)
  rw [← hcomm] at hperf
  exact (commutator_and_natCard_statedOmega_quadMinus 2 b c hperf).1

theorem natCard_statedOmega_quadMinus_two (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (StatedOmega (StatedQuadMinus 2 K b c)) = ordSL 2 (Nat.card K ^ 2) := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, -, hperf, -, hcard, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction (quadMinus 2 K b c)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr)
      (finrank_minusSpace (n := 2) (by norm_num))
      (fun U hU => exists_quadMinus_ne_zero hirr (by norm_num) U hU)
  rw [← hcomm] at hperf hcard
  rw [(commutator_and_natCard_statedOmega_quadMinus 2 b c hperf).2, hcard, ordSL_two, ← pow_mul]

end CFSG.SeitzReduction.F4Pilot
