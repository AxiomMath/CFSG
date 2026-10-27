module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.Blueprint.Catalog
public import CFSG.Adapters.ProjectiveSpecialLinear

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearCover

open Matrix LinearFlag

@[expose] def projectiveSpecialLinearEquivProjectiveSL (n : ℕ) (K : Type*) [Field K] :
    ProjectiveSpecialLinearGroup (Fin n) K ≃* projectiveSL n K :=
  QuotientGroup.quotientMulEquivOfEq (scalars_eq_center n K).symm

theorem exists_mulEquiv_projectiveSL_of_lieModel {Q : Type} [Group Q] {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel Q .PSL n p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (Q ≃* projectiveSL n K) := by
  rcases h with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨-, K, hK, hfin, hcard, ⟨e⟩⟩ := hc
    exact ⟨K, hK, hfin, hcard, ⟨(e.trans
      (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (projectiveSpecialLinearEquivProjectiveSL n K)⟩⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem scalars_two_eq_bot (K : Type*) [Field K] [CharP K 2] : scalars 2 K = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨c, hc, hA⟩
  rw [Subgroup.mem_bot]
  have hc1 : (c : K) = 1 := by
    have h : ((c : K) - 1) ^ 2 = 0 := by
      have h2 : (c : K) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
      linear_combination h2 + (1 - (c : K)) * (CharP.cast_eq_zero K 2)
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h)
  apply Subtype.ext
  change (A : Matrix (Fin 2) (Fin 2) K) = 1
  rw [hA, hc1, map_one]

@[expose] def projectiveSLTwoEquivSL (K : Type*) [Field K] [CharP K 2] :
    projectiveSL 2 K ≃* SpecialLinearGroup (Fin 2) K :=
  (QuotientGroup.quotientMulEquivOfEq (scalars_two_eq_bot K)).trans
    (QuotientGroup.quotientBot)

end LinearCover

end CFSG.LocalAnalysis.ComponentInitial
