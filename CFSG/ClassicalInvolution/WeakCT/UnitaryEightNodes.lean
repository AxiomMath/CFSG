module

public import CFSG.ClassicalInvolution.WeakCT.UnitaryEightRoots
public import CFSG.RankThree.PartTwo.CTU6.WeakCT

public section

namespace CFSG.ClassicalInvolution.WeakCT.UnitaryEight

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)
open CFSG.ClassicalInvolution.WeakCT (blockSL2 blockSL2_injective commute_of_tv₂)
open CFSG.RankThree.PartTwo.CTU6 (toTraceZero mem_fixedSubfield_of_mem_traceZero
  rootGroup_le_range_longRootHom rootMatrix_mul_longRootMatrix_comm commute_of_mat_comm)
open CFSG.LieType.Steinberg (fixedSubfield)
open CFSG.Timmesfeld (tv)
open scoped MatrixGroups

abbrev n0 : Fin (8 / 2) := ⟨0, by decide⟩

abbrev n1 : Fin (8 / 2) := ⟨1, by decide⟩

abbrev n2 : Fin (8 / 2) := ⟨2, by decide⟩

abbrev n3 : Fin (8 / 2) := ⟨3, by decide⟩

section Short

variable {F : Type} [Field F] (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c)

@[expose] noncomputable def rS8 (k : Fin 3) : SL(2, F) →* SU σ 8 :=
  (embSL4 σ hσ).comp (blockSL2 F 3 k)

theorem rS8_injective (k : Fin 3) : Function.Injective (rS8 σ hσ k) :=
  (embSL4_injective σ hσ).comp (blockSL2_injective 3 k)

abbrev nS (k : Fin 3) : Fin (8 / 2) := ⟨k.val, by omega⟩

theorem nS_succ_lt (k : Fin 3) : (nS k).val + 1 < 8 / 2 := by
  show (k : ℕ) + 1 < 4
  have := k.2
  omega

theorem rS8_tv01 (k : Fin 3) (c : F) :
    rS8 σ hσ k (tv 0 1 c) = rootHom σ hσ (lowIdx_ne_succ (nS_succ_lt k)) (lowIdx_ne_rev _ _)
      (lowIdx_ne_rev _ _) (Multiplicative.ofAdd c) := by
  rw [rS8, MonoidHom.comp_apply, blockSL2_three_tv01]
  fin_cases k
  · exact embSL4_tv01 σ hσ c
  · exact embSL4_tv12 σ hσ c
  · exact embSL4_tv23 σ hσ c

theorem rS8_tv10 (k : Fin 3) (c : F) :
    rS8 σ hσ k (tv 1 0 c) = rootHom σ hσ (lowIdx_ne_succ (nS_succ_lt k)).symm (lowIdx_ne_rev _ _)
      (lowIdx_ne_rev _ _) (Multiplicative.ofAdd c) := by
  rw [rS8, MonoidHom.comp_apply, blockSL2_three_tv10]
  fin_cases k
  · exact embSL4_tv10 σ hσ c
  · exact embSL4_tv21 σ hσ c
  · exact embSL4_tv32 σ hσ c

end Short

section Long

variable {F : Type} [Field F] (σ : F ≃+* F)

theorem embSU6_longRootHom (t : Multiplicative (traceZero σ)) :
    embSU6 σ (longRootHom σ (i := (2 : Fin 6)) (by decide) t) =
      longRootHom σ (i := (3 : Fin 8)) (by decide) t := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_embSU6, coe_longRootHom, coe_longRootHom]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockMat_apply, longRootMatrix, one_apply, Fin.rev]

theorem embSU6_longRootHom_rev (t : Multiplicative (traceZero σ)) :
    embSU6 σ (longRootHom σ (i := (3 : Fin 6)) (by decide) t) =
      longRootHom σ (i := (4 : Fin 8)) (by decide) t := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_embSU6, coe_longRootHom, coe_longRootHom]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockMat_apply, longRootMatrix, one_apply, Fin.rev]

end Long

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]

variable (K f) in
@[expose] noncomputable def rL8 : SL(2, fixedSubfield K 2 f) →* SU (unitaryInvolution K 2 f) 8 :=
  (embSU6 (unitaryInvolution K 2 f)).comp (CFSG.RankThree.PartTwo.CTU6.rL K f)

theorem rL8_injective : Function.Injective (rL8 K f) :=
  (embSU6_injective _).comp CFSG.RankThree.PartTwo.CTU6.rL_injective

theorem rL8_tv01 (c : fixedSubfield K 2 f) :
    rL8 K f (tv 0 1 c) = longRootHom (unitaryInvolution K 2 f) (lowIdx_ne_rev n3 n3)
      (Multiplicative.ofAdd (toTraceZero c)) := by
  rw [rL8, MonoidHom.comp_apply, CFSG.RankThree.PartTwo.CTU6.rL_tv01]
  exact embSU6_longRootHom _ _

theorem rL8_tv10 (c : fixedSubfield K 2 f) :
    rL8 K f (tv 1 0 c) = longRootHom (unitaryInvolution K 2 f)
      (rev_ne_rev_rev (lowIdx_ne_rev n3 n3)) (Multiplicative.ofAdd (toTraceZero c)) := by
  rw [rL8, MonoidHom.comp_apply, CFSG.RankThree.PartTwo.CTU6.rL_tv10]
  exact embSU6_longRootHom_rev _ _

variable (hK : Nat.card K = (2 ^ f) ^ 2)
include hK

theorem rL8_upper_mem (c : fixedSubfield K 2 f) :
    rL8 K f (tv 0 1 c) ∈ rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 8
      (Pi.single n3 1) := by
  rw [rL8_tv01]
  exact longRootHom_mem _ _ (toStd_last_even (k := n3) (by decide) ⟨4, rfl⟩).symm _

theorem rL8_lower_mem (c : fixedSubfield K 2 f) :
    rL8 K f (tv 1 0 c) ∈ rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 8
      (-Pi.single n3 1) := by
  rw [rL8_tv10]
  exact longRootHom_mem _ _ (toStd_neg_last_even (k := n3) (by decide) ⟨4, rfl⟩).symm _

theorem rL8_param_upper :
    ∀ g ∈ rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 8
      (Pi.single n3 1), ∃ c, rL8 K f (tv 0 1 c) = g := by
  intro g hg
  obtain ⟨t, rfl⟩ := rootGroup_le_range_longRootHom (unitaryInvolution_involutive hK) ⟨4, rfl⟩
    (lowIdx_ne_rev n3 n3) (toStd_last_even (k := n3) (by decide) ⟨4, rfl⟩) hg
  refine ⟨⟨((Multiplicative.toAdd t : traceZero (unitaryInvolution K 2 f)) : K),
    mem_fixedSubfield_of_mem_traceZero _⟩, ?_⟩
  rw [rL8_tv01]
  rfl

theorem rL8_param_lower :
    ∀ g ∈ rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 8
      (-Pi.single n3 1), ∃ c, rL8 K f (tv 1 0 c) = g := by
  intro g hg
  obtain ⟨t, rfl⟩ := rootGroup_le_range_longRootHom (unitaryInvolution_involutive hK) ⟨4, rfl⟩
    (rev_ne_rev_rev (lowIdx_ne_rev n3 n3))
    (toStd_neg_last_even (k := n3) (by decide) ⟨4, rfl⟩) hg
  refine ⟨⟨((Multiplicative.toAdd t : traceZero (unitaryInvolution K 2 f)) : K),
    mem_fixedSubfield_of_mem_traceZero _⟩, ?_⟩
  rw [rL8_tv10]
  rfl

theorem commute_rS8_zero_rL8 (a : SL(2, K)) (b : SL(2, fixedSubfield K 2 f)) :
    Commute (rS8 _ (unitaryInvolution_involutive hK) 0 a) (rL8 K f b) := by
  refine commute_of_tv₂ _ _ (fun c d => ⟨?_, ?_, ?_, ?_⟩) a b
  · rw [rS8_tv01, rL8_tv01]
    refine commute_of_mat_comm ?_
    rw [coe_rootHom, coe_longRootHom]
    exact rootMatrix_mul_longRootMatrix_comm _ _ (by decide) (by decide) (by decide) (by decide)
  · rw [rS8_tv01, rL8_tv10]
    refine commute_of_mat_comm ?_
    rw [coe_rootHom, coe_longRootHom]
    exact rootMatrix_mul_longRootMatrix_comm _ _ (by decide) (by decide) (by decide) (by decide)
  · rw [rS8_tv10, rL8_tv01]
    refine commute_of_mat_comm ?_
    rw [coe_rootHom, coe_longRootHom]
    exact rootMatrix_mul_longRootMatrix_comm _ _ (by decide) (by decide) (by decide) (by decide)
  · rw [rS8_tv10, rL8_tv10]
    refine commute_of_mat_comm ?_
    rw [coe_rootHom, coe_longRootHom]
    exact rootMatrix_mul_longRootMatrix_comm _ _ (by decide) (by decide) (by decide) (by decide)

end CFSG.ClassicalInvolution.WeakCT.UnitaryEight

end
