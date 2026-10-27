module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.BlockSL
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLinear

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit
open CFSG.ClassicalInvolution.WeakCT (blockSL)
open scoped MatrixGroups

def negOneFour (K : Type) [Field K] : SL(4, K) :=
  ⟨-1, by norm_num [Matrix.det_neg]⟩

theorem negOneFour_mem_center (K : Type) [Field K] : negOneFour K ∈ center SL(4, K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext i j
  show ((g : Matrix (Fin 4) (Fin 4) K) * (-1)) i j =
    ((-1) * (g : Matrix (Fin 4) (Fin 4) K)) i j
  simp

theorem orderOf_negOneFour {K : Type} [Field K] (h2 : (2 : K) ≠ 0) :
    orderOf (negOneFour K) = 2 := by
  apply orderOf_eq_prime
  · ext i j
    show ((-1 : Matrix (Fin 4) (Fin 4) K) ^ 2) i j = (1 : Matrix (Fin 4) (Fin 4) K) i j
    simp [pow_two]
  · intro h
    have h' : (-1 : K) = 1 := by
      simpa [negOneFour] using
        congrArg (fun g : SL(4, K) => (g : Matrix (Fin 4) (Fin 4) K) 0 0) h
    have : (2 : K) = 0 := by
      rw [show (2 : K) = 1 - (-1) by ring, h', sub_self]
    exact h2 this

theorem normal_blockSL_four {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 4 ≤ n) :
    ((blockSL K n 4 0 (by omega)).range.subgroupOf
      (centralizer ({blockSL K n 4 0 (by omega) (negOneFour K)} : Set SL(n, K)))).Normal := by
  set D : Matrix (Fin n) (Fin n) K :=
    CFSG.ClassicalInvolution.ModelFacts.negBlockK K n 0 4 with hD
  have hrange : (blockSL K n 4 0 (by omega)).range =
      CFSG.ClassicalInvolution.Models.longRootGroup D := by
    rw [hD]
    exact CFSG.ClassicalInvolution.ModelFacts.range_blockSL_eq_longRootGroupK h2
      (j := 0) (k := 4) (by omega)
  have hsD : ((blockSL K n 4 0 (by omega) (negOneFour K) : SL(n, K)) :
      Matrix (Fin n) (Fin n) K) = D := by
    rw [hD, CFSG.ClassicalInvolution.WeakCT.coe_blockSL,
      CFSG.ClassicalInvolution.ModelFacts.negBlockK]
    rfl
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  rw [hrange] at hx ⊢
  have hcomm : ((g : SL(n, K)) : Matrix (Fin n) (Fin n) K) * D =
      D * ((g : SL(n, K)) : Matrix (Fin n) (Fin n) K) := by
    have hg := Subgroup.mem_centralizer_singleton_iff.mp g.2
    have hg' := congrArg (fun y : SL(n, K) => (y : Matrix (Fin n) (Fin n) K)) hg
    simpa [Matrix.SpecialLinearGroup.coe_mul, hsD] using hg'
  have hconj := CFSG.ClassicalInvolution.Models.conj_mem_longRootGroup_of_commute hcomm hx
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hconj

theorem hasCleanFullClassBMember_psl
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 3) {n : ℕ} (hn : 5 ≤ n)
    [IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) K)] :
    HasCleanFullClassBMember (Matrix.ProjectiveSpecialLinearGroup (Fin n) K) := by
  have h2 := two_ne_zero_of_card_three hK
  haveI hSfin : Finite SL(n, K) := inferInstance
  haveI hQfin : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin n) K) :=
    Finite.of_surjective (QuotientGroup.mk' (center SL(n, K)))
      (QuotientGroup.mk'_surjective _)
  haveI hXfin : Finite SL(4, K) := inferInstance
  have key : HasCleanFullClassBMember (SL(n, K) ⧸ center SL(n, K)) :=
    hasCleanFullClassBMember_of_block
      (QuotientGroup.mk' (center SL(n, K)))
      (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk'])
      (blockSL K n 4 0 (by omega))
      (CFSG.ClassicalInvolution.WeakCT.comp_blockSL_injective
        (θ := QuotientGroup.mk' (center SL(n, K)))
        (by rw [QuotientGroup.ker_mk']) (by omega) (by omega))
      (c := negOneFour K)
      (orderOf_negOneFour h2)
      (negOneFour_mem_center K)
      (normal_blockSL_four h2 (by omega))
      (blockData_specialLinear hGA hK (Or.inl rfl))
  exact key

theorem hasCleanFullClassBMember_of_lieModel_psl
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {Q : Type} [Group Q]
    [Finite Q] [IsSimpleGroup Q] {n : ℕ} (hn : 5 ≤ n)
    (h : CFSG.Blueprint.LieModel Q .PSL n 3 1) : HasCleanFullClassBMember Q := by
  have hcm := h.statedClassicalModel (by decide)
  unfold CFSG.Open.StatedClassicalModel at hcm
  obtain ⟨-, K, _, _, hKcard, ⟨e⟩⟩ := hcm
  have hK : Nat.card K = 3 := by simpa using hKcard
  let e' : Q ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) K :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) K) := e'.symm.isSimpleGroup
  exact HasCleanFullClassBMember.of_mulEquiv e'.symm (hasCleanFullClassBMember_psl hGA hK hn)

end CFSG.OddStandard.HigherRank.F3
