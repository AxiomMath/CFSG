module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverStated
public import CFSG.RankThree.PartOne.SLBN.LeviSU

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.RankThree.PartOne.SLBN
  CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

section Levi

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {m n : ℕ}
  {P : Matrix (Fin n) ((Fin 2 ⊕ Fin 2) ⊕ Fin m) K}
  (hP : hadj h P * P = frameGram 2 m K) (hnm : 2 * 2 + m = n)

theorem a2l_levSU_injective : Function.Injective (levSU h hP hnm) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have h1 : frameConj h P (leviSL h (m := m) A) = Matrix.scalar (Fin n) 1 := by
    have := congrArg (fun g : unitarySU p f K n =>
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hA
    simpa [coe_levSU] using this
  have h2 := eq_smul_of_frameConj_eq_scalar h hP h1
  refine Subtype.ext (Matrix.ext fun a b => ?_)
  have := congrFun (congrFun h2 (Sum.inl (Sum.inl a))) (Sum.inl (Sum.inl b))
  simpa [leviSL, Matrix.one_apply] using this

theorem a2l_leviSL_negOne (hm0 : m = 0) :
    leviSL h (m := m) (a2lNegOne K) = -1 := by
  subst hm0
  have h0 : (-1 : Matrix (Fin 0) (Fin 0) K) = 1 := Subsingleton.elim _ _
  have h1 : (-1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      Matrix.fromBlocks (-1) 0 0 (-1) := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have hneg : (-1 : Matrix ((Fin 2 ⊕ Fin 2) ⊕ Fin 0) ((Fin 2 ⊕ Fin 2) ⊕ Fin 0) K) =
      Matrix.fromBlocks (Matrix.fromBlocks (-1) 0 0 (-1)) 0 0 1 := by
    rw [← h1]
    conv_lhs => rw [← Matrix.fromBlocks_one]
    rw [Matrix.fromBlocks_neg]
    simp [h0]
  have hinv : (a2lNegOne K)⁻¹ = a2lNegOne K :=
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact a2lNegOne_sq K)
  have hinvmat : (((a2lNegOne K)⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1 := by
    rw [hinv]
    rfl
  have hadj1 : hadj h (-1 : Matrix (Fin 2) (Fin 2) K) = -1 := by
    ext a b
    simp [hadj, Matrix.one_apply, eq_comm]
  rw [hneg, leviSL, hinvmat, hadj1]
  rfl

theorem a2l_levSU_negOne (hm0 : m = 0) :
    ((levSU h hP hnm (a2lNegOne K) : unitarySU p f K n) : GL (Fin n) K) =
      Matrix.GeneralLinearGroup.scalar (Fin n) (-1) := by
  refine Units.ext ?_
  rw [coe_levSU, Matrix.GeneralLinearGroup.coe_scalar, a2l_leviSL_negOne h hm0]
  simp only [frameConj, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, frame_mul_inv h hP hnm,
    Units.val_neg, Units.val_one, map_neg, map_one]

theorem a2l_levSU_negOne_mem_center (hm0 : m = 0) :
    levSU h hP hnm (a2lNegOne K) ∈ center (unitarySU p f K n) := by
  apply Open.StatedAPI.statedScalars_subgroupOf_le_center
  rw [Subgroup.mem_subgroupOf, a2l_levSU_negOne h hP hnm hm0]
  exact ⟨-1, rfl⟩

end Levi

theorem a2l_centralDatum_psu43 (hC : HypA2.ChevOddInChev2) {K : Type} [Group K] [Finite K]
    (hq : IsQuasisimple K) (h2 : IsPGroup 2 ↥(center K)) (hZ : center K ≠ ⊥)
    (hnF : ¬ HypA2.IsFStar K) (hm : LieModel (K ⧸ center K) .PSU 4 3 1) :
    HypA2.CentralDatum K := by
  haveI : Group.IsPerfect K := hq.1
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  have hd := a2l_unitaryFieldData_three hcard
  haveI := hd.finite
  haveI := hd.charP
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := Fintype.ofFinite F
  have hF9 : Nat.card F = 9 := by rw [hcard]; norm_num
  have hFc : Fintype.card F = 9 := by rw [← Nat.card_eq_fintype_card]; exact hF9
  have hc3 : 3 ≤ Nat.card (center K) := by
    have h2le := a2l_two_le_card_center h2 hZ
    by_contra hlt
    exact hnF (a2l_isFStar_of_two_u43 hq h2 (by omega) hm)
  have hN : Nat.card ((StatedScalars (Fin 4) F).subgroupOf (StatedSU 4 (3 ^ 1) F)) < 2 * 3 := by
    have := a2l_card_scalars_su_four_le hF9
    omega
  obtain ⟨ψ⟩ := a2l_nonempty_equiv_of_cover
    (a2l_splits_statedSU hcard (by norm_num) (by norm_num)) h2 _ e hN hc3
  have hk : ringChar F ≠ 2 := a2l_ringChar_ne_two (by rw [hFc]; decide)
  obtain ⟨P, hPraw⟩ := exists_evenFrame hd (Ring.two_ne_zero hk) (n := 4) (r := 2) (by norm_num)
  have hP : hadj hd P * P = frameGram 2 (4 - 2 * 2) F := hPraw
  have hTU : HypA2.TypU K := a2l_typU_of_not_inChev2 hq h2
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))))) (a2l_not_inChev2_psu43 hC hm)
  exact a2l_centralDatum_of_equiv ψ (by decide) (by norm_num) hFc
    (levSU hd hP (by norm_num)) (a2l_levSU_injective hd hP _)
    (a2l_levSU_negOne_mem_center hd hP _ (by norm_num)) hTU

end CFSG.OddStandard.SmallF3.HypA2Leaves
