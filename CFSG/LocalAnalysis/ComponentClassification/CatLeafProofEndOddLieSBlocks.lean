module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieS6c
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieL1
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddSp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.Sp
open CFSG.ComponentClassification.CatLeafProof.EndOddLin
open CFSG.ComponentClassification.CatFactsSp4 (diagSL coe_diagSL T2 mem_centralizer_T2_iff
  exists_conj_T2 kron_mul kron_neg_one_one)
open CFSG.LinearGroups (elementarySet special_linear_elementary_generation)
open scoped MatrixGroups

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem quatBlock_of_isometryEquiv (hK : ringChar K ≠ 2) {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {B : LinearMap.BilinForm K V} (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hdim : 2 ≤ Module.finrank K V) {P : Type} [Group P]
    {N : Subgroup P} (e : N ≃* CatalogueBAlternatingIsometry.isometryGroup B) : QuatBlock N := by
  have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  obtain ⟨m, hm, ⟨e'⟩⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic B hB hnd
  have hm1 : 0 < m := by omega
  set eS : N ≃* StatedSp m K := (e.trans e').trans (MulEquiv.subgroupCongr
    (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := m) (K := K)).symm) with heS
  by_cases hsmall : Module.finrank K V = 2 ∧ Nat.card K = 3
  · have := CatalogueBAlternatingIsometry.plane_fieldThree_solvable B hB hnd hsmall.1 hsmall.2
    exact quatBlock_of_isSolvable
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  have hq : IsQuasisimple N := LocalCores.isQuasisimple_of_mulEquiv e.symm
    (CatalogueBAlternatingIsometry.isometry_quasisimple B hB hnd hdim hodd (not_and_or.1 hsmall))
  obtain ⟨H, ⟨eH⟩⟩ := exists_quaternion_of_mulEquiv_SL hK (longRootEquiv K (⟨0, hm1⟩ : Fin m))
  let ι : longRoot K (⟨0, hm1⟩ : Fin m) →* N :=
    eS.symm.toMonoidHom.comp (longRoot K (⟨0, hm1⟩ : Fin m)).subtype
  have hι : Function.Injective ι := eS.symm.injective.comp (Subgroup.subtype_injective _)
  exact quatBlock_of_quat hq (H.map ι) ((H.equivMapOfInjective ι hι).symm.trans eH)

omit [Finite K] in
theorem not_mem_scalars_of_ne_smul {x : StatedSp r K}
    (hx : ∀ c : K, (((x : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) ≠ c • 1) :
    x ∉ (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K) := by
  intro hm
  rw [mem_subgroupOf] at hm
  obtain ⟨c, hc⟩ := hm
  apply hx (c : K)
  rw [← hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem quatBlock_leviSL (hK : ringChar K ≠ 2) (hr : 3 ≤ r) :
    QuatBlock ((leviSL r K).range.map (QuotientGroup.mk'
      ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K)))) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨n, rfl⟩ : ∃ n, r = 2 + n := ⟨r - 2, by omega⟩
  have hn : 1 ≤ n := by omega
  refine quatBlock_map_of_sl2 (isQuasisimple_leviSL_range (by omega) (Or.inl (by omega))) hK
    ((leviSL (2 + n) K).comp (slBlk n)) (fun g => ⟨slBlk n g, rfl⟩)
    (not_mem_scalars_of_ne_smul fun c hc => ?_)
  have e1 := congrFun (congrFun hc (Sum.inl (Fin.castAdd n 0))) (Sum.inl (Fin.castAdd n 0))
  have e2 := congrFun (congrFun hc (Sum.inl (Fin.natAdd 2 ⟨0, hn⟩)))
    (Sum.inl (Fin.natAdd 2 ⟨0, hn⟩))
  rw [MonoidHom.comp_apply, coe_leviSL, fromBlocks_apply₁₁, coe_slBlk] at e1 e2
  rw [slBlkMat_castAdd, coe_neg_one_SL2] at e1
  rw [slBlkMat_natAdd] at e2
  simp only [Matrix.neg_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul,
    mul_one] at e1 e2
  exact h2 (by linear_combination e2 - e1)

end CFSG.ComponentClassification.CatLeafProof.EndOddSp
