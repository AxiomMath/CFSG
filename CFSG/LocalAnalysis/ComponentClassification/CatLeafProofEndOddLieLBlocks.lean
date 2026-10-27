module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieL3

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddLin

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.PSL (quadRep quadRep_algebraMap blockRep
  blockRep_apply blockSLE coe_blockSLE blockSLE_injective isQuasisimple_SL_quadExt QuadExt)
open scoped MatrixGroups

section Ring

variable {R : Type*} [CommRing R] (n : ℕ)

@[expose] def blkMatR (g : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin (2 + n)) (Fin (2 + n)) R :=
  (fromBlocks g 0 0 1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem blkMatR_mul (g h : Matrix (Fin 2) (Fin 2) R) :
    blkMatR n g * blkMatR n h = blkMatR n (g * h) := by
  rw [blkMatR, blkMatR, blkMatR, submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem blkMatR_one : blkMatR n (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  rw [blkMatR, fromBlocks_one, submatrix_one_equiv]

theorem det_blkMatR (g : Matrix (Fin 2) (Fin 2) R) : (blkMatR n g).det = g.det := by
  rw [blkMatR, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, mul_one]

theorem blkMatR_castAdd (g : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2) :
    blkMatR n g (Fin.castAdd n i) (Fin.castAdd n j) = g i j := by
  simp [blkMatR]

theorem blkMatR_natAdd (g : Matrix (Fin 2) (Fin 2) R) (i : Fin n) :
    blkMatR n g (Fin.natAdd 2 i) (Fin.natAdd 2 i) = 1 := by
  simp [blkMatR]

@[expose] def slBlkR : SL(2, R) →* SL(2 + n, R) where
  toFun g := ⟨blkMatR n (g : Matrix (Fin 2) (Fin 2) R), by rw [det_blkMatR, g.2]⟩
  map_one' := Subtype.ext (blkMatR_one n)
  map_mul' g h := Subtype.ext (blkMatR_mul n (g : Matrix (Fin 2) (Fin 2) R) h).symm

theorem coe_slBlkR (g : SL(2, R)) :
    ((slBlkR n g : SL(2 + n, R)) : Matrix (Fin (2 + n)) (Fin (2 + n)) R) =
      blkMatR n (g : Matrix (Fin 2) (Fin 2) R) := rfl

end Ring

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem coe_neg_one_SL2' : ((-1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1 := rfl

theorem quatBlock_blockSLE (hK : ringChar K ≠ 2) {l : K} (hl : ¬ IsSquare l) {m : ℕ}
    (hm : 2 ≤ m) (hm3 : 3 ≤ m) :
    QuatBlock ((blockSLE hl hm).range.map (QuotientGroup.mk' (scalars (m * 2) K))) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨n, rfl⟩ : ∃ n, m = 2 + n := ⟨m - 2, by omega⟩
  have hn : 1 ≤ n := by omega
  have hFq : IsQuasisimple (blockSLE hl hm).range :=
    LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (blockSLE_injective hl hm))
      (isQuasisimple_SL_quadExt hl hm)
  refine quatBlock_map_of_sl2 hFq hK ((blockSLE hl hm).comp ((slBlkR n).comp
    (Matrix.SpecialLinearGroup.map (algebraMap K (QuadExt l))))) (fun g => ⟨_, rfl⟩) ?_
  intro hmem
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hmem
  have hent : ∀ (i : Fin (2 + n)) (x : QuadExt l),
      blkMatR n ((algebraMap K (QuadExt l)).mapMatrix ((-1 : SL(2, K)) :
        Matrix (Fin 2) (Fin 2) K)) i i = x →
      ((blockSLE hl hm ((slBlkR n) (Matrix.SpecialLinearGroup.map
        (algebraMap K (QuadExt l)) (-1))) : SpecialLinearGroup (Fin ((2 + n) * 2)) K) :
          Matrix (Fin ((2 + n) * 2)) (Fin ((2 + n) * 2)) K) (finProdFinEquiv (i, 0))
          (finProdFinEquiv (i, 0)) = quadRep l x 0 0 := by
    intro i x hx
    rw [coe_blockSLE, blockRep_apply, coe_slBlkR, Matrix.SpecialLinearGroup.map_apply_coe, hx]
  have e1 := congrFun (congrFun hc (finProdFinEquiv (Fin.castAdd n 0, 0)))
    (finProdFinEquiv (Fin.castAdd n 0, 0))
  have e2 := congrFun (congrFun hc (finProdFinEquiv (Fin.natAdd 2 ⟨0, hn⟩, 0)))
    (finProdFinEquiv (Fin.natAdd 2 ⟨0, hn⟩, 0))
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
    hent _ (algebraMap K (QuadExt l) (-1)) (by
      rw [blkMatR_castAdd, RingHom.mapMatrix_apply, Matrix.map_apply, coe_neg_one_SL2',
        Matrix.neg_apply, Matrix.one_apply_eq]), quadRep_algebraMap, scalar_apply,
    diagonal_apply_eq] at e1
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
    hent _ 1 (by rw [blkMatR_natAdd]), map_one, scalar_apply, diagonal_apply_eq] at e2
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e1 e2
  exact h2 (by linear_combination e2 - e1)

variable {p f : ℕ}

theorem quatBlock_prSLHom (hu : UnitaryFieldData p f K) (hp2 : p ≠ 2) {l : K} (hl : l ≠ 0)
    (hN : hu.norm l = -1) {m : ℕ} (hm : 3 ≤ m) :
    QuatBlock ((prSLHom (m := m) hu (two_ne_zero_of_unitary hu hp2) hl hN).range.map
      (QuotientGroup.mk' ((StatedScalars (Fin (m + m)) K).subgroupOf
        (StatedSU (m + m) (p ^ f) K)))) := by
  have : Fact p.Prime := ⟨hu.prime⟩
  have := hu.charP
  have h2 := two_ne_zero_of_unitary hu hp2
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨n, rfl⟩ : ∃ n, m = 2 + n := ⟨m - 2, by omega⟩
  have hn : 1 ≤ n := by omega
  have hK4 : 4 ≤ Nat.card K := by
    rw [hu.card_eq_sq]
    have := hu.prime.two_le
    have : p ≤ p ^ f := Nat.le_self_pow (by have := hu.one_le; omega) p
    nlinarith
  refine quatBlock_map_of_sl2 (isQuasisimple_range_prSLHom hu h2 hl hN (by omega) hK4) hK
    ((prSLHom hu h2 hl hN).comp (slBlkR n)) (fun g => ⟨_, rfl⟩) ?_
  intro hmem
  rw [mem_subgroupOf] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hM : prPhi (2 + n) l (blkMatR n (-1)) (prDual hu (slBlkR n (-1))) = (c : K) • 1 := by
    have e := congrArg Units.val hc
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← smul_one_eq_diagonal] at e
    exact e.symm
  have hev := congrArg (prEv (2 + n) l) hM
  rw [prEv_prPhi h2 hl] at hev
  have hev' : prEv (2 + n) l ((c : K) • 1) = fromBlocks ((c : K) • 1) 0 0 ((c : K) • 1) := by
    rw [prEv, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, prWi_mul_prW h2 hl, map_smul,
      map_one, ← fromBlocks_one, fromBlocks_smul, smul_zero]
  rw [hev'] at hev
  have hblk := (fromBlocks_inj.1 hev).1
  have e1 := congrFun (congrFun hblk (Fin.castAdd n 0)) (Fin.castAdd n 0)
  have e2 := congrFun (congrFun hblk (Fin.natAdd 2 ⟨0, hn⟩)) (Fin.natAdd 2 ⟨0, hn⟩)
  rw [blkMatR_castAdd, Matrix.neg_apply, Matrix.one_apply_eq] at e1
  rw [blkMatR_natAdd] at e2
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e1 e2
  exact h2 (by linear_combination e2 - e1)

end CFSG.ComponentClassification.CatLeafProof.EndOddLin
