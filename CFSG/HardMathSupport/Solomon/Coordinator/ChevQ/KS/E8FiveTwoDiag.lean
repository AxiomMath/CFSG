module

public import CFSG.RankThree.SubgroupLists2.SpectralBounds

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

namespace Two

open Matrix

theorem exists_simul_diag {L : Type} [Field L] [IsAlgClosed L] (h5 : (5 : L) ≠ 0) {ι : Type}
    (Y : ι → Matrix (Fin 5) (Fin 5) L) (hcomm : ∀ i j, Y i * Y j = Y j * Y i) {c : ι → L}
    (hc : ∀ i, c i ≠ 0) (hY : ∀ i, Y i ^ 5 = c i • 1) :
    ∃ S : GL (Fin 5) L, ∀ i, ∃ d : Fin 5 → L,
      Y i * (S : Matrix (Fin 5) (Fin 5) L) = (S : Matrix (Fin 5) (Fin 5) L) * diagonal d := by
  classical
  choose a ha using fun i => IsAlgClosed.exists_pow_nat_eq (c i) (by norm_num : 0 < 5)
  have ha0 : ∀ i, a i ≠ 0 := fun i h => hc i (by rw [← ha i, h]; norm_num)
  set A : ι → Matrix (Fin 5) (Fin 5) L := fun i => (a i)⁻¹ • Y i with hA
  have hAc : ∀ i j, A i * A j = A j * A i := fun i j => by
    simp only [hA, Matrix.smul_mul, Matrix.mul_smul, hcomm i j]
    exact smul_comm _ _ _
  have hA5 : ∀ i, A i ^ 5 = 1 := fun i => by
    simp only [hA, smul_pow, hY i, smul_smul]
    rw [← ha i, ← mul_pow, inv_mul_cancel₀ (ha0 i), one_pow, one_smul]
  obtain ⟨P, hP, d, hd⟩ := CFSG.RankThree.SubgroupLists.exists_simultaneous_diagonal A hAc
    fun i => ⟨5, by exact_mod_cast h5, hA5 i⟩
  refine ⟨hP.unit, fun i => ⟨a i • d i, ?_⟩⟩
  rw [IsUnit.unit_spec]
  have hY' : Y i = a i • A i := by simp only [hA, smul_smul, mul_inv_cancel₀ (ha0 i), one_smul]
  rw [hY', Matrix.smul_mul, hd i, Matrix.diagonal_smul, Matrix.mul_smul]

end Two

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five
