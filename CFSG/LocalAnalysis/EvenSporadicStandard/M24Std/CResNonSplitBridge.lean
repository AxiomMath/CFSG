module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResNonSplit
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Sym6Act

public section

namespace CFSG.EvenSporadicStandard.M24Std.Sym6

open Subgroup CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint

theorem qdNorm_one : QdNorm 1 := fun s => by simp

theorem qdNorm_pow {g : S24} (hg : QdNorm g) : ∀ n : ℕ, QdNorm (g ^ n)
  | 0 => by simpa using qdNorm_one
  | n + 1 => by rw [pow_succ]; exact (qdNorm_pow hg n).mul hg


theorem tetAct_one : tetAct 1 qdNorm_one = 1 := by
  refine Equiv.ext fun i => ?_
  rw [tetAct_apply]
  simp [tetIdx_tetRep]

theorem tetAct_pow {g : S24} (hg : QdNorm g) :
    ∀ n : ℕ, tetAct (g ^ n) (qdNorm_pow hg n) = tetAct g hg ^ n
  | 0 => by simpa using tetAct_one
  | n + 1 => by
    have h := tetAct_mul (qdNorm_pow hg n) hg
    simp only [pow_succ]
    rw [← tetAct_pow hg n]
    exact h

theorem qdNorm_nsS (k : ℕ) : QdNorm (nsS k) :=
  ((qdNorm_pow qdNorm_sxT k).mul qdNorm_sxS).mul (qdNorm_pow qdNorm_sxT (6 - k))

theorem tetAct_nsS (k : ℕ) : tetAct (nsS k) (qdNorm_nsS k) =
    finRotate 6 ^ k * Equiv.swap 0 1 * finRotate 6 ^ (6 - k) := by
  have h := tetAct_mul ((qdNorm_pow qdNorm_sxT k).mul qdNorm_sxS) (qdNorm_pow qdNorm_sxT (6 - k))
  rw [tetAct_mul (qdNorm_pow qdNorm_sxT k) qdNorm_sxS, tetAct_pow qdNorm_sxT k,
    tetAct_pow qdNorm_sxT (6 - k), tetAct_sxS, tetAct_sxT] at h
  exact h

theorem qdNorm_nsX : QdNorm nsX := qdNorm_sxT.mul qdNorm_sxT

theorem qdNorm_nsG : QdNorm nsG := ((qdNorm_nsS 3).mul (qdNorm_nsS 4)).mul (qdNorm_nsS 3)

theorem qdNorm_nsY : QdNorm nsY := (qdNorm_nsG.mul qdNorm_nsX).mul qdNorm_nsG

theorem tetAct_nsX : tetAct nsX qdNorm_nsX = finRotate 6 * finRotate 6 := by
  have h := tetAct_mul qdNorm_sxT qdNorm_sxT
  rwa [tetAct_sxT] at h

theorem tetAct_nsG : tetAct nsG qdNorm_nsG =
    (finRotate 6 ^ 3 * Equiv.swap 0 1 * finRotate 6 ^ (6 - 3)) *
      (finRotate 6 ^ 4 * Equiv.swap 0 1 * finRotate 6 ^ (6 - 4)) *
      (finRotate 6 ^ 3 * Equiv.swap 0 1 * finRotate 6 ^ (6 - 3)) := by
  have h := tetAct_mul ((qdNorm_nsS 3).mul (qdNorm_nsS 4)) (qdNorm_nsS 3)
  rw [tetAct_mul (qdNorm_nsS 3) (qdNorm_nsS 4), tetAct_nsS, tetAct_nsS] at h
  exact h

theorem tetAct_nsY : tetAct nsY qdNorm_nsY =
    tetAct nsG qdNorm_nsG * tetAct nsX qdNorm_nsX * tetAct nsG qdNorm_nsG := by
  have h := tetAct_mul (qdNorm_nsG.mul qdNorm_nsX) qdNorm_nsG
  rw [tetAct_mul qdNorm_nsG qdNorm_nsX] at h
  exact h

set_option maxRecDepth 100000 in
theorem tet_nonsplit_perm :
    tetAct nsX qdNorm_nsX ∈ alternatingGroup (Fin 6) ∧
      tetAct nsY qdNorm_nsY ∈ alternatingGroup (Fin 6) ∧
      tetAct nsX qdNorm_nsX * tetAct nsY qdNorm_nsY =
        tetAct nsY qdNorm_nsY * tetAct nsX qdNorm_nsX := by
  rw [tetAct_nsY, tetAct_nsG, tetAct_nsX]
  refine ⟨?_, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup]; decide
  · rw [Equiv.Perm.mem_alternatingGroup]; decide
  · decide

end CFSG.EvenSporadicStandard.M24Std.Sym6
