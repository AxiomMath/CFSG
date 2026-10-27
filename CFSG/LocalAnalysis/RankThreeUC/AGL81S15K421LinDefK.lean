module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421OrbV
import Mathlib.LinearAlgebra.Matrix.Notation

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421LinK

open K421MonoProof K421OrbProof Matrix

@[expose] def CmK : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 1]

@[expose] def JmK : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 0]

@[expose] def cpowK (z : ZMod 3) : Matrix (Fin 2) (Fin 2) (ZMod 2) := CmK ^ z.val

@[expose] def aMatK (x : V3) : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) (ZMod 2) :=
  Matrix.of fun i j => if i.1 = j.1 then cpowK (x i.1) i.2 j.2 else 0

@[expose] def pMatK (π : Equiv.Perm (Fin 3)) : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) (ZMod 2) :=
  Matrix.of fun i j => if i.1 = π j.1 ∧ i.2 = j.2 then 1 else 0

@[expose] def jMatK (ε : Fin 3 → Bool) : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) (ZMod 2) :=
  Matrix.of fun i j => if i.1 = j.1 then (if ε i.1 then JmK else 1) i.2 j.2 else 0

theorem jK_aK : ∀ (ε : Fin 3 → Bool) (x : V3),
    jMatK ε * aMatK x = aMatK (fun b => (if ε b then -1 else 1) * x b) * jMatK ε := by
  unfold jMatK JmK aMatK cpowK CmK
  decide +kernel

theorem pK_aK : ∀ (π : Equiv.Perm (Fin 3)) (y : V3),
    pMatK π * aMatK y = aMatK (fun b => y (π.symm b)) * pMatK π := by
  unfold pMatK aMatK cpowK CmK
  decide +kernel

theorem jK_jK : ∀ ε : Fin 3 → Bool, jMatK ε * jMatK ε = 1 := by
  unfold jMatK JmK
  decide +kernel

theorem pK_pK : ∀ π : Equiv.Perm (Fin 3), pMatK π * pMatK π.symm = 1 := by
  unfold pMatK
  decide +kernel

theorem pK_pK' : ∀ π : Equiv.Perm (Fin 3), pMatK π.symm * pMatK π = 1 := by
  unfold pMatK
  decide +kernel

theorem aK_split : ∀ x : V3, aMatK x =
    aMatK (Pi.single 0 (x 0)) * aMatK (Pi.single 1 (x 1)) * aMatK (Pi.single 2 (x 2)) := by
  unfold aMatK cpowK CmK
  decide +kernel

theorem aK_single_add : ∀ (b : Fin 3) (c d : ZMod 3),
    aMatK (Pi.single b (c + d)) = aMatK (Pi.single b c) * aMatK (Pi.single b d) := by
  unfold aMatK cpowK CmK
  decide +kernel

theorem aK_comm : ∀ (b b' : Fin 3) (c d : ZMod 3),
    aMatK (Pi.single b c) * aMatK (Pi.single b' d) =
      aMatK (Pi.single b' d) * aMatK (Pi.single b c) := by
  unfold aMatK cpowK CmK
  decide +kernel

theorem mul_six {M : Type*} [Monoid M] (a0 a1 a2 b0 b1 b2 : M) (h01 : Commute b0 a1)
    (h02 : Commute b0 a2) (h12 : Commute b1 a2) :
    a0 * b0 * (a1 * b1) * (a2 * b2) = a0 * a1 * a2 * (b0 * b1 * b2) := by
  simp only [mul_assoc]
  rw [h01.left_comm, h12.left_comm, h02.left_comm]

theorem aMat_add (x y : V3) : aMatK (x + y) = aMatK x * aMatK y := by
  rw [aK_split (x + y), aK_split x, aK_split y, Pi.add_apply, Pi.add_apply, Pi.add_apply,
    aK_single_add, aK_single_add, aK_single_add]
  exact mul_six _ _ _ _ _ _ (aK_comm _ _ _ _) (aK_comm _ _ _ _) (aK_comm _ _ _ _)

theorem nMat_mul_inv (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) :
    (pMatK π * jMatK ε) * (jMatK ε * pMatK π.symm) = 1 := by
  rw [mul_assoc, ← mul_assoc (jMatK ε), jK_jK, one_mul, pK_pK]

theorem nMat_inv_mul (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) :
    (jMatK ε * pMatK π.symm) * (pMatK π * jMatK ε) = 1 := by
  rw [mul_assoc, ← mul_assoc (pMatK π.symm), pK_pK', one_mul, jK_jK]

theorem nMat_aMat (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) (x : V3) :
    (pMatK π * jMatK ε) * aMatK x = aMatK (act π ε x) * (pMatK π * jMatK ε) := by
  rw [mul_assoc, jK_aK, ← mul_assoc, pK_aK, mul_assoc]
  rfl

end K421LinK

end CFSG.LocalAnalysis.RankThreeUC.S15
