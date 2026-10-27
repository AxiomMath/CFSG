module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.BNFCheck
public import CFSG.Sporadic.Co1.Module.CoTwoNorton

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B3B

open CFSG.Sporadic.Co1.Module.CoTwo
open scoped Matrix

@[expose] def tMat (k : ℕ) : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  Matrix.of fun i j =>
    if j.val < 4 then (((nfXData.getD (4 * k + j.val) []).getD i.val 0 : ℕ) : ZMod 3)
    else (((nfYData.getD (4 * k + (j.val - 4)) []).getD i.val 0 : ℕ) : ZMod 3)

@[expose] def tA : Matrix (Fin 8) (Fin 8) (ZMod 3) := !![2, 2, 0, 2, 1, 0, 2, 0;
    2, 0, 1, 2, 2, 1, 1, 2;
    2, 2, 0, 1, 1, 0, 0, 0;
    2, 0, 1, 2, 0, 0, 2, 2;
    0, 2, 2, 1, 0, 0, 0, 0;
    0, 2, 1, 1, 0, 2, 0, 2;
    2, 2, 0, 0, 1, 2, 2, 1;
    2, 2, 1, 1, 1, 2, 0, 2]

@[expose] def tB : Matrix (Fin 8) (Fin 8) (ZMod 3) := !![1, 2, 1, 1, 1, 2, 0, 2;
    1, 0, 1, 0, 0, 2, 0, 0;
    0, 2, 1, 1, 0, 1, 1, 0;
    2, 2, 0, 0, 1, 1, 0, 0;
    0, 1, 0, 1, 2, 0, 0, 1;
    0, 2, 2, 2, 1, 0, 2, 2;
    2, 0, 0, 0, 0, 1, 0, 0;
    0, 2, 0, 1, 1, 1, 0, 0]

theorem tMat_zero : tMat 0 = tA := by decide

theorem tMat_one : tMat 1 = tB := by decide

@[expose] def hA : Matrix (Fin 8) (Fin 8) (ZMod 3) := !![1, 2, 2, 1, 0, 1, 1, 1;
    2, 1, 1, 2, 1, 2, 0, 2;
    0, 0, 0, 1, 2, 2, 1, 2;
    0, 0, 0, 0, 2, 1, 1, 0;
    0, 1, 2, 2, 2, 0, 1, 2;
    0, 1, 2, 0, 1, 1, 1, 1;
    2, 1, 1, 1, 0, 0, 1, 1;
    1, 1, 2, 1, 0, 0, 1, 2]

@[expose] def hB : Matrix (Fin 8) (Fin 8) (ZMod 3) := !![1, 2, 2, 1, 1, 0, 1, 0;
    0, 2, 1, 1, 2, 0, 0, 2;
    1, 0, 1, 2, 0, 0, 2, 1;
    2, 1, 2, 0, 0, 1, 0, 2;
    1, 2, 1, 1, 0, 0, 2, 2;
    0, 1, 2, 1, 0, 2, 2, 0;
    0, 0, 0, 2, 0, 0, 2, 2;
    2, 1, 1, 2, 1, 1, 0, 0]

set_option maxRecDepth 100000 in
theorem pow_sixty_tA_tB : (tA * tB) ^ 60 = hA := by decide

set_option maxRecDepth 100000 in
theorem pow_sixty_tB_tA : (tB * tA) ^ 60 = hB := by decide

@[expose] def hM : Fin 2 → Matrix (Fin 8) (Fin 8) (ZMod 3) := ![hA, hB]

@[expose] def nTheta : List (List (Fin 2)) := [[0], [0, 0], [0, 0, 1], [0, 1, 0]]

@[expose] def nP : Matrix (Fin 8) (Fin 8) (ZMod 3) := !![1, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 1, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def nP' : Matrix (Fin 8) (Fin 8) (ZMod 3) := !![0, 0, 0, 0, 1, 0, 0, 0;
    1, 0, 0, 0, 2, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 2, 0, 0, 0;
    0, 0, 0, 1, 2, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def nQ : Matrix (Fin 8) (Fin 8) (ZMod 3) := !![0, 1, 1, 1, 1, 0, 2, 0;
    1, 0, 2, 1, 1, 2, 2, 1;
    0, 0, 1, 1, 2, 1, 1, 0;
    1, 0, 0, 2, 1, 1, 0, 0;
    1, 0, 2, 1, 2, 1, 2, 0;
    2, 0, 2, 0, 2, 0, 1, 1;
    2, 0, 0, 2, 1, 0, 1, 2;
    2, 0, 0, 0, 1, 0, 1, 2]

@[expose] def nQ' : Matrix (Fin 8) (Fin 8) (ZMod 3) := !![0, 0, 1, 0, 2, 2, 0, 2;
    1, 2, 1, 0, 1, 2, 2, 2;
    0, 2, 1, 2, 2, 2, 0, 1;
    0, 0, 0, 0, 0, 0, 2, 1;
    0, 0, 1, 2, 0, 1, 2, 2;
    0, 0, 1, 2, 1, 0, 0, 0;
    0, 1, 0, 1, 0, 2, 0, 0;
    0, 1, 0, 0, 1, 1, 2, 2]

@[expose] def nuV (k : ℕ) : Fin 8 → ZMod 3 :=
  ([![1, 0, 1, 1, 1, 0, 0, 0],
    ![1, 0, 0, 2, 0, 0, 1, 1],
    ![2, 1, 1, 1, 0, 0, 2, 0],
    ![2, 2, 2, 1, 1, 2, 0, 0],
    ![1, 1, 2, 1, 1, 1, 2, 0],
    ![0, 1, 0, 1, 1, 2, 0, 2],
    ![2, 1, 1, 2, 2, 0, 2, 0],
    ![1, 0, 2, 1, 0, 0, 1, 0]] : List (Fin 8 → ZMod 3)).getD k 0

@[expose] def nparV (k : ℕ) : ℕ := [0, 0, 0, 1, 1, 2, 4, 5].getD k 0

@[expose] def nlabV (k : ℕ) : Fin 2 := ([0, 0, 1, 0, 1, 1, 0, 0] : List (Fin 2)).getD k 0

@[expose] def nVi : Matrix (Fin 8) (Fin 8) (ZMod 3) := !![1, 1, 1, 1, 1, 2, 2, 1;
    1, 1, 0, 1, 1, 0, 1, 0;
    2, 2, 1, 1, 2, 1, 1, 1;
    1, 0, 2, 0, 0, 2, 1, 1;
    2, 1, 2, 1, 1, 0, 2, 0;
    1, 1, 0, 1, 1, 0, 1, 2;
    2, 0, 2, 0, 2, 1, 0, 1;
    2, 2, 2, 1, 1, 2, 0, 2]

@[expose] def nuW (k : ℕ) : Fin 8 → ZMod 3 :=
  ([![0, 1, 1, 1, 1, 0, 2, 0],
    ![0, 1, 2, 1, 1, 2, 2, 2],
    ![1, 2, 2, 2, 2, 1, 2, 2],
    ![2, 2, 1, 1, 2, 0, 1, 1],
    ![0, 0, 0, 1, 1, 1, 2, 0],
    ![2, 2, 1, 0, 0, 0, 0, 2],
    ![1, 0, 1, 0, 1, 0, 0, 0],
    ![2, 2, 1, 0, 1, 2, 2, 0]] : List (Fin 8 → ZMod 3)).getD k 0

@[expose] def nparW (k : ℕ) : ℕ := [0, 0, 0, 1, 1, 2, 2, 5].getD k 0

@[expose] def nlabW (k : ℕ) : Fin 2 := ([0, 0, 1, 0, 1, 0, 1, 0] : List (Fin 2)).getD k 0

@[expose] def nWi : Matrix (Fin 8) (Fin 8) (ZMod 3) := !![0, 2, 2, 0, 1, 0, 1, 0;
    1, 2, 0, 2, 2, 2, 0, 0;
    2, 0, 2, 2, 2, 2, 0, 0;
    0, 2, 0, 0, 0, 2, 2, 1;
    1, 0, 0, 1, 2, 1, 0, 2;
    0, 0, 1, 2, 2, 1, 2, 0;
    1, 0, 1, 1, 2, 1, 1, 0;
    2, 1, 2, 1, 2, 0, 0, 2]

theorem nP_mul : nP * nP' = 1 := by decide

theorem nQ_mul : nQ * nQ' = 1 := by decide

set_option maxRecDepth 100000 in
theorem nDiag : nQ * polyMat hM nTheta * nP = diagOne (0 : Fin 8) := by decide

theorem nSpinV : IsSpin hM (nP *ᵥ Pi.single 0 1) nuV nparV nlabV := by
  refine ⟨by decide, fun k hk0 hk8 => ?_⟩
  interval_cases k <;> decide

theorem nVi_mul : nVi * colsMat nuV = 1 := by decide

theorem nSpinW : IsSpin (fun i => (hM i)ᵀ) (nQ 0) nuW nparW nlabW := by
  refine ⟨by decide, fun k hk0 hk8 => ?_⟩
  interval_cases k <;> decide

theorem nWi_mul : nWi * colsMat nuW = 1 := by decide

theorem irred_hAB (U : Submodule (ZMod 3) (Fin 8 → ZMod 3))
    (hU : ∀ i, ∀ x ∈ U, hM i *ᵥ x ∈ U) : U = ⊥ ∨ U = ⊤ :=
  norton_criterion hM nTheta 0 nP_mul nQ_mul nDiag nSpinV nVi_mul nSpinW nWi_mul U hU

end CFSG.HardMathSupport.Solomon.Coordinator.B3B
