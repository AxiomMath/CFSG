module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421OrbV
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinDefK

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421LinProof

open K421MonoProof K421OrbProof Matrix

abbrev F2 : Type := ZMod 2

abbrev Idx : Type := Fin 3 × Fin 2

@[expose] def Cm : Matrix (Fin 2) (Fin 2) F2 := !![0, 1; 1, 1]

@[expose] def Jm : Matrix (Fin 2) (Fin 2) F2 := !![0, 1; 1, 0]

@[expose] def cpow (z : ZMod 3) : Matrix (Fin 2) (Fin 2) F2 := Cm ^ z.val

@[expose] def aMat (x : V3) : Matrix Idx Idx F2 :=
  Matrix.of fun i j => if i.1 = j.1 then cpow (x i.1) i.2 j.2 else 0

@[expose] def sMat : Matrix Idx Idx F2 :=
  Matrix.of fun i j => if i.1 = j.1 + 1 ∧ i.2 = j.2 then 1 else 0

@[expose] def fMat : Matrix Idx Idx F2 :=
  Matrix.of fun i j => (Cm ^ (i.1.val * j.1.val)) i.2 j.2

@[expose] def fInv : Matrix Idx Idx F2 :=
  Matrix.of fun i j => (Cm ^ (2 * (i.1.val * j.1.val))) i.2 j.2

@[expose] def pMat (π : Equiv.Perm (Fin 3)) : Matrix Idx Idx F2 :=
  Matrix.of fun i j => if i.1 = π j.1 ∧ i.2 = j.2 then 1 else 0

@[expose] def jMat (ε : Fin 3 → Bool) : Matrix Idx Idx F2 :=
  Matrix.of fun i j => if i.1 = j.1 then (if ε i.1 then Jm else 1) i.2 j.2 else 0

theorem aMat_add : ∀ x y : V3, aMat (x + y) = aMat x * aMat y := K421LinK.aMat_add

theorem aMat_zero : aMat 0 = 1 := by
  unfold aMat cpow Cm
  decide +kernel

theorem aMat_inj : ∀ x y : V3, aMat x = aMat y → x = y := by
  unfold aMat cpow Cm
  decide +kernel

theorem sMat_cube : sMat * (sMat * sMat) = 1 := by
  unfold sMat
  decide +kernel

theorem sMat_cube' : (sMat * sMat) * sMat = 1 := by
  unfold sMat
  decide +kernel

theorem sMat_aMat : ∀ x : V3, sMat * aMat x = aMat (shiftV x) * sMat := by
  unfold sMat aMat cpow Cm shiftV
  decide +kernel

theorem sMat_ne_aMat : ∀ x : V3, sMat ≠ aMat x := by
  unfold sMat aMat cpow Cm
  decide +kernel

theorem sMat_sq_ne_aMat : ∀ x : V3, sMat * sMat ≠ aMat x := by
  unfold sMat aMat cpow Cm
  decide +kernel

theorem fMat_mul_fInv : fMat * fInv = 1 := by
  unfold fMat fInv Cm
  decide +kernel

theorem fInv_mul_fMat : fInv * fMat = 1 := by
  unfold fMat fInv Cm
  decide +kernel

theorem fInv_sMat_fMat : fInv * sMat * fMat = aMat ![0, 2, 1] := by
  unfold fMat fInv sMat aMat cpow Cm
  decide +kernel

theorem fInv_aMat_fMat : ∀ c : ZMod 3,
    fInv * aMat (fun _ => c) * fMat = aMat (fun _ => c) := by
  unfold fMat fInv aMat cpow Cm
  decide +kernel

theorem nMat_mul_inv : ∀ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool),
    (pMat π * jMat ε) * (jMat ε * pMat π.symm) = 1 :=
  K421LinK.nMat_mul_inv

theorem nMat_inv_mul : ∀ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool),
    (jMat ε * pMat π.symm) * (pMat π * jMat ε) = 1 :=
  K421LinK.nMat_inv_mul

theorem nMat_aMat : ∀ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) (x : V3),
    (pMat π * jMat ε) * aMat x = aMat (act π ε x) * (pMat π * jMat ε) :=
  K421LinK.nMat_aMat

end K421LinProof

end CFSG.LocalAnalysis.RankThreeUC.S15
