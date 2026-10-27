module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4Q11Sg

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary GenLocU4QSu4

namespace GenLocU4Q11

open GenLocU4Q11Sg

section Mat

variable {K : Type} [Field K]

@[expose] def Dx11 : Matrix (Fin 4) (Fin 4) K :=
  !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def Dy11 : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

@[expose] def Dz11 : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

theorem diagonal_eq_Dx11 : (Matrix.diagonal ![-1, -1, 1, 1] : Matrix (Fin 4) (Fin 4) K) = Dx11 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Dx11]

theorem Sg1_comm_Dx (ι c : K) : Sg1 ι c * Dx11 = Dx11 * Sg1 ι c := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Sg1, Dx11, Matrix.mul_apply, Fin.sum_univ_four]

theorem Sg1_comm_Dy (ι c : K) : Sg1 ι c * Dy11 = Dy11 * Sg1 ι c := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Sg1, Dy11, Matrix.mul_apply, Fin.sum_univ_four]

theorem SgY_comm_Dx (ι c : K) : SgY ι c * Dx11 = Dx11 * SgY ι c := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [SgY, Dx11, Matrix.mul_apply, Fin.sum_univ_four]

theorem SgY_comm_Dyz (ι c : K) : SgY ι c * (Dy11 * Dz11) = (Dy11 * Dz11) * SgY ι c := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [SgY, Dy11, Dz11, Matrix.mul_apply, Fin.sum_univ_four]

theorem SgZ_comm_Dy (ι c : K) : SgZ ι c * Dy11 = Dy11 * SgZ ι c := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [SgZ, Dy11, Matrix.mul_apply, Fin.sum_univ_four]

theorem SgZ_comm_Dxz (ι c : K) : SgZ ι c * (Dx11 * Dz11) = (Dx11 * Dz11) * SgZ ι c := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [SgZ, Dx11, Dz11, Matrix.mul_apply, Fin.sum_univ_four]

theorem SgX_comm_Dxy (ι c : K) : SgX ι c * (Dx11 * Dy11) = (Dx11 * Dy11) * SgX ι c := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [SgX, Dx11, Dy11, Matrix.mul_apply, Fin.sum_univ_four]

theorem SgX_comm_Dxz (ι c : K) : SgX ι c * (Dx11 * Dz11) = (Dx11 * Dz11) * SgX ι c := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [SgX, Dx11, Dz11, Matrix.mul_apply, Fin.sum_univ_four]

end Mat

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem tv_va (hσ : IsUnitaryInvolution (unitaryInvolution K p f)) {ι : K} (hι : ι * ι = -1)
    (hσι : unitaryInvolution K p f ι = ι) (d : K) (hd : unitaryInvolution K p f d = -d)
    (hc : 2 * d + unitaryInvolution K p f (2 * d) = 0) :
    tv hσ.invol (herm_va hι hσι) hc =
      sgElt1 ι d hι hσι hd * sgEltY ι (-d) hι hσι (by rw [map_neg, hd]) := by
  apply ext_smul
  intro x
  rw [mul_smul, tv_smul]
  show x + (2 * d * herm (unitaryInvolution K p f) ![1, ι, 0, 0] x) • (![1, ι, 0, 0] : Fin 4 → K) =
    Sg1 ι d *ᵥ (SgY ι (-d) *ᵥ x)
  have hσι2 : (iterateFrobenius K p f) ι = ι := hσι
  funext j
  fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Sg1, SgY, herm_def, hσι2]
  · linear_combination (-(d ^ 2 * x 0)) * hι
  · linear_combination ((2 * d - d ^ 2) * x 1) * hι
  · linear_combination (d ^ 2 * x 2) * hι
  · linear_combination (d ^ 2 * x 3) * hι

theorem tv_vb (hσ : IsUnitaryInvolution (unitaryInvolution K p f)) {ι : K} (hι : ι * ι = -1)
    (hσι : unitaryInvolution K p f ι = ι) (d : K) (hd : unitaryInvolution K p f d = -d)
    (hc : 2 * d + unitaryInvolution K p f (2 * d) = 0) :
    tv hσ.invol (herm_vb hι hσι) hc =
      sgElt1 ι d hι hσι hd * sgEltY ι d hι hσι hd := by
  apply ext_smul
  intro x
  rw [mul_smul, tv_smul]
  show x + (2 * d * herm (unitaryInvolution K p f) ![0, 0, 1, ι] x) • (![0, 0, 1, ι] : Fin 4 → K) =
    Sg1 ι d *ᵥ (SgY ι d *ᵥ x)
  have hσι2 : (iterateFrobenius K p f) ι = ι := hσι
  funext j
  fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Sg1, SgY, herm_def, hσι2]
  · linear_combination (d ^ 2 * x 0) * hι
  · linear_combination (d ^ 2 * x 1) * hι
  · linear_combination (-(d ^ 2 * x 2)) * hι
  · linear_combination ((2 * d - d ^ 2) * x 3) * hι

theorem tv_vc (hσ : IsUnitaryInvolution (unitaryInvolution K p f)) {ι : K} (hι : ι * ι = -1)
    (hσι : unitaryInvolution K p f ι = ι) (c : K) (hc' : unitaryInvolution K p f c = -c)
    (hc : c + unitaryInvolution K p f c = 0) :
    tv hσ.invol (herm_vc hι hσι) hc =
      sgElt1 ι c hι hσι hc' * sgEltZ ι c hι hσι hc' := by
  apply ext_smul
  intro x
  rw [mul_smul, tv_smul]
  show x + (c * herm (unitaryInvolution K p f) ![1, ι, 1, ι] x) • (![1, ι, 1, ι] : Fin 4 → K) =
    Sg1 ι c *ᵥ (SgZ ι c *ᵥ x)
  have hσι2 : (iterateFrobenius K p f) ι = ι := hσι
  funext j
  fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Sg1, SgZ, herm_def, hσι2]
  · linear_combination (-(c ^ 2 * x 2)) * hι
  · linear_combination (c * (x 1 + x 3) - c ^ 2 * x 3) * hι
  · linear_combination (-(c ^ 2 * x 0)) * hι
  · linear_combination (c * (x 1 + x 3) - c ^ 2 * x 1) * hι

end GenLocU4Q11

end CFSG.GH74.Generic.BProg.B2
