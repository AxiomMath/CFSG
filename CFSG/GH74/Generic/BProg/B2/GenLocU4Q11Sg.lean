module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4QSu4

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary GenLocU4QSu4

namespace GenLocU4Q11Sg

variable {K : Type} [Field K]

@[expose] def Sg1 (ι c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1 + c, c * ι, 0, 0; c * ι, 1 - c, 0, 0; 0, 0, 1 + c, c * ι; 0, 0, c * ι, 1 - c]

@[expose] def SgY (ι c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1 - c, -(c * ι), 0, 0; -(c * ι), 1 + c, 0, 0; 0, 0, 1 + c, c * ι; 0, 0, c * ι, 1 - c]

@[expose] def SgZ (ι c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, c, c * ι; 0, 1, c * ι, -c; c, c * ι, 1, 0; c * ι, -c, 0, 1]

@[expose] def SgX (ι c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, c, c * ι; 0, 1, c * ι, -c; -c, -(c * ι), 1, 0; -(c * ι), c, 0, 1]

theorem det_Sg1 (ι c : K) (hι : ι * ι = -1) : (Sg1 ι c).det = 1 := by
  simp [Sg1, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  linear_combination (c ^ 4 * (ι * ι + 1) - 2 * c ^ 2) * hι

theorem det_SgY (ι c : K) (hι : ι * ι = -1) : (SgY ι c).det = 1 := by
  simp [SgY, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  linear_combination (c ^ 4 * (ι * ι + 1) - 2 * c ^ 2) * hι

theorem det_SgZ (ι c : K) (hι : ι * ι = -1) : (SgZ ι c).det = 1 := by
  simp [SgZ, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  linear_combination (c ^ 4 * (ι * ι + 1) - 2 * c ^ 2) * hι

theorem det_SgX (ι c : K) (hι : ι * ι = -1) : (SgX ι c).det = 1 := by
  simp [SgX, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  linear_combination (c ^ 4 * (ι * ι + 1) + 2 * c ^ 2) * hι

variable (σ : K ≃+* K)

theorem Sg1_unitary {ι c : K} (hι : ι * ι = -1) (hσι : σ ι = ι) (hc : σ c = -c) :
    ((Sg1 ι c).map σ)ᵀ * Sg1 ι c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Sg1, Matrix.mul_apply, Fin.sum_univ_four, Matrix.map_apply, hσι, hc] <;>
    first | ring1 | linear_combination (-(c * c)) * hι

theorem SgY_unitary {ι c : K} (hι : ι * ι = -1) (hσι : σ ι = ι) (hc : σ c = -c) :
    ((SgY ι c).map σ)ᵀ * SgY ι c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SgY, Matrix.mul_apply, Fin.sum_univ_four, Matrix.map_apply, hσι, hc] <;>
    first | ring1 | linear_combination (-(c * c)) * hι

theorem SgZ_unitary {ι c : K} (hι : ι * ι = -1) (hσι : σ ι = ι) (hc : σ c = -c) :
    ((SgZ ι c).map σ)ᵀ * SgZ ι c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SgZ, Matrix.mul_apply, Fin.sum_univ_four, Matrix.map_apply, hσι, hc] <;>
    first | ring1 | linear_combination (-(c * c)) * hι

theorem SgX_unitary {ι c : K} (hι : ι * ι = -1) (hσι : σ ι = ι) (hc : σ c = c) :
    ((SgX ι c).map σ)ᵀ * SgX ι c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SgX, Matrix.mul_apply, Fin.sum_univ_four, Matrix.map_apply, hσι, hc] <;>
    first | ring1 | linear_combination (-(c * c)) * hι | linear_combination (c * c) * hι


section Elt

variable [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem hfun_sigma : (fun x : K => x ^ (p ^ f)) = unitaryInvolution K p f :=
  funext fun x => (unitaryInvolution_apply K p f x).symm

@[expose] noncomputable def sgElt1 (ι c : K) (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = ι)
    (hc : unitaryInvolution K p f c = -c) : Su K p f 4 :=
  su4Mk (p := p) (f := f) (Sg1 ι c) (det_Sg1 ι c hι)
    (by rw [hfun_sigma (p := p) (f := f)]; exact Sg1_unitary _ hι hσι hc)

@[expose] noncomputable def sgEltY (ι c : K) (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = ι)
    (hc : unitaryInvolution K p f c = -c) : Su K p f 4 :=
  su4Mk (p := p) (f := f) (SgY ι c) (det_SgY ι c hι)
    (by rw [hfun_sigma (p := p) (f := f)]; exact SgY_unitary _ hι hσι hc)

@[expose] noncomputable def sgEltZ (ι c : K) (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = ι)
    (hc : unitaryInvolution K p f c = -c) : Su K p f 4 :=
  su4Mk (p := p) (f := f) (SgZ ι c) (det_SgZ ι c hι)
    (by rw [hfun_sigma (p := p) (f := f)]; exact SgZ_unitary _ hι hσι hc)

@[expose] noncomputable def sgEltX (ι c : K) (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = ι)
    (hc : unitaryInvolution K p f c = c) : Su K p f 4 :=
  su4Mk (p := p) (f := f) (SgX ι c) (det_SgX ι c hι)
    (by rw [hfun_sigma (p := p) (f := f)]; exact SgX_unitary _ hι hσι hc)

end Elt

end GenLocU4Q11Sg

end CFSG.GH74.Generic.BProg.B2
