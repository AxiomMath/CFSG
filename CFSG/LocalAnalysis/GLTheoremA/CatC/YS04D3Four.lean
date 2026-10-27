module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D3
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117F
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeV4InputsLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank CFSG.SectionRank.ClassicalOdd
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance (isElemAbelian_of_forall)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

section Four

variable {K : Type} [Field K]

abbrev D3I4 : Type := Fin 4 ⊕ Fin 4

theorem d3_quadPlus_apply (w : D3I4 → K) :
    StatedQuadPlus 4 K w = ∑ i : Fin 4, w (Sum.inl i) * w (Sum.inr i) := by
  simp [StatedQuadPlus]

theorem d3_rad_isometry (M : Matrix (Fin 4) (Fin 4) K)
    (hM : ∀ y : Fin 4 → K, ∑ i, (M *ᵥ y) i * y i = 0) (w : D3I4 → K) :
    StatedQuadPlus 4 K ((Matrix.fromBlocks (1 : Matrix (Fin 4) (Fin 4) K) M 0 1 :
      Matrix D3I4 D3I4 K) *ᵥ w) = StatedQuadPlus 4 K w := by
  rw [d3_quadPlus_apply, d3_quadPlus_apply]
  simp only [Matrix.fromBlocks_mulVec, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec,
    Matrix.one_mulVec, zero_add, Pi.add_apply]
  have := hM (w ∘ Sum.inr)
  simp only [add_mul, Finset.sum_add_distrib]
  rw [this, add_zero]
  rfl

theorem d3_lv_isometry (A B : Matrix (Fin 4) (Fin 4) K) (hAB : Aᵀ * B = 1) (w : D3I4 → K) :
    StatedQuadPlus 4 K ((Matrix.fromBlocks A 0 0 B : Matrix D3I4 D3I4 K) *ᵥ w) =
      StatedQuadPlus 4 K w := by
  rw [d3_quadPlus_apply, d3_quadPlus_apply]
  simp only [Matrix.fromBlocks_mulVec, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec, add_zero,
    zero_add]
  have h1 : (A *ᵥ (w ∘ Sum.inl)) ⬝ᵥ (B *ᵥ (w ∘ Sum.inr)) = (w ∘ Sum.inl) ⬝ᵥ (w ∘ Sum.inr) := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
      hAB, Matrix.one_mulVec, dotProduct_comm]
  exact h1

def d3AltM (t₁ t₂ : K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, t₁, 0, 0; -t₁, 0, 0, 0; 0, 0, 0, t₂; 0, 0, -t₂, 0]
def d3UA (s₁ s₂ : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, s₁, 0, 0; 0, 1, 0, 0; 0, 0, 1, s₂; 0, 0, 0, 1]
def d3UB (s₁ s₂ : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; -s₁, 1, 0, 0; 0, 0, 1, 0; 0, 0, -s₂, 1]

theorem d3UA_add (s₁ s₂ s₁' s₂' : K) :
    d3UA s₁ s₂ * d3UA s₁' s₂' = d3UA (s₁ + s₁') (s₂ + s₂') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3UA, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem d3UA_zero : d3UA (0 : K) 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3UA]

theorem d3UB_add (s₁ s₂ s₁' s₂' : K) :
    d3UB s₁ s₂ * d3UB s₁' s₂' = d3UB (s₁ + s₁') (s₂ + s₂') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3UB, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem d3UB_zero : d3UB (0 : K) 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3UB]

theorem d3UA_transpose_mul_UB (s₁ s₂ : K) : (d3UA s₁ s₂)ᵀ * d3UB s₁ s₂ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3UA, d3UB, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem d3UA_mul_AltM (s₁ s₂ t₁ t₂ : K) :
    d3UA s₁ s₂ * d3AltM t₁ t₂ = d3AltM t₁ t₂ * d3UB s₁ s₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3UA, d3UB, d3AltM, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem d3AltM_add (t₁ t₂ t₁' t₂' : K) :
    d3AltM t₁ t₂ + d3AltM t₁' t₂' = d3AltM (t₁ + t₁') (t₂ + t₂') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3AltM] <;> ring

theorem d3AltM_zero : d3AltM (0 : K) 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3AltM]

theorem d3AltM_alt (t₁ t₂ : K) (y : Fin 4 → K) : ∑ i, (d3AltM t₁ t₂ *ᵥ y) i * y i = 0 := by
  simp [d3AltM, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

def d3D : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![1, -1, 1, -1]
def d3Z : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![-1, -1, 1, 1]
def d3J : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![1, -1, 1, 1]
def d3I : Matrix (Fin 4) (Fin 4) K := !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem d3D_mul_D : d3D * d3D = (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3D, Matrix.mul_apply, Fin.sum_univ_four]

theorem d3Z_mul_Z : d3Z * d3Z = (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3Z, Matrix.mul_apply, Fin.sum_univ_four]

theorem d3J_mul_J : d3J * d3J = (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3J, Matrix.mul_apply, Fin.sum_univ_four]

theorem d3I_mul_I : d3I * d3Iᵀ = (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3I, Matrix.mul_apply, Fin.sum_univ_four]

theorem d3I_transpose_mul : d3Iᵀ * d3I = (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3I, Matrix.mul_apply, Fin.sum_univ_four]

theorem d3D_transpose : (d3D : Matrix (Fin 4) (Fin 4) K)ᵀ = d3D := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3D, Matrix.diagonal_apply]

theorem d3J_transpose : (d3J : Matrix (Fin 4) (Fin 4) K)ᵀ = d3J := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3J, Matrix.diagonal_apply]

def d3It : Matrix (Fin 4) (Fin 4) K := !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem d3I_transpose : (d3I : Matrix (Fin 4) (Fin 4) K)ᵀ = d3It := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3I, d3It]

theorem d3_comm_IJ : (d3I : Matrix (Fin 4) (Fin 4) K) * d3J * d3It * d3J = d3Z := by
  have h1 : (d3I : Matrix (Fin 4) (Fin 4) K) * d3J =
      !![0, -1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [d3I, d3J, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.diagonal_apply]
  have h2 : (!![0, -1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) K) *
      d3It = !![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [d3It, Matrix.mul_apply, Fin.sum_univ_four]
  rw [h1, h2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3J, d3Z, Matrix.mul_apply, Fin.sum_univ_four,
    Matrix.diagonal_apply]

theorem d3D_UA_D (s₁ s₂ : K) : d3D * d3UA s₁ s₂ * d3D = d3UA (-s₁) (-s₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3D, d3UA, Matrix.mul_apply, Fin.sum_univ_four,
    Matrix.diagonal_apply]

theorem d3D_UB_D (s₁ s₂ : K) : d3D * d3UB s₁ s₂ * d3D = d3UB (-s₁) (-s₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3D, d3UB, Matrix.mul_apply, Fin.sum_univ_four,
    Matrix.diagonal_apply]

theorem d3D_AltM_D (t₁ t₂ : K) : d3D * d3AltM t₁ t₂ * d3D = d3AltM (-t₁) (-t₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3D, d3AltM, Matrix.mul_apply, Fin.sum_univ_four,
    Matrix.diagonal_apply]

theorem d3Z_UA (s₁ s₂ : K) : d3Z * d3UA s₁ s₂ = d3UA s₁ s₂ * d3Z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3Z, d3UA, Matrix.mul_apply, Fin.sum_univ_four,
    Matrix.diagonal_apply]

theorem d3Z_UB (s₁ s₂ : K) : d3Z * d3UB s₁ s₂ = d3UB s₁ s₂ * d3Z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3Z, d3UB, Matrix.mul_apply, Fin.sum_univ_four,
    Matrix.diagonal_apply]

theorem d3Z_AltM (t₁ t₂ : K) : d3Z * d3AltM t₁ t₂ = d3AltM t₁ t₂ * d3Z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d3Z, d3AltM, Matrix.mul_apply, Fin.sum_univ_four,
    Matrix.diagonal_apply]

def d3Rad (M : Matrix (Fin 4) (Fin 4) K) : Matrix D3I4 D3I4 K := Matrix.fromBlocks 1 M 0 1

def d3Lv (A B : Matrix (Fin 4) (Fin 4) K) : Matrix D3I4 D3I4 K := Matrix.fromBlocks A 0 0 B

theorem d3Rad_mul (M M' : Matrix (Fin 4) (Fin 4) K) : d3Rad M * d3Rad M' = d3Rad (M + M') := by
  simp [d3Rad, Matrix.fromBlocks_multiply, add_comm]

theorem d3Lv_mul (A B A' B' : Matrix (Fin 4) (Fin 4) K) :
    d3Lv A B * d3Lv A' B' = d3Lv (A * A') (B * B') := by
  simp [d3Lv, Matrix.fromBlocks_multiply]

theorem d3Lv_rad (A B M M' : Matrix (Fin 4) (Fin 4) K) (h : A * M = M' * B) :
    d3Lv A B * d3Rad M = d3Rad M' * d3Lv A B := by
  simp [d3Lv, d3Rad, Matrix.fromBlocks_multiply, h]

def d3PhiM (a : K × K × K × K) : Matrix D3I4 D3I4 K :=
  d3Rad (d3AltM a.1 a.2.1) * d3Lv (d3UA a.2.2.1 a.2.2.2) (d3UB a.2.2.1 a.2.2.2)

theorem d3PhiM_zero : d3PhiM (0 : K × K × K × K) = 1 := by
  simp [d3PhiM, d3Rad, d3Lv, d3AltM_zero, d3UA_zero, d3UB_zero, Matrix.fromBlocks_one]

theorem d3PhiM_add (a b : K × K × K × K) : d3PhiM (a + b) = d3PhiM a * d3PhiM b := by
  obtain ⟨t₁, t₂, s₁, s₂⟩ := a
  obtain ⟨t₁', t₂', s₁', s₂'⟩ := b
  have hcomm := d3Lv_rad (d3UA s₁ s₂) (d3UB s₁ s₂) (d3AltM t₁' t₂') (d3AltM t₁' t₂')
    (d3UA_mul_AltM s₁ s₂ t₁' t₂')
  simp only [d3PhiM, Prod.mk_add_mk]
  rw [← d3AltM_add, ← d3Rad_mul, ← d3UA_add, ← d3UB_add, ← d3Lv_mul]
  calc d3Rad (d3AltM t₁ t₂) * d3Rad (d3AltM t₁' t₂') * (d3Lv (d3UA s₁ s₂) (d3UB s₁ s₂) *
        d3Lv (d3UA s₁' s₂') (d3UB s₁' s₂'))
      = d3Rad (d3AltM t₁ t₂) * (d3Rad (d3AltM t₁' t₂') * d3Lv (d3UA s₁ s₂) (d3UB s₁ s₂)) *
          d3Lv (d3UA s₁' s₂') (d3UB s₁' s₂') := by simp only [mul_assoc]
    _ = d3Rad (d3AltM t₁ t₂) * (d3Lv (d3UA s₁ s₂) (d3UB s₁ s₂) * d3Rad (d3AltM t₁' t₂')) *
          d3Lv (d3UA s₁' s₂') (d3UB s₁' s₂') := by rw [hcomm]
    _ = _ := by simp only [mul_assoc]

def d3LvGL (A B A' B' : Matrix (Fin 4) (Fin 4) K) (h1 : A * A' = 1) (h2 : A' * A = 1)
    (h3 : B * B' = 1) (h4 : B' * B = 1) : GL D3I4 K :=
  ⟨d3Lv A B, d3Lv A' B', by rw [d3Lv_mul, h1, h3]; simp [d3Lv, Matrix.fromBlocks_one],
    by rw [d3Lv_mul, h2, h4]; simp [d3Lv, Matrix.fromBlocks_one]⟩

theorem d3PhiM_eq (a : K × K × K × K) :
    d3PhiM a = Matrix.fromBlocks (d3UA a.2.2.1 a.2.2.2) (d3AltM a.1 a.2.1 * d3UB a.2.2.1 a.2.2.2) 0
      (d3UB a.2.2.1 a.2.2.2) := by
  simp [d3PhiM, d3Rad, d3Lv, Matrix.fromBlocks_multiply]

theorem d3PhiM_injective : Function.Injective (d3PhiM : K × K × K × K → Matrix D3I4 D3I4 K) := by
  rintro ⟨t₁, t₂, s₁, s₂⟩ ⟨t₁', t₂', s₁', s₂'⟩ h
  rw [d3PhiM_eq, d3PhiM_eq] at h
  have e1 := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 1)
  have e2 := congrFun (congrFun h (Sum.inl 2)) (Sum.inl 3)
  have e3 := congrFun (congrFun h (Sum.inl 0)) (Sum.inr 1)
  have e4 := congrFun (congrFun h (Sum.inl 2)) (Sum.inr 3)
  simp [d3UA, d3UB, d3AltM, Matrix.mul_apply, Fin.sum_univ_four] at e1 e2 e3 e4
  simp [e1, e2, e3, e4]

theorem d3PhiM_isometry (a : K × K × K × K) (w : D3I4 → K) :
    StatedQuadPlus 4 K (d3PhiM a *ᵥ w) = StatedQuadPlus 4 K w := by
  unfold d3PhiM
  rw [← Matrix.mulVec_mulVec]
  have h1 := d3_rad_isometry (d3AltM a.1 a.2.1) (d3AltM_alt a.1 a.2.1) (d3Lv (d3UA a.2.2.1 a.2.2.2)
    (d3UB a.2.2.1 a.2.2.2) *ᵥ w)
  have h2 := d3_lv_isometry (d3UA a.2.2.1 a.2.2.2) (d3UB a.2.2.1 a.2.2.2)
    (d3UA_transpose_mul_UB a.2.2.1 a.2.2.2) w
  exact h1.trans h2

theorem d3PhiM_fix (a : K × K × K × K) :
    d3PhiM a *ᵥ (Pi.single (Sum.inl 0) 1 : D3I4 → K) = Pi.single (Sum.inl 0) 1 := by
  rw [d3PhiM_eq]
  ext (i | i)
  · simp [Matrix.fromBlocks_mulVec, d3UA, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Pi.single_apply]
    fin_cases i <;> simp
  · simp [Matrix.fromBlocks_mulVec, d3UB, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Pi.single_apply]

theorem d3Lv_conj_D (a : K × K × K × K) :
    d3Lv d3D d3D * d3PhiM a * d3Lv d3D d3D = d3PhiM (-a) := by
  obtain ⟨t₁, t₂, s₁, s₂⟩ := a
  have h1 := d3Lv_rad d3D d3D (d3AltM t₁ t₂) (d3D * d3AltM t₁ t₂ * d3D)
    (by rw [mul_assoc, mul_assoc, d3D_mul_D, mul_one])
  unfold d3PhiM
  calc d3Lv d3D d3D * (d3Rad (d3AltM t₁ t₂) * d3Lv (d3UA s₁ s₂) (d3UB s₁ s₂)) * d3Lv d3D d3D
      = (d3Lv d3D d3D * d3Rad (d3AltM t₁ t₂)) * d3Lv (d3UA s₁ s₂) (d3UB s₁ s₂) * d3Lv d3D d3D := by
        simp only [mul_assoc]
    _ = d3Rad (d3D * d3AltM t₁ t₂ * d3D) * (d3Lv d3D d3D * d3Lv (d3UA s₁ s₂) (d3UB s₁ s₂) *
          d3Lv d3D d3D) := by rw [h1]; simp only [mul_assoc]
    _ = _ := by
      rw [d3Lv_mul, d3Lv_mul, d3D_UA_D, d3D_UB_D, d3D_AltM_D]
      rfl

theorem d3Lv_comm_Z (a : K × K × K × K) : d3Lv d3Z d3Z * d3PhiM a = d3PhiM a * d3Lv d3Z d3Z := by
  obtain ⟨t₁, t₂, s₁, s₂⟩ := a
  have h1 := d3Lv_rad d3Z d3Z (d3AltM t₁ t₂) (d3AltM t₁ t₂) (d3Z_AltM t₁ t₂)
  unfold d3PhiM
  calc d3Lv d3Z d3Z * (d3Rad (d3AltM t₁ t₂) * d3Lv (d3UA s₁ s₂) (d3UB s₁ s₂))
      = (d3Lv d3Z d3Z * d3Rad (d3AltM t₁ t₂)) * d3Lv (d3UA s₁ s₂) (d3UB s₁ s₂) := by
        simp only [mul_assoc]
    _ = d3Rad (d3AltM t₁ t₂) * (d3Lv d3Z d3Z * d3Lv (d3UA s₁ s₂) (d3UB s₁ s₂)) := by
        rw [h1]; simp only [mul_assoc]
    _ = d3Rad (d3AltM t₁ t₂) * (d3Lv (d3UA s₁ s₂) (d3UB s₁ s₂) * d3Lv d3Z d3Z) := by
        rw [d3Lv_mul, d3Lv_mul, d3Z_UA, d3Z_UB]
    _ = _ := by simp only [mul_assoc]

noncomputable def d3Phi : Multiplicative (K × K × K × K) →* GL D3I4 K :=
  glOfAdd d3PhiM d3PhiM_zero d3PhiM_add

noncomputable def d3hD : GL D3I4 K :=
  d3LvGL d3D d3D d3D d3D d3D_mul_D d3D_mul_D d3D_mul_D d3D_mul_D

noncomputable def d3uZ : GL D3I4 K :=
  d3LvGL d3Z d3Z d3Z d3Z d3Z_mul_Z d3Z_mul_Z d3Z_mul_Z d3Z_mul_Z

noncomputable def d3g1 : GL D3I4 K :=
  d3LvGL d3I d3I d3It d3It (by rw [← d3I_transpose]; exact d3I_mul_I)
    (by rw [← d3I_transpose]; exact d3I_transpose_mul) (by rw [← d3I_transpose]; exact d3I_mul_I)
    (by rw [← d3I_transpose]; exact d3I_transpose_mul)

noncomputable def d3g2 : GL D3I4 K :=
  d3LvGL d3J d3J d3J d3J d3J_mul_J d3J_mul_J d3J_mul_J d3J_mul_J

theorem d3hD_iso (w : D3I4 → K) :
    StatedQuadPlus 4 K ((d3hD : GL D3I4 K).val *ᵥ w) = StatedQuadPlus 4 K w :=
  d3_lv_isometry d3D d3D (by rw [d3D_transpose, d3D_mul_D]) w

theorem d3g1_iso (w : D3I4 → K) :
    StatedQuadPlus 4 K ((d3g1 : GL D3I4 K).val *ᵥ w) = StatedQuadPlus 4 K w :=
  d3_lv_isometry d3I d3I d3I_transpose_mul w

theorem d3g2_iso (w : D3I4 → K) :
    StatedQuadPlus 4 K ((d3g2 : GL D3I4 K).val *ᵥ w) = StatedQuadPlus 4 K w :=
  d3_lv_isometry d3J d3J (by rw [d3J_transpose, d3J_mul_J]) w

theorem d3Phi_iso (a : Multiplicative (K × K × K × K)) (w : D3I4 → K) :
    StatedQuadPlus 4 K ((d3Phi a : GL D3I4 K).val *ᵥ w) = StatedQuadPlus 4 K w :=
  d3PhiM_isometry a.toAdd w

theorem d3_comm_mem {g₁ g₂ : GL D3I4 K}
    (h₁ : ∀ w, StatedQuadPlus 4 K ((g₁ : GL D3I4 K).val *ᵥ w) = StatedQuadPlus 4 K w)
    (h₂ : ∀ w, StatedQuadPlus 4 K ((g₂ : GL D3I4 K).val *ᵥ w) = StatedQuadPlus 4 K w) :
    ⁅g₁, g₂⁆ ∈ StatedOmega (StatedQuadPlus 4 K) :=
  Subgroup.commutator_mem_commutator (Subgroup.subset_closure h₁) (Subgroup.subset_closure h₂)

theorem d3uZ_eq : (d3uZ : GL D3I4 K) = ⁅(d3g1 : GL D3I4 K), (d3g2 : GL D3I4 K)⁆ := by
  apply Units.ext
  change d3Lv d3Z d3Z = d3Lv d3I d3I * d3Lv d3J d3J * d3Lv d3It d3It * d3Lv d3J d3J
  rw [d3Lv_mul, d3Lv_mul, d3Lv_mul, d3_comm_IJ]

theorem d3uZ_mem : (d3uZ : GL D3I4 K) ∈ StatedOmega (StatedQuadPlus 4 K) := by
  rw [d3uZ_eq]
  exact d3_comm_mem d3g1_iso d3g2_iso

theorem d3uZ_sq : (d3uZ : GL D3I4 K) ^ 2 = 1 := by
  rw [pow_two]
  apply Units.ext
  change (d3Lv d3Z d3Z : Matrix D3I4 D3I4 K) * d3Lv d3Z d3Z = 1
  rw [d3Lv_mul, d3Z_mul_Z]
  simp [d3Lv, Matrix.fromBlocks_one]

theorem d3uZ_comm (a : Multiplicative (K × K × K × K)) :
    (d3uZ : GL D3I4 K) * d3Phi a = d3Phi a * d3uZ :=
  Units.ext (d3Lv_comm_Z a.toAdd)

theorem d3Phi_mem [CharP K 3] (a : Multiplicative (K × K × K × K)) :
    (d3Phi a : GL D3I4 K) ∈ StatedOmega (StatedQuadPlus 4 K) := by
  have hconj : (d3hD : GL D3I4 K) * d3Phi a * d3hD⁻¹ = d3Phi a⁻¹ := by
    apply Units.ext
    change d3Lv d3D d3D * d3PhiM a.toAdd * d3Lv d3D d3D = d3PhiM (a⁻¹).toAdd
    rw [d3Lv_conj_D]
    rfl
  have h3 : a ^ 3 = 1 := pow_char_eq_one (K := K) (p := 3) a
  have hcomm : ⁅(d3hD : GL D3I4 K), d3Phi a⁆ = d3Phi a := by
    rw [commutatorElement_def, hconj, ← map_inv, ← map_mul]
    congr 1
    calc a⁻¹ * a⁻¹ = (a⁻¹ * a⁻¹) * a ^ 3 := by rw [h3, mul_one]
      _ = a := by group
  rw [← hcomm]
  exact d3_comm_mem d3hD_iso (d3Phi_iso a)

theorem d3uZ_not_scalar (h2 : (2 : K) ≠ 0) : (d3uZ : GL D3I4 K) ∉ StatedScalars D3I4 K := by
  rintro ⟨c, hc⟩
  have e1 := congrArg (fun g : GL D3I4 K => (g : Matrix D3I4 D3I4 K) (Sum.inl 0) (Sum.inl 0)) hc
  have e2 := congrArg (fun g : GL D3I4 K => (g : Matrix D3I4 D3I4 K) (Sum.inl 2) (Sum.inl 2)) hc
  simp [d3uZ, d3LvGL, d3Lv, d3Z, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply] at e1 e2
  have h := congrArg (fun x : Kˣ => (x : K)) (e1.symm.trans e2)
  simp only [Units.val_neg, Units.val_one] at h
  exact h2 (by linear_combination (-1 : K) * h)

end Four

theorem exists_four_centralizing_involution_char3 {K : Type} [Field K] [Finite K] {n : ℕ}
    [CharP K 3] (hK : Nat.card K = 3 ^ n) :
    ∃ (F : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K))))
      (ū : StatedProj (StatedOmega (StatedQuadPlus 4 K))),
      IsElemAbelian 3 F ∧ 3 ^ (4 * n) ≤ Nat.card F ∧ ū ^ 2 = 1 ∧ ū ≠ 1 ∧ ∀ s ∈ F, s * ū = ū * s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h3 : (3 : K) = 0 := by
      have := CharP.cast_eq_zero K 3
      simpa using this
    have h1 : (1 : K) = 0 := by linear_combination h3 - h
    exact one_ne_zero h1
  set u : GL D3I4 K := d3uZ with hu
  set Hc : Subgroup (GL D3I4 K) :=
    StatedOmega (StatedQuadPlus 4 K) ⊓ Subgroup.centralizer ({u} : Set (GL D3I4 K)) with hHc
  have hcard : Nat.card (Multiplicative (K × K × K × K)) = 3 ^ (4 * n) := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod, Nat.card_prod, hK,
      ← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  have hH : ∀ a, d3Phi a ∈ Hc := fun a =>
    ⟨d3Phi_mem a, Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact d3uZ_comm a⟩
  have hv : (Pi.single (Sum.inl 0) 1 : D3I4 → K) ≠ 0 := by
    intro h
    have := congrFun h (Sum.inl 0)
    simp at this
  have hrank := le_pRank_statedProj (H := Hc) (p := 3) (k := 4 * n) (by norm_num)
    multiplicative_comm (fun a => pow_char_eq_one (K := K) (p := 3) a) hcard d3Phi
    (glOfAdd_injective d3PhiM_injective) hH hv (fun a => d3PhiM_fix a.toAdd)
  obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3)
    (⊤ : Subgroup (StatedProj Hc))
  obtain ⟨ι₀, hι₀, hι₀mk⟩ := exists_statedProj_map
    (inf_le_left : Hc ≤ StatedOmega (StatedQuadPlus 4 K))
  let ū : StatedProj (StatedOmega (StatedQuadPlus 4 K)) := QuotientGroup.mk ⟨u, d3uZ_mem⟩
  refine ⟨E.map ι₀, ū, ?_, ?_, ?_, ?_, ?_⟩
  · refine isElemAbelian_of_forall ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, isElemAbelian_commute hE ha hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hE.2 a ha, map_one]
  · rw [Subgroup.card_map_of_injective hι₀, hEcard]
    exact Nat.pow_le_pow_right (by norm_num) hrank
  · change (QuotientGroup.mk ⟨u, d3uZ_mem⟩ : StatedProj (StatedOmega (StatedQuadPlus 4 K))) ^ 2 = 1
    rw [← QuotientGroup.mk_pow]
    have : (⟨u, d3uZ_mem⟩ : StatedOmega (StatedQuadPlus 4 K)) ^ 2 = 1 := Subtype.ext d3uZ_sq
    rw [this]
    rfl
  · intro h
    apply d3uZ_not_scalar h2
    have h' := (QuotientGroup.eq_one_iff _).1 h
    exact Subgroup.mem_subgroupOf.1 h'
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective e
    rw [hι₀mk]
    show (QuotientGroup.mk (Subgroup.inclusion inf_le_left g) :
      StatedProj (StatedOmega (StatedQuadPlus 4 K))) * QuotientGroup.mk ⟨u, d3uZ_mem⟩ = _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 g.2.2 u (Set.mem_singleton u)).symm

theorem d3TwoLocalFour_holds : D3TwoLocalFour := by
  intro K _ _ n hK
  have : CharP K 3 :=
    CFSG.Wreathed.OriginalAllPrime.V4InputsW.charP_of_card_eq_pow Nat.prime_three hK
  let e0 : D4Model K ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
    (statedProjectiveReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).symm
  obtain ⟨F, ū, hF, hFc, hū2, hū1, hFū⟩ := exists_four_centralizing_involution_char3 hK
  let e : StatedProj (StatedOmega (StatedQuadPlus 4 K)) ≃* D4Model K := e0.symm
  refine ⟨F.map e.toMonoidHom, e ū, isElemAbelian_map_equiv e hF, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hFc
  · rw [← map_pow, hū2, map_one]
  · intro h
    exact hū1 (e.injective (h.trans (map_one e).symm))
  · rintro _ ⟨s, hs, rfl⟩
    show e s * e ū = e ū * e s
    rw [← map_mul, ← map_mul, hFū s hs]

end CFSG.LocalAnalysis.GLTheoremA
