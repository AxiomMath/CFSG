module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerC3Plane
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3.Model

open CFSG.Open CFSG.Open.StatedAPI CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3.Plane Matrix

noncomputable section

variable (K : Type) [Field K]

@[expose] def Jm : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K := fromBlocks 0 1 (-1) 0

@[expose] def Bsp : LinearMap.BilinForm K ((Fin 3 ⊕ Fin 3) → K) := Matrix.toBilin' (Jm K)

theorem Jm_ll (i j : Fin 3) : Jm K (Sum.inl i) (Sum.inl j) = 0 := by
  simp [Jm, Matrix.fromBlocks_apply₁₁]

theorem Jm_lr (i j : Fin 3) : Jm K (Sum.inl i) (Sum.inr j) = if i = j then 1 else 0 := by
  simp [Jm, Matrix.fromBlocks_apply₁₂, Matrix.one_apply]

theorem Jm_rl (i j : Fin 3) : Jm K (Sum.inr i) (Sum.inl j) = if i = j then -1 else 0 := by
  simp only [Jm, Matrix.fromBlocks_apply₂₁, Matrix.neg_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem Jm_rr (i j : Fin 3) : Jm K (Sum.inr i) (Sum.inr j) = 0 := by
  simp [Jm, Matrix.fromBlocks_apply₂₂]

theorem Bsp_apply (v w : (Fin 3 ⊕ Fin 3) → K) :
    Bsp K v w = ∑ i : Fin 3, (v (Sum.inl i) * w (Sum.inr i) - v (Sum.inr i) * w (Sum.inl i)) := by
  simp only [Bsp, Matrix.toBilin'_apply, Fintype.sum_sum_type, Jm_ll, Jm_lr, Jm_rl, Jm_rr,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  simp only [ite_mul, zero_mul, one_mul, neg_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_neg_distrib, ite_mul, mul_ite, mul_one, mul_neg,
    mul_zero, Finset.sum_const_zero, zero_add, add_zero, sub_eq_add_neg]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem Bsp_halt : ∀ v : (Fin 3 ⊕ Fin 3) → K, Bsp K v v = 0 := by
  intro v
  rw [Bsp_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  ring
theorem Bsp_nd : ∀ v : (Fin 3 ⊕ Fin 3) → K, (∀ w, Bsp K v w = 0) → v = 0 := by
  intro v hv
  have hl : ∀ i : Fin 3, v (Sum.inl i) = 0 := by
    intro i
    have h := hv (Pi.single (Sum.inr i) 1)
    rw [Bsp_apply] at h
    simpa [Pi.single_apply] using h
  have hr : ∀ i : Fin 3, v (Sum.inr i) = 0 := by
    intro i
    have h := hv (Pi.single (Sum.inl i) 1)
    rw [Bsp_apply] at h
    simpa [Pi.single_apply] using h
  funext x
  rcases x with i | i
  · exact hl i
  · exact hr i

theorem Bsp_comp_mem (g : GL (Fin 3 ⊕ Fin 3) K) (hg : g ∈ StatedSp 3 K) (u v : (Fin 3 ⊕ Fin 3) → K) :
    Bsp K (Matrix.toLin' (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) u)
      (Matrix.toLin' (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) v) = Bsp K u v := by
  have hg' : (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)ᵀ * Jm K *
      (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = Jm K := mem_statedSp_iff.1 hg
  have key := Matrix.toBilin'_comp (Jm K) (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
    (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
  rw [hg'] at key
  have := congrArg (fun B : LinearMap.BilinForm K ((Fin 3 ⊕ Fin 3) → K) => B u v) key
  simpa [Bsp] using this

structure PlaneData (P : Module.End K ((Fin 3 ⊕ Fin 3) → K)) where
  hP : P * P = P
  hPa : ∀ u v, Bsp K (P u) v = Bsp K u (P v)
  S : SympPair (Bsp K) P

variable {K} {P : Module.End K ((Fin 3 ⊕ Fin 3) → K)}

theorem Phi_matrix_symp (D : PlaneData K P) (A : Matrix (Fin 2) (Fin 2) K) (hdet : A.det = 1) :
    (LinearMap.toMatrix' (Phi D.S A))ᵀ * Jm K * LinearMap.toMatrix' (Phi D.S A) = Jm K := by
  have key := Matrix.toBilin'_comp (Jm K) (LinearMap.toMatrix' (Phi D.S A)) (LinearMap.toMatrix' (Phi D.S A))
  simp only [Matrix.toLin'_toMatrix'] at key
  have h2 : (Matrix.toBilin' (Jm K)).comp (Phi D.S A) (Phi D.S A) = Matrix.toBilin' (Jm K) := by
    apply LinearMap.ext₂
    intro u v
    simp only [LinearMap.BilinForm.comp_apply]
    exact Phi_bilin D.S (Bsp_halt K) D.hP D.hPa A hdet u v
  rw [h2] at key
  exact Matrix.toBilin'.injective key.symm

theorem Phi_mul_mat (D : PlaneData K P) (A B : Matrix (Fin 2) (Fin 2) K) :
    Phi D.S A * Phi D.S B = Phi D.S (A * B) :=
  LinearMap.ext fun v => Phi_mul D.S (Bsp_halt K) D.hP A B v

@[expose] def PhiGL (D : PlaneData K P) (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    GL (Fin 3 ⊕ Fin 3) K :=
  Units.mk (LinearMap.toMatrix' (Phi D.S A.1)) (LinearMap.toMatrix' (Phi D.S A⁻¹.1))
    (by
      rw [← LinearMap.toMatrix'_mul, Phi_mul_mat D, ← Matrix.SpecialLinearGroup.coe_mul,
        mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Phi_one D.S D.hP, LinearMap.toMatrix'_one])
    (by
      rw [← LinearMap.toMatrix'_mul, Phi_mul_mat D, ← Matrix.SpecialLinearGroup.coe_mul,
        inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Phi_one D.S D.hP, LinearMap.toMatrix'_one])

theorem PhiGL_mem (D : PlaneData K P) (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    PhiGL D A ∈ StatedSp 3 K := by
  rw [mem_statedSp_iff]
  exact Phi_matrix_symp D A.1 A.2

@[expose] def ΦSp (D : PlaneData K P) : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 3 K where
  toFun A := ⟨PhiGL D A, PhiGL_mem D A⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    simp only [PhiGL, Units.val_mk, Matrix.SpecialLinearGroup.coe_one, Phi_one D.S D.hP,
      LinearMap.toMatrix'_one, Subgroup.coe_one, Units.val_one]
  map_mul' A B := by
    apply Subtype.ext
    apply Units.ext
    simp only [PhiGL, Units.val_mk, Subgroup.coe_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_mul]
    rw [← LinearMap.toMatrix'_mul, Phi_mul_mat D]

end

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3.Model

end
