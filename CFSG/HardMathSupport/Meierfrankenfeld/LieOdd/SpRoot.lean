module

public import CFSG.LargeExtraspecial.A2ModFrCMat
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpTrace

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix CFSG.Assembly.LowTwoRank CFSG.LargeExtraspecial.A2Mod.FrC
open CFSG.LieType.Universal.Symplectic

variable {K : Type} [Field K] {r : ℕ}

@[expose] noncomputable def leviGL (A : GL (Fin r) K) : StatedSp r K :=
  ⟨⟨fromBlocks (A : Matrix (Fin r) (Fin r) K) 0 0
        ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ,
      fromBlocks ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) 0 0
        (A : Matrix (Fin r) (Fin r) K)ᵀ, by
        rw [fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ← transpose_mul,
          Units.mul_inv, transpose_one, fromBlocks_one], by
        rw [fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ← transpose_mul,
          Units.inv_mul, transpose_one, fromBlocks_one]⟩, by
      rw [mem_statedSp_iff]
      simp only [fromBlocks_transpose, transpose_zero, transpose_transpose,
        fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
        Matrix.mul_neg, Matrix.neg_mul, ← transpose_mul, Units.inv_mul, transpose_one,
        neg_zero]⟩

@[simp]
theorem mat_leviGL (A : GL (Fin r) K) :
    SpExtras.mat r K (leviGL A) = fromBlocks (A : Matrix (Fin r) (Fin r) K) 0 0
      ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ :=
  rfl

@[expose] noncomputable def levGL : GL (Fin r) K →* StatedSp r K where
  toFun := leviGL
  map_one' := ext_mat (by
    simp only [mat_leviGL, inv_one, Units.val_one, transpose_one, fromBlocks_one]
    rfl)
  map_mul' A B := ext_mat (by
    simp only [map_mul, mat_leviGL, fromBlocks_multiply, _root_.mul_inv_rev, Units.val_mul,
      transpose_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add])

@[simp]
theorem mat_levGL (A : GL (Fin r) K) :
    SpExtras.mat r K (levGL A) = fromBlocks (A : Matrix (Fin r) (Fin r) K) 0 0
      ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ :=
  rfl

theorem levGL_conj_lower (A : GL (Fin r) K) {S S' : Matrix (Fin r) (Fin r) K} (hS : Sᵀ = S)
    (hS' : S'ᵀ = S')
    (h : S' = ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ * S *
      ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)) :
    levGL A * lower S hS * (levGL A)⁻¹ = lower S' hS' := by
  subst h
  refine ext_mat ?_
  rw [← map_inv, map_mul, map_mul, mat_levGL, mat_levGL, mat_lower, mat_lower, inv_inv,
    fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    Units.mul_inv, Matrix.mul_assoc, ← transpose_mul, transpose_one]

section Root

variable {F : Type} [Field F] [Algebra K F] [FiniteDimensional K F]
variable (β : Module.Basis (Fin r) K F)

@[expose] noncomputable def rootEl (a : F) : StatedSp r K := lower (gram β a) (gram_transpose β a)

theorem mat_rootEl (a : F) :
    SpExtras.mat r K (rootEl β a) = fromBlocks 1 0 (gram β a) 1 := rfl

@[expose] noncomputable def rootHom : Multiplicative F →* StatedSp r K where
  toFun a := rootEl β a.toAdd
  map_one' := ext_mat (by
    rw [mat_rootEl, toAdd_one, gram_zero, fromBlocks_one]
    rfl)
  map_mul' a b := ext_mat (by
    rw [toAdd_mul, map_mul, mat_rootEl, mat_rootEl, mat_rootEl, gram_add, fromBlocks_multiply]
    simp [add_comm])

theorem rootHom_apply (a : F) : rootHom β (Multiplicative.ofAdd a) = rootEl β a := rfl

@[expose] noncomputable def mulGL : Fˣ →* GL (Fin r) K :=
  Units.map (MonoidHom.ofClass (Algebra.leftMulMatrix β))

theorem coe_mulGL (b : Fˣ) :
    ((mulGL β b : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = Algebra.leftMulMatrix β (b : F) :=
  rfl

@[expose] noncomputable def torusHom : Fˣ →* StatedSp r K :=
  levGL.comp ((mulGL β).comp invMonoidHom)

theorem torusHom_conj (b : Fˣ) (a : F) :
    torusHom β b * rootEl β a * (torusHom β b)⁻¹ = rootEl β ((b : F) * b * a) := by
  have hinv : (((mulGL β (b⁻¹)) : GL (Fin r) K)⁻¹ : GL (Fin r) K) = mulGL β b := by
    rw [← map_inv, inv_inv]
  refine levGL_conj_lower (mulGL β b⁻¹) (gram_transpose β a) (gram_transpose β _) ?_
  rw [hinv, coe_mulGL]
  exact (gram_conj β a (b : F)).symm

section Proj

@[expose] noncomputable def uProj : Multiplicative F →* StatedProj (StatedSp r K) :=
  (QuotientGroup.mk' _).comp (rootHom β)

@[expose] noncomputable def tProj : Fˣ →* StatedProj (StatedSp r K) :=
  (QuotientGroup.mk' _).comp (torusHom β)

theorem tProj_conj (b : Fˣ) (a : F) :
    tProj β b * uProj β (Multiplicative.ofAdd a) * (tProj β b)⁻¹ =
      uProj β (Multiplicative.ofAdd ((b : F) ^ 2 * a)) := by
  have key : torusHom β b * rootHom β (Multiplicative.ofAdd a) * (torusHom β b)⁻¹ =
      rootHom β (Multiplicative.ofAdd ((b : F) ^ 2 * a)) := by
    rw [rootHom_apply, torusHom_conj, rootHom_apply]
    congr 2
    ring
  have := congrArg (QuotientGroup.mk' ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf
    (StatedSp r K))) key
  simpa [tProj, uProj, map_mul, map_inv] using this

theorem uProj_injective (hr : 0 < r) (htr : Function.Surjective (Algebra.trace K F)) :
    Function.Injective (uProj β) := by
  intro a a' h
  simp only [uProj, MonoidHom.comp_apply, QuotientGroup.mk'_apply] at h
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  set x := rootHom β a with hx
  set y := rootHom β a' with hy
  have hs : ((Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (c : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.one_apply]
  have h1 : SpExtras.mat r K (x⁻¹ * y) = (c : K) • 1 := by
    rw [SpExtras.mat_apply, ← hs, hc]
  have h2 : SpExtras.mat r K y = (c : K) • SpExtras.mat r K x := by
    have : SpExtras.mat r K y = SpExtras.mat r K x * SpExtras.mat r K (x⁻¹ * y) := by
      rw [← map_mul, mul_inv_cancel_left]
    rw [this, h1, Matrix.mul_smul, Matrix.mul_one]
  have hxm : SpExtras.mat r K x = fromBlocks 1 0 (gram β a.toAdd) 1 := rfl
  have hym : SpExtras.mat r K y = fromBlocks 1 0 (gram β a'.toAdd) 1 := rfl
  have e := congrFun (congrFun h2 (Sum.inl ⟨0, hr⟩)) (Sum.inl ⟨0, hr⟩)
  rw [hxm, hym] at e
  simp at e
  have hc1 : (c : K) = 1 := e.symm
  rw [hc1, one_smul, hxm, hym, fromBlocks_inj] at h2
  exact Multiplicative.toAdd.injective (gram_injective β htr h2.2.2.1).symm

end Proj

end Root

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
