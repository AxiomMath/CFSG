module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OILd
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OFLa

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIL

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {k : Type} [Field k]

theorem eq_of_conjAut_eq_of_pow [Finite k] {p : ℕ} [Fact p.Prime] [CharP k p]
    {X Y : GL (Fin 4) k} (hX : X ^ p = 1) (hY : Y ^ p = 1)
    (h : conjAut 4 k X = conjAut 4 k Y) : X = Y := by
  obtain ⟨c, hc⟩ :=
    (UnbalancedCatalog.conjAut_eq_conjAut_iff (by norm_num) X Y).mp h
  have hsc : GeneralLinearGroup.scalar (Fin 4) c ∈ Subgroup.center (GL (Fin 4) k) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have hcomm : Commute Y (GeneralLinearGroup.scalar (Fin 4) c) :=
    Subgroup.mem_center_iff.mp hsc Y
  have e2 : (Y * GeneralLinearGroup.scalar (Fin 4) c) ^ p = 1 := by rw [← hc, hX]
  rw [hcomm.mul_pow, hY, one_mul, ← map_pow] at e2
  have hc1 : c ^ p = 1 := by
    have := congrArg (fun Z : GL (Fin 4) k => (Z : Matrix (Fin 4) (Fin 4) k) 0 0) e2
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_one, Matrix.one_apply_eq] at this
    exact Units.val_eq_one.mp (by simpa using this)
  have hc2 : c = 1 := by
    have h3 : ((c : k) - 1) ^ p = 0 := by
      have e : (c : k) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hc1, Units.val_one]
      rw [sub_pow_char, e, one_pow, sub_self]
    exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.1 h3))
  rw [hc, hc2, map_one, mul_one]

theorem conj_map_eq_of_comm [Finite k] {p : ℕ} [Fact p.Prime] [CharP k p] (B h : GL (Fin 4) k)
    (σ : k ≃+* k) (hhp : h ^ p = 1)
    (hc : conjAut 4 k B * fieldAut 4 k σ * conjAut 4 k h =
      conjAut 4 k h * (conjAut 4 k B * fieldAut 4 k σ)) :
    B * GeneralLinearGroup.map (σ : k →+* k) h * B⁻¹ = h := by
  apply eq_of_conjAut_eq_of_pow (p := p)
  · rw [conj_pow, ← map_pow, hhp, map_one, mul_one, mul_inv_cancel]
  · exact hhp
  · rw [← (normalForm_conj_conjAut B h σ).1, hc, mul_inv_cancel_right]

theorem trace_rowOHom (δ : kˣ) (h2 : (2 : k) ≠ 0)
    (ψ : (Fin 4 → k) ≃ₗ[k] hermitianSubmodule (δ : k))
    (g : SpecialLinearGroup (Fin 2) (extension (δ : k))) (U : Matrix (Fin 4) (Fin 4) k)
    (hU : ∀ x, (hermitianCoordinates (δ : k) h2).symm
      (rowOAction δ g (hermitianCoordinates (δ : k) h2 x)) = U *ᵥ x) :
    (rowOHom δ ψ g : Matrix (Fin 4) (Fin 4) k).trace = U.trace := by
  set e : (Fin 4 → k) ≃ₗ[k] (Fin 4 → k) := (hermitianCoordinates (δ : k) h2).trans ψ.symm
    with he
  have h1 : Matrix.toLin' (rowOHom δ ψ g : Matrix (Fin 4) (Fin 4) k) =
      e.conj (Matrix.toLin' U) := by
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply, LinearEquiv.conj_apply_apply, Matrix.toLin'_apply]
    have hev : e.symm v = (hermitianCoordinates (δ : k) h2).symm (ψ v) := rfl
    rw [hev, ← hU, LinearEquiv.apply_symm_apply]
    change _ = ψ.symm ((hermitianCoordinates (δ : k) h2)
      ((hermitianCoordinates (δ : k) h2).symm (rowOAction δ g (ψ v))))
    rw [LinearEquiv.apply_symm_apply]
    exact linearConjGL_mulVec ψ _ v
  rw [← Matrix.trace_toLin'_eq, h1, LinearMap.trace_conj', Matrix.trace_toLin'_eq]

section GT

variable (δ : k)

theorem coe_gT (t : extension δ) :
    ((uE δ (t - 1) * lE δ 1 * uE δ (-1) : SpecialLinearGroup (Fin 2) (extension δ)) :
      Matrix (Fin 2) (Fin 2) (extension δ)) = !![t, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [uE, lE, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

@[expose] def mT (t : extension δ) : Matrix (Fin 4) (Fin 4) k :=
  !![t.re ^ 2 - δ * t.im ^ 2, 1, -2 * t.re, -2 * δ * t.im; 1, 0, 0, 0; t.re, 0, -1, 0;
    t.im, 0, 0, 1]

theorem mT_mulVec (t : extension δ) (x : Fin 4 → k) :
    mT δ t *ᵥ x = ![(t.re ^ 2 - δ * t.im ^ 2) * x 0 + x 1 - 2 * t.re * x 2 -
      2 * δ * t.im * x 3, x 0, t.re * x 0 - x 2, t.im * x 0 + x 3] := by
  funext i
  fin_cases i
  all_goals simp [mT, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  all_goals ring

theorem trace_mT (t : extension δ) : (mT δ t).trace = t.re ^ 2 - δ * t.im ^ 2 := by
  simp [mT, Matrix.trace, Fin.sum_univ_four]

end GT

theorem coord_gT (δ : kˣ) (h2 : (2 : k) ≠ 0) (t : extension (δ : k)) (x : Fin 4 → k) :
    (hermitianCoordinates (δ : k) h2).symm
        (rowOAction δ (uE (δ : k) (t - 1) * lE (δ : k) 1 * uE (δ : k) (-1))
          (hermitianCoordinates (δ : k) h2 x)) = mT (δ : k) t *ᵥ x := by
  rw [mT_mulVec, hermitianCoordinates_symm_apply, rowOAction_val, hermitianCoordinates_val,
    coe_gT]
  funext i
  fin_cases i
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im]
  all_goals ring

theorem trace_rowOHom_gT (δ : kˣ) (h2 : (2 : k) ≠ 0)
    (ψ : (Fin 4 → k) ≃ₗ[k] hermitianSubmodule (δ : k)) (t : extension (δ : k)) :
    (rowOHom δ ψ (uE (δ : k) (t - 1) * lE (δ : k) 1 * uE (δ : k) (-1)) :
      Matrix (Fin 4) (Fin 4) k).trace = t.re ^ 2 - (δ : k) * t.im ^ 2 := by
  rw [trace_rowOHom δ h2 ψ _ (mT (δ : k) t) (coord_gT δ h2 t), trace_mT]

theorem fieldAut_eq_one_of_comm [Fintype k] {p : ℕ} [Fact p.Prime] [CharP k p]
    (hq : Fintype.card k % 2 = 1) (δ : kˣ) (h2 : (2 : k) ≠ 0)
    (ψ : (Fin 4 → k) ≃ₗ[k] hermitianSubmodule (δ : k)) (B : GL (Fin 4) k) (σ : k ≃+* k)
    (hB : ∀ g : SpecialLinearGroup (Fin 2) (extension (δ : k)),
      conjAut 4 k B * fieldAut 4 k σ * conjAut 4 k (rowOHom δ ψ g) =
        conjAut 4 k (rowOHom δ ψ g) * (conjAut 4 k B * fieldAut 4 k σ)) :
    σ = 1 := by
  set T : SpecialLinearGroup (Fin 2) (extension (δ : k)) →* GL (Fin 4) k :=
    (MulAut.conj B).toMonoidHom.comp
      ((GeneralLinearGroup.map (σ : k →+* k)).comp (rowOHom δ ψ)) with hT
  have hTapp : ∀ g, T g = B * GeneralLinearGroup.map (σ : k →+* k) (rowOHom δ ψ g) * B⁻¹ :=
    fun g => rfl
  have hunip : ∀ g : SpecialLinearGroup (Fin 2) (extension (δ : k)), g ^ p = 1 →
      T g = rowOHom δ ψ g := fun g hg => by
    rw [hTapp]
    exact conj_map_eq_of_comm (p := p) B _ σ (by rw [← map_pow, hg, map_one]) (hB g)
  have hgT : ∀ t : extension (δ : k),
      T (uE (δ : k) (t - 1) * lE (δ : k) 1 * uE (δ : k) (-1)) =
        rowOHom δ ψ (uE (δ : k) (t - 1) * lE (δ : k) 1 * uE (δ : k) (-1)) := fun t => by
    rw [map_mul, map_mul, map_mul, map_mul, hunip _ (uE_pow_char _ _),
      hunip _ (lE_pow_char _ _), hunip _ (uE_pow_char _ _)]
  have htr : ∀ t : extension (δ : k), σ (t.re ^ 2 - (δ : k) * t.im ^ 2) =
      t.re ^ 2 - (δ : k) * t.im ^ 2 := fun t => by
    have h1 := congrArg (fun X : GL (Fin 4) k => (X : Matrix (Fin 4) (Fin 4) k).trace) (hgT t)
    have hmap : ∀ X : GL (Fin 4) k, ((GeneralLinearGroup.map (σ : k →+* k) X : GL (Fin 4) k) :
        Matrix (Fin 4) (Fin 4) k) = (X : Matrix (Fin 4) (Fin 4) k).map (σ : k →+* k) :=
      fun X => rfl
    rw [hTapp, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, Units.inv_mul, one_mul,
      hmap, ← AddMonoidHom.map_trace, trace_rowOHom_gT δ h2 ψ t] at h1
    exact h1
  refine RingEquiv.ext fun d => ?_
  obtain ⟨a, b, hab⟩ := OFL.exists_norm_eq hq δ.ne_zero d
  have h1 := htr ⟨a, b⟩
  change σ (a ^ 2 - (δ : k) * b ^ 2) = a ^ 2 - (δ : k) * b ^ 2 at h1
  rw [hab] at h1
  exact h1

end OIL

end CFSG.ComponentClassification.CatFactsL4U4
