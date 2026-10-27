module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OILc

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIL

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {k : Type} [Field k]

theorem eq_smul_one_of_comm_rowOHom (δ : kˣ) (h2 : (2 : k) ≠ 0)
    (ψ : (Fin 4 → k) ≃ₗ[k] hermitianSubmodule (δ : k)) (B : Matrix (Fin 4) (Fin 4) k)
    (hu1 : B * (rowOHom δ ψ (uE (δ : k) 1) : Matrix (Fin 4) (Fin 4) k) =
      (rowOHom δ ψ (uE (δ : k) 1) : Matrix (Fin 4) (Fin 4) k) * B)
    (huw : B * (rowOHom δ ψ (uE (δ : k) ⟨0, 1⟩) : Matrix (Fin 4) (Fin 4) k) =
      (rowOHom δ ψ (uE (δ : k) ⟨0, 1⟩) : Matrix (Fin 4) (Fin 4) k) * B)
    (hl1 : B * (rowOHom δ ψ (lE (δ : k) 1) : Matrix (Fin 4) (Fin 4) k) =
      (rowOHom δ ψ (lE (δ : k) 1) : Matrix (Fin 4) (Fin 4) k) * B) :
    ∃ c : k, B = c • (1 : Matrix (Fin 4) (Fin 4) k) := by
  classical
  set hc := hermitianCoordinates (δ : k) h2 with hhc
  set S : (Fin 4 → k) →ₗ[k] (Fin 4 → k) :=
    (hc.symm : hermitianSubmodule (δ : k) →ₗ[k] (Fin 4 → k)) ∘ₗ
      (ψ : (Fin 4 → k) →ₗ[k] hermitianSubmodule (δ : k)) ∘ₗ Matrix.toLin' B ∘ₗ
      (ψ.symm : hermitianSubmodule (δ : k) →ₗ[k] (Fin 4 → k)) ∘ₗ
      (hc : (Fin 4 → k) →ₗ[k] hermitianSubmodule (δ : k)) with hS
  have hSapp : ∀ y, S y = hc.symm (ψ (B *ᵥ ψ.symm (hc y))) := fun y => by
    simp [hS, Matrix.toLin'_apply]
  have hrow : ∀ (g : SpecialLinearGroup (Fin 2) (extension (δ : k))) (v : Fin 4 → k),
      (rowOHom δ ψ g : Matrix (Fin 4) (Fin 4) k) *ᵥ v = ψ.symm (rowOAction δ g (ψ v)) :=
    fun g v => linearConjGL_mulVec ψ _ v
  have key : ∀ (g : SpecialLinearGroup (Fin 2) (extension (δ : k))) (U : Matrix (Fin 4) (Fin 4) k),
      (∀ x, hc.symm (rowOAction δ g (hc x)) = U *ᵥ x) →
      B * (rowOHom δ ψ g : Matrix (Fin 4) (Fin 4) k) =
        (rowOHom δ ψ g : Matrix (Fin 4) (Fin 4) k) * B →
      LinearMap.toMatrix' S * U = U * LinearMap.toMatrix' S := by
    intro g U hU hBg
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, LinearMap.comp_apply, LinearMap.comp_apply,
      Matrix.toLin'_toMatrix', Matrix.toLin'_apply, Matrix.toLin'_apply, ← hU, hSapp, hSapp,
      LinearEquiv.apply_symm_apply, ← hU]
    congr 1
    set v := ψ.symm (hc x) with hv
    have hxv : hc x = ψ v := by rw [hv, LinearEquiv.apply_symm_apply]
    rw [hxv, ← hrow, Matrix.mulVec_mulVec, hBg, ← Matrix.mulVec_mulVec, hrow,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hM1 := key _ mU1 (fun x => by rw [coord_uE_one, mU1_mulVec]) hu1
  have hMw := key _ (mUw (δ : k)) (fun x => by rw [coord_uE_omega, mUw_mulVec]) huw
  have hMl := key _ mL1 (fun x => by rw [coord_lE_one, mL1_mulVec]) hl1
  have hM := schur_matrix h2 hM1 hMw hMl
  set c := LinearMap.toMatrix' S 0 0 with hc0
  have hSc : ∀ y, S y = c • y := fun y => by
    rw [← Matrix.toLin'_toMatrix' S, Matrix.toLin'_apply, hM, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  refine ⟨c, Matrix.toLin'.injective (LinearMap.ext fun v => ?_)⟩
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h1 := hSc (hc.symm (ψ v))
  rw [hSapp, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h1
  have h2' := congrArg (fun y => ψ.symm (hc y)) h1
  simp only [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply, map_smul] at h2'
  exact h2'

theorem uE_pow_char {p : ℕ} [CharP k p] (δ : k) (t : extension δ) : uE δ t ^ p = 1 := by
  have hp : (p : extension δ) = 0 := by
    rw [← map_natCast (algebraMap k (extension δ)) p, CharP.cast_eq_zero, map_zero]
  rw [uE_pow, hp, zero_mul, uE_zero]

theorem lE_pow_char {p : ℕ} [CharP k p] (δ : k) (t : extension δ) : lE δ t ^ p = 1 := by
  have hp : (p : extension δ) = 0 := by
    rw [← map_natCast (algebraMap k (extension δ)) p, CharP.cast_eq_zero, map_zero]
  rw [lE_pow, hp, zero_mul, lE_zero]

theorem comm_of_conjAut_comm [Finite k] {p : ℕ} [Fact p.Prime] [CharP k p] {B h : GL (Fin 4) k}
    (hhp : h ^ p = 1) (hBh : conjAut 4 k B * conjAut 4 k h = conjAut 4 k h * conjAut 4 k B) :
    B * h = h * B := by
  have h1 : conjAut 4 k (B * h * B⁻¹ * h⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hBh]
    group
  obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by norm_num) _).1 h1
  have hsc : GeneralLinearGroup.scalar (Fin 4) c ∈ Subgroup.center (GL (Fin 4) k) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have e1 : B * h * B⁻¹ = GeneralLinearGroup.scalar (Fin 4) c * h := by
    rw [hc]
    group
  have e2 : (B * h * B⁻¹) ^ p = 1 := by rw [conj_pow, hhp, mul_one, mul_inv_cancel]
  have hcomm : Commute (GeneralLinearGroup.scalar (Fin 4) c) h :=
    (Subgroup.mem_center_iff.mp hsc h).symm
  rw [e1, hcomm.mul_pow, hhp, mul_one, ← map_pow] at e2
  have hc1 : c ^ p = 1 := by
    have := congrArg (fun X : GL (Fin 4) k => (X : Matrix (Fin 4) (Fin 4) k) 0 0) e2
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_one, Matrix.one_apply_eq] at this
    exact Units.val_eq_one.mp (by simpa using this)
  have hc2 : c = 1 := by
    have h3 : ((c : k) - 1) ^ p = 0 := by
      have e : (c : k) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hc1, Units.val_one]
      rw [sub_pow_char, e, one_pow, sub_self]
    exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.1 h3))
  rw [hc2, map_one, one_mul] at e1
  calc B * h = B * h * B⁻¹ * B := by group
    _ = h * B := by rw [e1]

theorem conjAut_eq_one_of_comm [Finite k] {p : ℕ} [Fact p.Prime] [CharP k p] (δ : kˣ)
    (h2 : (2 : k) ≠ 0)
    (ψ : (Fin 4 → k) ≃ₗ[k] hermitianSubmodule (δ : k)) (B : GL (Fin 4) k)
    (hB : ∀ g : SpecialLinearGroup (Fin 2) (extension (δ : k)),
      conjAut 4 k B * conjAut 4 k (rowOHom δ ψ g) = conjAut 4 k (rowOHom δ ψ g) * conjAut 4 k B) :
    conjAut 4 k B = 1 := by
  have hcomm : ∀ g : SpecialLinearGroup (Fin 2) (extension (δ : k)), g ^ p = 1 →
      (B : Matrix (Fin 4) (Fin 4) k) * (rowOHom δ ψ g : Matrix (Fin 4) (Fin 4) k) =
        (rowOHom δ ψ g : Matrix (Fin 4) (Fin 4) k) * B := by
    intro g hg
    have := comm_of_conjAut_comm (B := B) (h := rowOHom δ ψ g)
      (by rw [← map_pow, hg, map_one]) (hB g)
    exact congrArg Units.val this
  obtain ⟨c, hc⟩ := eq_smul_one_of_comm_rowOHom δ h2 ψ (B : Matrix (Fin 4) (Fin 4) k)
    (hcomm _ (uE_pow_char _ _)) (hcomm _ (uE_pow_char _ _)) (hcomm _ (lE_pow_char _ _))
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 := (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
    rw [hc, zero_smul, Matrix.det_zero] at h1
    exact not_isUnit_zero h1
  apply (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by norm_num) _).2
  refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar, hc, Units.val_mk0, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]

end OIL

end CFSG.ComponentClassification.CatFactsL4U4
