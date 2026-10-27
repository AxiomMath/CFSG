module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsBridge
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {σ : K →+* K}

section Block

theorem map_eq_of_forall_mem (e : (ι → K) ≃ₗ[K] (ι → K)) {U : Submodule K (ι → K)}
    (h : ∀ u ∈ U, e u ∈ U) : U.map (e : (ι → K) →ₗ[K] (ι → K)) = U := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨u, hu, rfl⟩
    exact h u hu
  · exact LinearEquiv.finrank_map_eq e U

theorem symm_mem_of_forall_mem (e : (ι → K) ≃ₗ[K] (ι → K)) {U : Submodule K (ι → K)}
    (h : ∀ u ∈ U, e u ∈ U) {u : ι → K} (hu : u ∈ U) : e.symm u ∈ U := by
  rw [← map_eq_of_forall_mem e h] at hu
  obtain ⟨u', hu', rfl⟩ := hu
  simpa using hu'

@[expose] noncomputable def blkSub (β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K)
    (U W : Submodule K (ι → K)) : Subgroup (GL ι K) where
  carrier := {g | g ∈ isomGL β ∧ (∀ u ∈ U, glEquiv g u ∈ U) ∧ ∀ w ∈ W, glEquiv g w = w}
  one_mem' := ⟨(isomGL β).one_mem, fun u hu => by simpa using hu, fun w _ => by simp⟩
  mul_mem' {g h} hg hh := ⟨(isomGL β).mul_mem hg.1 hh.1, fun u hu => by
      rw [map_mul, LinearEquiv.mul_apply]
      exact hg.2.1 _ (hh.2.1 u hu), fun w hw => by
      rw [map_mul, LinearEquiv.mul_apply, hh.2.2 w hw, hg.2.2 w hw]⟩
  inv_mem' {g} hg := ⟨(isomGL β).inv_mem hg.1, fun u hu => by
      rw [map_inv]
      exact symm_mem_of_forall_mem (glEquiv g) hg.2.1 hu, fun w hw => by
      rw [map_inv]
      apply (glEquiv g).injective
      rw [← LinearEquiv.mul_apply, mul_inv_cancel, LinearEquiv.coe_one, id, hg.2.2 w hw]⟩

theorem mem_blkSub {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K} {U W : Submodule K (ι → K)}
    {g : GL ι K} : g ∈ blkSub β U W ↔
      g ∈ isomGL β ∧ (∀ u ∈ U, glEquiv g u ∈ U) ∧ ∀ w ∈ W, glEquiv g w = w :=
  Iff.rfl

@[expose] noncomputable def blkI (β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K)
    (U W : Submodule K (ι → K)) : Subgroup (GL ι K) :=
  ⁅blkSub β U W, blkSub β U W⁆

theorem blkI_le_blkSub (β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K) (U W : Submodule K (ι → K)) :
    blkI β U W ≤ blkSub β U W :=
  Subgroup.commutator_le_self _

theorem blkSub_le_isomGL (β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K) (U W : Submodule K (ι → K)) :
    blkSub β U W ≤ isomGL β :=
  fun _ hg => hg.1

theorem blkI_le_isomGL (β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K) (U W : Submodule K (ι → K)) :
    blkI β U W ≤ isomGL β :=
  (blkI_le_blkSub β U W).trans (blkSub_le_isomGL β U W)

end Block

section Restrict

@[expose] def isomU (β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K) (U : Submodule K (ι → K)) :
    Subgroup (U ≃ₗ[K] U) where
  carrier := {g | ∀ x y : U, β (g x : ι → K) (g y : ι → K) = β x y}
  one_mem' := fun _ _ => rfl
  mul_mem' {g h} hg hh x y := (hg _ _).trans (hh x y)
  inv_mem' {g} hg x y := by
    have h := hg (g.symm x) (g.symm y)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    exact h.symm

theorem mem_isomU {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K} {U : Submodule K (ι → K)}
    {g : U ≃ₗ[K] U} : g ∈ isomU β U ↔ ∀ x y : U, β (g x : ι → K) (g y : ι → K) = β x y :=
  Iff.rfl

variable (β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K) (U W : Submodule K (ι → K))

@[expose] noncomputable def resU : blkSub β U W →* (U ≃ₗ[K] U) where
  toFun g := (glEquiv (g : GL ι K)).ofSubmodules U U (map_eq_of_forall_mem _ g.2.2.1)
  map_one' := by
    ext u
    simp [LinearEquiv.ofSubmodules_apply]
  map_mul' g h := by
    ext u
    simp [LinearEquiv.ofSubmodules_apply]

theorem coe_resU_apply (g : blkSub β U W) (u : U) :
    ((resU β U W g u : U) : ι → K) = glEquiv (g : GL ι K) u :=
  rfl

theorem resU_mem_isomU (g : blkSub β U W) : resU β U W g ∈ isomU β U := fun x y => by
  rw [coe_resU_apply, coe_resU_apply]
  exact mem_isomGL.mp g.2.1 x y

variable {U W} (hUW : IsCompl U W)

@[expose] noncomputable def extU (g : U ≃ₗ[K] U) : (ι → K) ≃ₗ[K] (ι → K) :=
  (Submodule.prodEquivOfIsCompl U W hUW).symm ≪≫ₗ
    ((g.prodCongr (LinearEquiv.refl K W)) ≪≫ₗ Submodule.prodEquivOfIsCompl U W hUW)

theorem extU_apply_mem (g : U ≃ₗ[K] U) (u : U) : extU hUW g u = g u := by
  simp [extU, Submodule.prodEquivOfIsCompl_symm_apply_left]

theorem extU_apply_mem_right (g : U ≃ₗ[K] U) (w : W) : extU hUW g w = w := by
  simp [extU, Submodule.prodEquivOfIsCompl_symm_apply_right]

omit [DecidableEq ι] in
theorem linearEquiv_ext_of_isCompl (hUW : IsCompl U W) {e e' : (ι → K) ≃ₗ[K] (ι → K)}
    (hU : ∀ u ∈ U, e u = e' u) (hW : ∀ w ∈ W, e w = e' w) : e = e' := by
  ext v
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1
    (show v ∈ U ⊔ W by rw [hUW.sup_eq_top]; trivial)
  rw [map_add, map_add, hU u hu, hW w hw]

@[expose] noncomputable def extHom : (U ≃ₗ[K] U) →* ((ι → K) ≃ₗ[K] (ι → K)) where
  toFun := extU hUW
  map_one' := linearEquiv_ext_of_isCompl hUW
    (fun u hu => by rw [extU_apply_mem hUW 1 ⟨u, hu⟩]; rfl)
    (fun w hw => by rw [extU_apply_mem_right hUW 1 ⟨w, hw⟩]; rfl)
  map_mul' g h := linearEquiv_ext_of_isCompl hUW
    (fun u hu => by
      rw [LinearEquiv.mul_apply, extU_apply_mem hUW _ ⟨u, hu⟩, extU_apply_mem hUW h ⟨u, hu⟩,
        extU_apply_mem hUW g (h ⟨u, hu⟩)]
      rfl)
    (fun w hw => by
      rw [LinearEquiv.mul_apply, extU_apply_mem_right hUW _ ⟨w, hw⟩,
        extU_apply_mem_right hUW h ⟨w, hw⟩, extU_apply_mem_right hUW g ⟨w, hw⟩])

variable {β}
variable (horth : ∀ u ∈ U, ∀ w ∈ W, β u w = 0 ∧ β w u = 0)
include horth

theorem extU_mem_isomGL {g : U ≃ₗ[K] U} (hg : g ∈ isomU β U) :
    glEquiv.symm (extU hUW g) ∈ isomGL β := by
  rw [mem_isomGL]
  intro x y
  rw [← glEquiv_apply, ← glEquiv_apply, MulEquiv.apply_symm_apply]
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1
    (show x ∈ U ⊔ W by rw [hUW.sup_eq_top]; trivial)
  obtain ⟨u', hu', w', hw', rfl⟩ := Submodule.mem_sup.1
    (show y ∈ U ⊔ W by rw [hUW.sup_eq_top]; trivial)
  rw [(extU hUW g).map_add u w, (extU hUW g).map_add u' w', extU_apply_mem hUW g ⟨u, hu⟩,
    extU_apply_mem hUW g ⟨u', hu'⟩, extU_apply_mem_right hUW g ⟨w, hw⟩,
    extU_apply_mem_right hUW g ⟨w', hw'⟩]
  simp only [map_add, LinearMap.add_apply]
  rw [(horth _ (g ⟨u, hu⟩).2 w' hw').1, (horth _ (g ⟨u', hu'⟩).2 w hw).2,
    (horth u hu w' hw').1, (horth u' hu' w hw).2, hg ⟨u, hu⟩ ⟨u', hu'⟩]

theorem extU_mem_blkSub {g : U ≃ₗ[K] U} (hg : g ∈ isomU β U) :
    glEquiv.symm (extU hUW g) ∈ blkSub β U W := by
  refine ⟨extU_mem_isomGL hUW horth hg, fun u hu => ?_, fun w hw => ?_⟩
  · rw [MulEquiv.apply_symm_apply, extU_apply_mem hUW g ⟨u, hu⟩]
    exact (g ⟨u, hu⟩).2
  · rw [MulEquiv.apply_symm_apply, extU_apply_mem_right hUW g ⟨w, hw⟩]

@[expose] noncomputable def blkSubEquiv : blkSub β U W ≃* isomU β U where
  toFun g := ⟨resU β U W g, resU_mem_isomU β U W g⟩
  invFun g := ⟨glEquiv.symm (extU hUW g.1), extU_mem_blkSub hUW horth g.2⟩
  left_inv g := by
    apply Subtype.ext
    apply glEquiv.injective
    rw [MulEquiv.apply_symm_apply]
    refine linearEquiv_ext_of_isCompl hUW (fun u hu => ?_) fun w hw => ?_
    · rw [extU_apply_mem hUW _ ⟨u, hu⟩, coe_resU_apply]
    · rw [extU_apply_mem_right hUW _ ⟨w, hw⟩, g.2.2.2 w hw]
  right_inv g := by
    apply Subtype.ext
    ext u
    rw [coe_resU_apply, MulEquiv.apply_symm_apply, extU_apply_mem hUW]
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul (resU β U W) g h

theorem coe_blkSubEquiv_apply (g : blkSub β U W) (u : U) :
    (((blkSubEquiv hUW horth g : isomU β U) : U ≃ₗ[K] U) u : ι → K) =
      glEquiv (g : GL ι K) u :=
  rfl

@[expose] noncomputable def blkIEquiv :
    blkI β U W ≃* (⁅isomU β U, isomU β U⁆ : Subgroup (U ≃ₗ[K] U)) := by
  have h1 : blkI β U W = (commutator (blkSub β U W)).map (blkSub β U W).subtype := by
    rw [blkI, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have h2 : (⁅isomU β U, isomU β U⁆ : Subgroup (U ≃ₗ[K] U)) =
      (commutator (isomU β U)).map (isomU β U).subtype := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have h3 : (commutator (blkSub β U W)).map (blkSubEquiv hUW horth).toMonoidHom =
      commutator (isomU β U) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 (blkSubEquiv hUW horth).surjective]
  exact (MulEquiv.subgroupCongr h1).trans
    ((Subgroup.equivMapOfInjective _ _ (blkSub β U W).subtype_injective).symm.trans
      ((((blkSubEquiv hUW horth).subgroupMap (commutator (blkSub β U W))).trans
        (MulEquiv.subgroupCongr h3)).trans
        ((Subgroup.equivMapOfInjective _ _ (isomU β U).subtype_injective).trans
          (MulEquiv.subgroupCongr h2.symm))))

end Restrict

section Models

theorem det_eq_one_of_mem_blkI {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K}
    {U W : Submodule K (ι → K)} {g : GL ι K} (hg : g ∈ blkI β U W) :
    (g : Matrix ι ι K).det = 1 := by
  have hle : blkI β U W ≤ (Matrix.GeneralLinearGroup.det : GL ι K →* Kˣ).ker := by
    rw [blkI, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have h := congrArg Units.val (MonoidHom.mem_ker.1 (hle hg))
  simpa [Matrix.GeneralLinearGroup.val_det_apply] using h

theorem blkI_le_statedSL {n : ℕ} (β : (Fin n → K) →ₗ[K] (Fin n → K) →ₛₗ[σ] K)
    (U W : Submodule K (Fin n → K)) : blkI β U W ≤ CFSG.Open.StatedSL n K := fun _ hg =>
  Subgroup.subset_closure (det_eq_one_of_mem_blkI hg)

theorem transpose_mul_map_of_mem_isomGL_unitForm {g : GL ι K} (hg : g ∈ isomGL (unitForm σ)) :
    (g : Matrix ι ι K)ᵀ * (g : Matrix ι ι K).map σ = 1 := by
  ext i j
  have h := mem_isomGL.mp hg (Pi.single i 1) (Pi.single j 1)
  have hσ : (σ ∘ Pi.single j (1 : K)) = Pi.single j 1 := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp
    · simp [Pi.single_apply, hk]
  rw [unitForm_apply, unitForm_apply, hσ, Matrix.mulVec_single_one, Matrix.mulVec_single_one,
    single_dotProduct, one_mul] at h
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [dotProduct, Function.comp_apply, Matrix.col_apply, Matrix.transpose_apply,
    Matrix.map_apply] at h ⊢
  rw [h]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Pi.single_apply, hij, Ne.symm hij]

theorem map_transpose_mul_of_mem_isomGL_unitForm {g : GL ι K} (hg : g ∈ isomGL (unitForm σ)) :
    ((g : Matrix ι ι K).map σ)ᵀ * (g : Matrix ι ι K) = 1 := by
  have h := congrArg Matrix.transpose (transpose_mul_map_of_mem_isomGL_unitForm hg)
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h

theorem blkI_le_gramSU {p f : ℕ} (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K)
    (U W : Submodule K (ι → K)) :
    blkI (unitForm h.bar) U W ≤ CFSG.ClassicalGroups.UnitaryFlag.gramSU h 1 := fun g hg => by
  refine CFSG.ClassicalGroups.UnitaryFlag.mem_gramSU.2 ⟨?_, det_eq_one_of_mem_blkI hg⟩
  rw [Matrix.mul_one]
  exact map_transpose_mul_of_mem_isomGL_unitForm (blkI_le_isomGL _ U W hg)

theorem transpose_mul_mul_of_mem_isomGL_toBilin' {J : Matrix ι ι K} {g : GL ι K}
    (hg : g ∈ isomGL (Matrix.toBilin' J)) :
    (g : Matrix ι ι K)ᵀ * J * (g : Matrix ι ι K) = J := by
  ext i j
  have h := mem_isomGL.mp hg (Pi.single i 1) (Pi.single j 1)
  rw [← Matrix.toBilin'_single ((g : Matrix ι ι K)ᵀ * J * (g : Matrix ι ι K)),
    ← Matrix.toBilin'_comp, ← Matrix.toBilin'_single J, LinearMap.BilinForm.comp_apply,
    Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact h

theorem blkI_le_statedSp {r : ℕ}
    (U W : Submodule K (Fin r ⊕ Fin r → K)) :
    blkI (Matrix.toBilin' (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) U W ≤ CFSG.Open.StatedSp r K := fun g hg =>
  Subgroup.subset_closure (transpose_mul_mul_of_mem_isomGL_toBilin' (blkI_le_isomGL _ U W hg))

theorem quad_mulVec_of_mem_isomGL_polar {d : ℕ} (h2 : (2 : K) ≠ 0)
    {Q : QuadraticForm K (Fin d → K)} {g : GL (Fin d) K}
    (hg : g ∈ isomGL (QuadraticMap.polarBilin Q)) (v : Fin d → K) :
    Q ((g : Matrix (Fin d) (Fin d) K) *ᵥ v) = Q v := by
  have h := mem_isomGL.mp hg v v
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self] at h
  have h' : (2 : K) * Q ((g : Matrix (Fin d) (Fin d) K) *ᵥ v) = 2 * Q v := by
    simpa [two_mul] using h
  exact mul_left_cancel₀ h2 h'

theorem blkI_le_matrixDerived {d : ℕ} (h2 : (2 : K) ≠ 0) (Q : QuadraticForm K (Fin d → K))
    (U W : Submodule K (Fin d → K)) :
    blkI (QuadraticMap.polarBilin Q) U W ≤
      CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixDerived Q := by
  have hle : blkSub (QuadraticMap.polarBilin Q) U W ≤
      CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixIsometries Q :=
    fun g hg => by
      rw [CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.mem_matrixIsometries_iff]
      intro v
      exact quad_mulVec_of_mem_isomGL_polar h2 hg.1 v
  exact Subgroup.commutator_mono hle hle

end Models

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls

end
