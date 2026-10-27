module

public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeDefs
public import CFSG.HardMathSupport.Cooperstein.StructureLie.BotCaseKeyForm
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeOrthCentCoord

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Curtis.Coordinator.PLType

namespace OrthCent

open CFSG.ComponentClassification.OutcomeLocal CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Cooperstein.StructureLie (orthGL eq_polar_of_tv_mem_orthGL)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog
open scoped commutatorElement
open Matrix

theorem mul_mem_of_relIndex_two {G : Type*} [Group G] {Ω O : Subgroup G}
    (h : Ω.relIndex O = 2) {x y : G} (hx : x ∈ O) (hy : y ∈ O) (hxΩ : x ∉ Ω) (hyΩ : y ∉ Ω) :
    x * y ∈ Ω := by
  have h2 : (Ω.subgroupOf O).index = 2 := h
  have := (Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)).mpr
    (by simp only [Subgroup.mem_subgroupOf]; exact iff_of_false hxΩ hyΩ)
  exact this

section Reflection

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem exists_reflection_of_transvection (Q : QuadraticForm (ZMod 2) W)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {t : LinearMap.GeneralLinearGroup (ZMod 2) W}
    (ht : t ∈ orthGL Q) (htv : IsF2Transvection t) :
    ∃ w : W, Q w = 1 ∧ ∀ x, (t : W →ₗ[ZMod 2] W) x = x + QuadraticMap.polar Q w x • w := by
  obtain ⟨φ, a, h, hφ, ha, rfl⟩ := (isF2Transvection_iff t).mp htv
  obtain ⟨hQa, hpol⟩ := eq_polar_of_tv_mem_orthGL Q (fun u hu => hQ.1 u hu) h hφ ha ht
  refine ⟨a, hQa, fun x => ?_⟩
  rw [tv_apply, hpol]

end Reflection

section Coordinates

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] {n : ℕ}

def conjAutC (e : W ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :
    (W ≃ₗ[ZMod 2] W) ≃* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) where
  toFun f := e.symm.trans (f.trans e)
  invFun f := e.trans (f.trans e.symm)
  left_inv f := LinearEquiv.ext fun v => by simp
  right_inv f := LinearEquiv.ext fun v => by simp
  map_mul' f g := LinearEquiv.ext fun v => by simp [LinearEquiv.mul_apply]

def theta (e : W ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :
    LinearMap.GeneralLinearGroup (ZMod 2) W ≃* GL (Fin n) (ZMod 2) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).trans
    ((conjAutC e).trans ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
      (Fin n → ZMod 2)).symm.trans Matrix.GeneralLinearGroup.toLin.symm))

theorem theta_mulVec (e : W ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (g : LinearMap.GeneralLinearGroup (ZMod 2) W) (x : W) :
    ((theta e g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ e x =
      e ((g : W →ₗ[ZMod 2] W) x) := by
  rw [← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.coe_toLin, theta,
    MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  change e ((g : W →ₗ[ZMod 2] W) (e.symm (e x))) = _
  rw [e.symm_apply_apply]

theorem gl_ext' {g h : GL (Fin n) (ZMod 2)}
    (H : ∀ x, (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x =
      (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) :
    g = h :=
  Units.ext (Matrix.toLin'.injective (LinearMap.ext fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, H]))

variable (e : W ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (Q : QuadraticForm (ZMod 2) W)

def coordForm : QuadraticForm (ZMod 2) (Fin n → ZMod 2) :=
  Q.comp (e.symm : (Fin n → ZMod 2) →ₗ[ZMod 2] W)

theorem coordForm_apply (x : W) : coordForm e Q (e x) = Q x := by
  simp [coordForm]

theorem polar_coordForm (a b : W) :
    QuadraticMap.polar (coordForm e Q) (e a) (e b) = QuadraticMap.polar Q a b := by
  simp only [QuadraticMap.polar, ← map_add, coordForm_apply]

theorem mem_orthGL_iff (g : LinearMap.GeneralLinearGroup (ZMod 2) W) :
    g ∈ orthGL Q ↔ theta e g ∈ matrixIsometries (coordForm e Q) := by
  rw [mem_matrixIsometries_iff]
  have hg : g ∈ orthGL Q ↔ ∀ x, Q ((g : W →ₗ[ZMod 2] W) x) = Q x := by
    unfold orthGL
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    rfl
  rw [hg]
  constructor
  · intro h v
    obtain ⟨x, rfl⟩ := e.surjective v
    rw [matrixLinearEquiv_apply, theta_mulVec, coordForm_apply, coordForm_apply, h]
  · intro h x
    have := h (e x)
    rwa [matrixLinearEquiv_apply, theta_mulVec, coordForm_apply, coordForm_apply] at this

theorem map_orthGL_theta :
    (orthGL Q).map (theta e).toMonoidHom = matrixIsometries (coordForm e Q) := by
  ext A
  rw [Subgroup.mem_map_equiv]
  exact (mem_orthGL_iff e Q _).trans (by simp)

theorem map_derived_theta :
    (⁅orthGL Q, orthGL Q⁆).map (theta e).toMonoidHom = matrixDerived (coordForm e Q) := by
  rw [Subgroup.map_commutator, map_orthGL_theta]
  rfl

theorem mem_derived_iff (g : LinearMap.GeneralLinearGroup (ZMod 2) W) :
    g ∈ ⁅orthGL Q, orthGL Q⁆ ↔ theta e g ∈ matrixDerived (coordForm e Q) := by
  rw [← map_derived_theta e Q]
  constructor
  · intro h
    exact ⟨g, h, rfl⟩
  · rintro ⟨g', hg', hgg⟩
    have := (theta e).injective hgg
    rwa [← this]

theorem theta_reflection [CharP (ZMod 2) 2] {w : W} (hw : Q w = 1)
    {t : LinearMap.GeneralLinearGroup (ZMod 2) W}
    (ht : ∀ x, (t : W →ₗ[ZMod 2] W) x = x + QuadraticMap.polar Q w x • w) :
    theta e t = symmetryGL (coordForm e Q) (e w) := by
  have hw' : coordForm e Q (e w) = 1 := by rw [coordForm_apply, hw]
  apply gl_ext'
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [theta_mulVec, symmetryGL_mulVec_of_charTwo hw', polar_coordForm, ht, map_add, map_smul]

theorem map_centralizer_theta (t : LinearMap.GeneralLinearGroup (ZMod 2) W) :
    (Subgroup.centralizer {t}).map (theta e).toMonoidHom =
      Subgroup.centralizer {theta e t} := by
  ext A
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg (theta e) h
    simpa using this
  · intro h
    apply (theta e).injective
    simpa using h

theorem polarBilin_nondegenerate (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    (QuadraticMap.polarBilin (coordForm e Q)).Nondegenerate := by
  have key : ∀ u : Fin n → ZMod 2,
      (∀ y, QuadraticMap.polar (coordForm e Q) u y = 0) → u = 0 := by
    intro u hu
    obtain ⟨a, rfl⟩ := e.surjective u
    have : a = 0 := hQ.1 a fun x => by
      rw [QuadraticMap.polarBilin_apply_apply, ← polar_coordForm e Q]
      exact hu _
    rw [this, map_zero]
  constructor
  · intro u hu
    exact key u fun y => hu y
  · intro u hu
    refine key u fun y => ?_
    rw [QuadraticMap.polar_comm]
    exact hu y

theorem nonempty_equiv_of_coordinates {k : ℕ} (e : W ≃ₗ[ZMod 2] (Fin (2 * k) → ZMod 2))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hidx : (⁅orthGL Q, orthGL Q⁆).relIndex (orthGL Q) = 2)
    {t : LinearMap.GeneralLinearGroup (ZMod 2) W} (ht : t ∈ orthGL Q)
    (htv : IsF2Transvection t) (htn : t ∉ ⁅orthGL Q, orthGL Q⁆) :
    Nonempty (↥(⁅orthGL Q, orthGL Q⁆ ⊓ Subgroup.centralizer {t}) ≃*
      ↥(CFSG.Open.StatedSp (k - 1) (ZMod 2))) := by
  obtain ⟨w, hw, htw⟩ := exists_reflection_of_transvection Q hQ ht htv
  have hθt := theta_reflection e Q hw htw
  have hw' : coordForm e Q (e w) = 1 := by rw [coordForm_apply, hw]
  have hmain := OrthCoord.coord_centralizer_equiv (K := ZMod 2) (coordForm e Q)
    (polarBilin_nondegenerate e Q hQ) (e w) hw'
    (by
      intro x y hx hy hxn hyn
      have hx' : (theta e).symm x ∈ orthGL Q := by
        rw [mem_orthGL_iff e Q, MulEquiv.apply_symm_apply]; exact hx
      have hy' : (theta e).symm y ∈ orthGL Q := by
        rw [mem_orthGL_iff e Q, MulEquiv.apply_symm_apply]; exact hy
      have hxn' : (theta e).symm x ∉ ⁅orthGL Q, orthGL Q⁆ := by
        rw [mem_derived_iff e Q, MulEquiv.apply_symm_apply]; exact hxn
      have hyn' : (theta e).symm y ∉ ⁅orthGL Q, orthGL Q⁆ := by
        rw [mem_derived_iff e Q, MulEquiv.apply_symm_apply]; exact hyn
      have := mul_mem_of_relIndex_two hidx hx' hy' hxn' hyn'
      rw [mem_derived_iff e Q, map_mul, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply] at this
      exact this)
    (by rw [← hθt, ← mem_derived_iff e Q]; exact htn)
  obtain ⟨f⟩ := hmain
  have hsub : (⁅orthGL Q, orthGL Q⁆ ⊓ Subgroup.centralizer {t}).map (theta e).toMonoidHom =
      matrixDerived (coordForm e Q) ⊓ symmetryCentralizer (coordForm e Q) (e w) := by
    rw [Subgroup.map_inf _ _ _ (theta e).injective, map_derived_theta, map_centralizer_theta,
      hθt]
    ext A
    simp only [Subgroup.mem_inf, symmetryCentralizer]
    exact ⟨fun h => ⟨h.1, matrixDerived_le_isometries _ h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  exact ⟨((Subgroup.equivMapOfInjective _ (theta e).toMonoidHom (theta e).injective).trans
    (MulEquiv.subgroupCongr hsub)).trans f⟩

end Coordinates

theorem polarBilin_isAlt {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (Q : QuadraticForm (ZMod 2) W) : LinearMap.BilinForm.IsAlt (QuadraticMap.polarBilin Q) := by
  intro x
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul]
  exact CharTwo.add_self_eq_zero _

theorem orthTransvectionCent_holds : OrthTransvectionCent := by
  intro W _ _ _ Q hQ hidx t ht htv htn
  obtain ⟨k', hk'⟩ := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.even_finrank _
    (polarBilin_isAlt Q) hQ
  obtain ⟨k, hk⟩ : ∃ k, Module.finrank (ZMod 2) W = 2 * k := ⟨k', by omega⟩
  refine ⟨k, hk, ?_⟩
  let e : W ≃ₗ[ZMod 2] (Fin (2 * k) → ZMod 2) :=
    LinearEquiv.ofFinrankEq W (Fin (2 * k) → ZMod 2) (by simp [hk])
  exact nonempty_equiv_of_coordinates Q e hQ hidx ht htv htn

end OrthCent

end CFSG.HardMathSupport.Curtis.Coordinator.PLType
