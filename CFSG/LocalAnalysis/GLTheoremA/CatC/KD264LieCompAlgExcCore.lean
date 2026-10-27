module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.RationalTypeAModel
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenRank
import CFSG.RankThree.Classical2.SLnConjLemmas
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgLinear
public import CFSG.LieType.SeitzGeneration.SeitzStatus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false

section ConjSL

variable {L : Type} [Field L] {ν : ℕ}

theorem exists_scalar_of_commute_conjSLn_kd264alg (C : GL (Fin ν) L)
    (h : ∀ A : SL(ν, L), conjSLn C A = A) :
    ∃ c : L, (C : Matrix (Fin ν) (Fin ν) L) = Matrix.scalar (Fin ν) c := by
  classical
  have hc : ∀ t : Matrix.TransvectionStruct (Fin ν) L,
      Commute t.toMatrix (C : Matrix (Fin ν) (Fin ν) L) := by
    intro t
    have hdet : (t.toMatrix).det = 1 := Matrix.TransvectionStruct.det t
    have h1 : (C : Matrix (Fin ν) (Fin ν) L) * t.toMatrix *
        ((C⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) = t.toMatrix :=
      congrArg (fun X : SL(ν, L) => (X : Matrix (Fin ν) (Fin ν) L)) (h ⟨t.toMatrix, hdet⟩)
    have h2 : (C : Matrix (Fin ν) (Fin ν) L) * t.toMatrix = t.toMatrix * C := by
      calc (C : Matrix (Fin ν) (Fin ν) L) * t.toMatrix =
            (C : Matrix (Fin ν) (Fin ν) L) * t.toMatrix *
              (((C⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) * C) := by
            rw [Units.inv_mul, Matrix.mul_one]
        _ = ((C : Matrix (Fin ν) (Fin ν) L) * t.toMatrix *
              ((C⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)) * C := by
            simp only [Matrix.mul_assoc]
        _ = t.toMatrix * C := by rw [h1]
    exact h2.symm
  obtain ⟨c, hc'⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct hc
  exact ⟨c, hc'.symm⟩

end ConjSL

section Transport

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms

private theorem centerQuotientHom_mem_innAutDerived_of_surjective_kd264alg {C R : Type*}
    [Group C] [Group R] (hC : commutator C = ⊤) (θ : C →* R) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center C) {φ : MulAut C} {α : MulAut R}
    (hφα : ∀ c, θ (φ c) = α (θ c)) (hφ : φ ∈ innAutDerived C) :
    centerQuotientHom R α ∈ innAutDerived (R ⧸ Subgroup.center R) := by
  haveI : Group.IsPerfect C := Group.isPerfect_def.2 hC
  exact (CFSG.ComponentClassification.PerfectCentralQuotient.centerQuotientHom_mem_innAutDerived_iff_of_surjective
    θ hθ hker (fun c => (hφα c).symm)).2
    (CFSG.ComponentClassification.PerfectCentralQuotient.centerQuotientHom_mem_innAutDerived hφ)

end Transport

section UnitaryAut

open CFSG.ComponentClassification.OuterAutomorphisms
open Matrix

variable {L : Type} [Field L] {ν : ℕ}

private noncomputable def conjSLnAut_kd264alg (M : GL (Fin ν) L) : MulAut SL(ν, L) where
  toFun := conjSLn M
  invFun := conjSLn M⁻¹
  left_inv A := by rw [← conjSLn_mul, inv_mul_cancel, conjSLn_one]
  right_inv A := by rw [← conjSLn_mul, mul_inv_cancel, conjSLn_one]
  map_mul' := map_mul _

private noncomputable def slMapAut_kd264alg (σ : L ≃+* L) : MulAut SL(ν, L) where
  toFun := Matrix.SpecialLinearGroup.map σ.toRingHom
  invFun := Matrix.SpecialLinearGroup.map σ.symm.toRingHom
  left_inv A := by
    apply Subtype.ext
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  right_inv A := by
    apply Subtype.ext
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  map_mul' := map_mul _

private noncomputable abbrev unitaryFix_kd264alg (σ : L ≃+* L) : Subgroup SL(ν, L) :=
  CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σ)

private theorem mem_unitaryFix_iff_kd264alg (σ : L ≃+* L) (X : SL(ν, L)) :
    X ∈ unitaryFix_kd264alg σ ↔
      ((X : Matrix (Fin ν) (Fin ν) L).map σ)ᵀ * (X : Matrix (Fin ν) (Fin ν) L) = 1 := by
  rw [unitaryFix_kd264alg, CFSG.RankThree.Classical2.mem_fixSubgroup, stdUnitaryEquiv_apply]
  have hdet : IsUnit ((X : Matrix (Fin ν) (Fin ν) L).map σ).det := by
    have h0 : ((X : Matrix (Fin ν) (Fin ν) L).map σ).det = σ (X : Matrix (Fin ν) (Fin ν) L).det :=
      (RingHom.map_det σ.toRingHom _).symm
    rw [h0, X.2, map_one]
    exact isUnit_one
  constructor
  · intro h
    have h1 : (((X : Matrix (Fin ν) (Fin ν) L).map σ)⁻¹)ᵀ = (X : Matrix (Fin ν) (Fin ν) L) := by
      have h2 := congrArg (fun Y : SL(ν, L) => (Y : Matrix (Fin ν) (Fin ν) L)) h
      simp only [coe_stdUnitary] at h2
      exact h2
    calc ((X : Matrix (Fin ν) (Fin ν) L).map σ)ᵀ * (X : Matrix (Fin ν) (Fin ν) L) =
        ((X : Matrix (Fin ν) (Fin ν) L).map σ)ᵀ *
          (((X : Matrix (Fin ν) (Fin ν) L).map σ)⁻¹)ᵀ := by rw [h1]
      _ = 1 := by
        rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.transpose_one]
  · intro h
    apply Subtype.ext
    rw [coe_stdUnitary]
    have : ((X : Matrix (Fin ν) (Fin ν) L).map σ)⁻¹ = (X : Matrix (Fin ν) (Fin ν) L)ᵀ := by
      refine Matrix.inv_eq_left_inv ?_
      rw [← Matrix.transpose_transpose ((X : Matrix (Fin ν) (Fin ν) L).map σ),
        ← Matrix.transpose_mul, h, Matrix.transpose_one]
    change (((X : Matrix (Fin ν) (Fin ν) L).map σ)⁻¹)ᵀ = _
    rw [this, Matrix.transpose_transpose]

private noncomputable def unitaryGL_kd264alg (σ : L ≃+* L) : Subgroup (GL (Fin ν) L) where
  carrier := {g | ((g : Matrix (Fin ν) (Fin ν) L).map σ)ᵀ * g = 1}
  one_mem' := by
    change ((1 : Matrix (Fin ν) (Fin ν) L).map σ)ᵀ * 1 = 1
    rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one, Matrix.mul_one]
  mul_mem' := by
    intro g h hg hh
    change ((((g * h : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)).map σ)ᵀ * (g * h : GL _ L) = 1
    change ((g : Matrix (Fin ν) (Fin ν) L).map σ)ᵀ * g = 1 at hg
    change ((h : Matrix (Fin ν) (Fin ν) L).map σ)ᵀ * h = 1 at hh
    rw [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (((g : Matrix (Fin ν) (Fin ν) L).map σ)ᵀ), hg, Matrix.one_mul, hh]
  inv_mem' := by
    intro g hg
    change ((g : Matrix (Fin ν) (Fin ν) L).map σ)ᵀ * g = 1 at hg
    change ((((g⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)).map σ)ᵀ * (g⁻¹ : GL _ L) = 1
    have h1 : ((g : Matrix (Fin ν) (Fin ν) L).map σ)ᵀ = ((g⁻¹ : GL (Fin ν) L) : Matrix _ _ L) := by
      calc ((g : Matrix (Fin ν) (Fin ν) L).map σ)ᵀ =
          ((g : Matrix (Fin ν) (Fin ν) L).map σ)ᵀ * ((g * g⁻¹ : GL (Fin ν) L) : Matrix _ _ L) := by
            rw [mul_inv_cancel, Units.val_one, Matrix.mul_one]
        _ = _ := by rw [Units.val_mul, ← Matrix.mul_assoc, hg, Matrix.one_mul]
    have h2 : ((((g⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)).map σ)ᵀ *
        ((g : Matrix (Fin ν) (Fin ν) L).map σ)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
    rw [h1] at h2
    exact h2

private theorem mem_unitaryFix_iff_toGL_kd264alg (σ : L ≃+* L) (X : SL(ν, L)) :
    X ∈ unitaryFix_kd264alg σ ↔ Matrix.SpecialLinearGroup.toGL X ∈ unitaryGL_kd264alg σ :=
  mem_unitaryFix_iff_kd264alg σ X

private theorem conjSLn_mem_unitaryFix_kd264alg {σ : L ≃+* L} {M : GL (Fin ν) L}
    (hM : M ∈ unitaryGL_kd264alg σ) {X : SL(ν, L)} (hX : X ∈ unitaryFix_kd264alg σ) :
    conjSLn M X ∈ unitaryFix_kd264alg σ := by
  rw [mem_unitaryFix_iff_toGL_kd264alg] at hX ⊢
  have h : Matrix.SpecialLinearGroup.toGL (conjSLn M X) =
      M * Matrix.SpecialLinearGroup.toGL X * M⁻¹ := by
    apply Units.ext
    change ((conjSLn M X : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) = _
    rw [coe_conjSLn, Units.val_mul, Units.val_mul]
    rfl
  rw [h]
  exact mul_mem (mul_mem hM hX) (inv_mem hM)

private theorem map_conjSLnAut_unitaryFix_kd264alg {σ : L ≃+* L} {M : GL (Fin ν) L}
    (hM : M ∈ unitaryGL_kd264alg σ) :
    (unitaryFix_kd264alg σ).map (conjSLnAut_kd264alg M).toMonoidHom = unitaryFix_kd264alg σ := by
  refine le_antisymm ?_ fun X hX => ?_
  · rintro _ ⟨X, hX, rfl⟩
    exact conjSLn_mem_unitaryFix_kd264alg hM hX
  · refine ⟨conjSLn M⁻¹ X, conjSLn_mem_unitaryFix_kd264alg (inv_mem hM) hX, ?_⟩
    change conjSLn M (conjSLn M⁻¹ X) = X
    rw [← conjSLn_mul, mul_inv_cancel, conjSLn_one]

private theorem slMap_mem_unitaryFix_kd264alg {σ τ' : L ≃+* L} (hc : ∀ c, σ (τ' c) = τ' (σ c))
    {X : SL(ν, L)} (hX : X ∈ unitaryFix_kd264alg σ) :
    Matrix.SpecialLinearGroup.map τ'.toRingHom X ∈ unitaryFix_kd264alg σ := by
  rw [mem_unitaryFix_iff_kd264alg] at hX ⊢
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  have e1 : (((X : Matrix (Fin ν) (Fin ν) L).map τ'.toRingHom).map σ)ᵀ *
      (X : Matrix (Fin ν) (Fin ν) L).map τ'.toRingHom =
      (((X : Matrix (Fin ν) (Fin ν) L).map σ)ᵀ * X).map τ'.toRingHom := by
    rw [Matrix.map_mul, Matrix.transpose_map]
    congr 2
    ext i j
    simp [hc]
  rw [e1, hX, Matrix.map_one _ (map_zero _) (map_one _)]

private theorem map_slMapAut_unitaryFix_kd264alg {σ τ' : L ≃+* L}
    (hc : ∀ c, σ (τ' c) = τ' (σ c)) :
    (unitaryFix_kd264alg (ν := ν) σ).map (slMapAut_kd264alg τ').toMonoidHom =
      unitaryFix_kd264alg σ := by
  have hc' : ∀ c, σ (τ'.symm c) = τ'.symm (σ c) := by
    intro c
    apply τ'.injective
    rw [← hc, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  refine le_antisymm ?_ fun X hX => ?_
  · rintro _ ⟨X, hX, rfl⟩
    exact slMap_mem_unitaryFix_kd264alg hc hX
  · refine ⟨Matrix.SpecialLinearGroup.map τ'.symm.toRingHom X,
      slMap_mem_unitaryFix_kd264alg hc' hX, ?_⟩
    change Matrix.SpecialLinearGroup.map τ'.toRingHom
      (Matrix.SpecialLinearGroup.map τ'.symm.toRingHom X) = X
    apply Subtype.ext
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem mem_innAutDerived_of_unitary_conj_kd264alg [CharP L 2] (hν : 0 < ν) (σ σ₂ : L ≃+* L)
    (hσ₂ : ∀ c, σ₂ c = c ^ 2) (hσσ₂ : ∀ c, σ (σ₂ c) = σ₂ (σ c)) (G : GL (Fin ν) L)
    (hG : ((G : Matrix (Fin ν) (Fin ν) L).map σ)ᵀ * G = 1)
    (φ : MulAut ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σ)))
    (hφ : ∀ X, ((φ X : SL(ν, L))) = conjSLn G X) :
    φ ∈ innAutDerived ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σ)) := by
  classical
  have hGu : G ∈ unitaryGL_kd264alg σ := hG
  set d : Lˣ := Matrix.GeneralLinearGroup.det G with hd
  have hσd : σ (d : L) * d = 1 := by
    have h1 := congrArg Matrix.det hG
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
    have h0 : ((G : Matrix (Fin ν) (Fin ν) L).map σ).det = σ (G : Matrix (Fin ν) (Fin ν) L).det :=
      (RingHom.map_det σ.toRingHom _).symm
    rw [h0] at h1
    rw [hd, Matrix.GeneralLinearGroup.val_det_apply]
    exact h1
  set dv : Fin ν → Lˣ := Function.update (fun _ => 1) ⟨0, hν⟩ d with hdv
  set D : GL (Fin ν) L := diagGLn dv with hD
  have hDu : D ∈ unitaryGL_kd264alg σ := by
    change ((D : Matrix (Fin ν) (Fin ν) L).map σ)ᵀ * D = 1
    change ((Matrix.diagonal fun i => (dv i : L)).map σ)ᵀ * Matrix.diagonal (fun i => (dv i : L)) = 1
    rw [Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext j
    by_cases hj : j = ⟨0, hν⟩
    · subst hj
      simp [hdv, hσd]
    · simp [hdv, Function.update_of_ne hj]
  have hG₀det : ((G * D⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L).det = 1 := by
    have h1 : (Matrix.GeneralLinearGroup.det (G * D⁻¹) : L) = 1 := by
      rw [map_mul, map_inv, ← hd, Units.val_mul]
      have h2 : Matrix.GeneralLinearGroup.det D = d := by
        apply Units.ext
        rw [Matrix.GeneralLinearGroup.val_det_apply, hD]
        change (Matrix.diagonal fun i => (dv i : L)).det = d
        rw [Matrix.det_diagonal, Finset.prod_eq_single ⟨0, hν⟩]
        · simp [hdv]
        · intro j _ hj
          simp [hdv, Function.update_of_ne hj]
        · intro h
          exact absurd (Finset.mem_univ _) h
      rw [h2, Units.val_inv_eq_inv_val, mul_inv_cancel₀ d.ne_zero]
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at h1
  set X₀ : SL(ν, L) := ⟨((G * D⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L), hG₀det⟩ with hX₀
  have hX₀toGL : Matrix.SpecialLinearGroup.toGL X₀ = G * D⁻¹ := Units.ext rfl
  have hX₀C : X₀ ∈ unitaryFix_kd264alg σ := by
    rw [mem_unitaryFix_iff_toGL_kd264alg, hX₀toGL]
    exact mul_mem hGu (inv_mem hDu)
  have hσ₂c : ∀ c, σ (σ₂ c) = σ₂ (σ c) := hσσ₂
  let φD : MulAut ↥(unitaryFix_kd264alg (ν := ν) σ) :=
    CFSG.GroupActions.subgroupStabRestrict _ ⟨conjSLnAut_kd264alg D,
      map_conjSLnAut_unitaryFix_kd264alg hDu⟩
  let φ₂ : MulAut ↥(unitaryFix_kd264alg (ν := ν) σ) :=
    CFSG.GroupActions.subgroupStabRestrict _ ⟨slMapAut_kd264alg σ₂,
      map_slMapAut_unitaryFix_kd264alg hσ₂c⟩
  have hφD : ∀ X, ((φD X : SL(ν, L))) = conjSLn D X := fun X => rfl
  have hφDinv : ∀ X, ((φD⁻¹ X : SL(ν, L))) = conjSLn D⁻¹ X := fun X => rfl
  have hφ₂ : ∀ X, ((φ₂ X : SL(ν, L))) = Matrix.SpecialLinearGroup.map σ₂.toRingHom X :=
    fun X => rfl
  have hφ₂inv : ∀ X, ((φ₂⁻¹ X : SL(ν, L))) = Matrix.SpecialLinearGroup.map σ₂.symm.toRingHom X :=
    fun X => rfl
  have hσ₂D : Matrix.GeneralLinearGroup.map σ₂.toRingHom D = D * D := by
    apply Units.ext
    change ((Matrix.diagonal fun i => (dv i : L)).map σ₂) =
      Matrix.diagonal (fun i => (dv i : L)) * Matrix.diagonal (fun i => (dv i : L))
    rw [Matrix.diagonal_map (map_zero σ₂), Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    rw [hσ₂, sq]
  have h1 : φ = MulAut.conj (⟨X₀, hX₀C⟩ : ↥(unitaryFix_kd264alg (ν := ν) σ)) * φD := by
    ext X : 2
    rw [hφ, MulAut.mul_apply, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hφD]
    rw [← conjSLn_toGL, hX₀toGL, ← conjSLn_mul, mul_assoc, inv_mul_cancel,
      mul_one]
  have h2 : φD = ⁅φ₂, φD⁆ := by
    ext X : 2
    rw [commutatorElement_def, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply]
    simp only [hφ₂, hφD, hφ₂inv, hφDinv]
    rw [map_conjSLn, hσ₂D, conjSLn_mul]
    have h3 : Matrix.SpecialLinearGroup.map σ₂.toRingHom
        (Matrix.SpecialLinearGroup.map σ₂.symm.toRingHom (conjSLn D⁻¹ X)) = conjSLn D⁻¹ X := by
      apply Subtype.ext
      ext i j
      simp [Matrix.SpecialLinearGroup.map_apply_coe]
    rw [h3, ← conjSLn_mul D D⁻¹, mul_inv_cancel, conjSLn_one]
  rw [h1, h2]
  exact mul_mem (inner_le_innAutDerived _ ⟨_, rfl⟩)
    (commutator_le_innAutDerived _ (Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
      (Subgroup.mem_top _)))

end UnitaryAut

section Frame

variable {τ : Tag} {L : Type} [Field L]

theorem exists_conj_frame_of_mem_kd264alg {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {ν : ℕ} (hν : 0 < ν) {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σ) {u : ModGL τ L}
    (hu : u ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a))) :
    ∃ M : GL (Fin ν) L, ∀ A : SL(ν, L), u * ψ A * u⁻¹ = ψ (conjSLn M A) := by
  classical
  let N : Subgroup (ModGL τ L) :=
    { carrier := {u | ∃ M : GL (Fin ν) L, ∀ A : SL(ν, L), u * ψ A * u⁻¹ = ψ (conjSLn M A)}
      one_mem' := ⟨1, fun A => by rw [conjSLn_one]; group⟩
      mul_mem' := by
        rintro u v ⟨Mu, hMu⟩ ⟨Mv, hMv⟩
        refine ⟨Mu * Mv, fun A => ?_⟩
        rw [conjSLn_mul, ← hMu, ← hMv]
        group
      inv_mem' := by
        rintro u ⟨Mu, hMu⟩
        refine ⟨Mu⁻¹, fun A => ?_⟩
        have h := hMu (conjSLn Mu⁻¹ A)
        rw [← conjSLn_mul, mul_inv_cancel, conjSLn_one] at h
        rw [← h]
        group }
  have hT : torusGroup τ L ≤ N := by
    intro t ht
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    refine ⟨diagGLn (fun j => rootChar b (σ j ⟨0, hν⟩)), fun A => ?_⟩
    rw [conjSLn_diagGLn]
    exact hψ.torus ⟨0, hν⟩ b A
  have hR : rootSpan τ L (kernelRoots (rootCharHom a)) ≤ N := by
    rw [← iSup_componentRootSpan (K := L) (χ := rootCharHom a)]
    refine iSup_le fun j => ?_
    by_cases hij : j = i
    · subst hij
      intro g hg
      have hg' : g ∈ ψ.range := by
        rw [hψ.range, ← hΨ]
        exact hg
      obtain ⟨B, rfl⟩ := hg'
      refine ⟨Matrix.SpecialLinearGroup.toGL B, fun A => ?_⟩
      rw [conjSLn_toGL, map_mul, map_mul, map_inv]
    · intro g hg
      refine ⟨1, fun A => ?_⟩
      rw [conjSLn_one]
      have hA : ψ A ∈ componentRootSpan L (rootCharHom a) i := by
        change ψ A ∈ rootSpan τ L (componentRoots (rootCharHom a) i)
        rw [hΨ, ← hψ.range]
        exact ⟨A, rfl⟩
      have hc := Subgroup.mem_centralizer_iff.1 (componentRootSpan_le_centralizer L hij hg) _ hA
      rw [← hc, mul_inv_cancel_right]
  exact (sup_le hT hR : _ ≤ N) hu

end Frame

section Descent

variable {L : Type} [Field L] {ν : ℕ}

theorem exists_sl2_fixed_of_map_eq_mul_scalar_kd264alg [IsAlgClosed L] [CharP L 2]
    (σ : L ≃+* L) {q : ℕ} (hq : 2 ≤ q) (hσ : ∀ c, σ c = c ^ q) (M : GL (Fin 2) L) (u : Lˣ)
    (hM : Matrix.GeneralLinearGroup.map σ.toRingHom M =
      M * Matrix.GeneralLinearGroup.scalar (Fin 2) u) :
    ∃ A₁ : SL(2, L), Matrix.SpecialLinearGroup.map σ.toRingHom A₁ = A₁ ∧
      ∀ A : SL(2, L), conjSLn M A = A₁ * A * A₁⁻¹ := by
  classical
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (u : L) (n := q - 1) (by omega)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hμ
    exact u.ne_zero hμ.symm
  set m : Lˣ := Units.mk0 μ hμ0 with hm
  have hσm : Units.map (σ.toRingHom : L →* L) m = u * m := by
    apply Units.ext
    show σ μ = (u : L) * μ
    rw [hσ, ← hμ, ← pow_succ]
    congr 1
    omega
  set M₀ : GL (Fin 2) L := M * Matrix.GeneralLinearGroup.scalar (Fin 2) m⁻¹ with hM₀
  have hM₀σ : Matrix.GeneralLinearGroup.map σ.toRingHom M₀ = M₀ := by
    rw [hM₀, map_mul, hM, Matrix.GeneralLinearGroup.map_scalar, map_inv, hσm, mul_assoc,
      ← map_mul, mul_inv_rev, mul_comm m⁻¹ u⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
  obtain ⟨ε, hε⟩ := IsAlgClosed.exists_pow_nat_eq
    (Matrix.GeneralLinearGroup.det M₀ : L) (n := 2) (by norm_num)
  have hε0 : ε ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hε
    exact (Matrix.GeneralLinearGroup.det M₀).ne_zero hε.symm
  have hdetσ : σ (Matrix.GeneralLinearGroup.det M₀ : L) = Matrix.GeneralLinearGroup.det M₀ := by
    have h1 := congrArg (fun g : GL (Fin 2) L => (Matrix.GeneralLinearGroup.det g : L)) hM₀σ
    simp only [Matrix.GeneralLinearGroup.map_det] at h1
    exact h1
  have hσε : σ ε = ε := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : (σ ε - ε) ^ 2 = 0 := by
      rw [sub_pow_char (σ ε) ε, ← map_pow, hε, hdetσ, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h1)
  set e : Lˣ := Units.mk0 ε hε0 with he
  set M₁ : GL (Fin 2) L := M₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) e⁻¹ with hM₁
  have hdet1 : (M₁ : Matrix (Fin 2) (Fin 2) L).det = 1 := by
    have h1 : (Matrix.GeneralLinearGroup.det M₁ : L) = 1 := by
      rw [hM₁, map_mul, Units.val_mul]
      have h2 : (Matrix.GeneralLinearGroup.det
          (Matrix.GeneralLinearGroup.scalar (Fin 2) e⁻¹) : L) = ε⁻¹ ^ 2 := by
        rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_scalar,
          Matrix.det_fin_two]
        simp [he, Matrix.scalar_apply, sq]
      rw [h2, ← hε, inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hε0)]
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at h1
  set A₁ : SL(2, L) := ⟨(M₁ : Matrix (Fin 2) (Fin 2) L), hdet1⟩ with hA₁
  have hM₁σ : Matrix.GeneralLinearGroup.map σ.toRingHom M₁ = M₁ := by
    have hσe : Units.map (σ.toRingHom : L →* L) e = e := by
      apply Units.ext
      show σ ε = ε
      exact hσε
    rw [hM₁, map_mul, hM₀σ, Matrix.GeneralLinearGroup.map_scalar, map_inv, hσe]
  refine ⟨A₁, ?_, fun A => ?_⟩
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe, hA₁]
    exact congrArg Units.val hM₁σ
  · have h1 : M = M₁ * Matrix.GeneralLinearGroup.scalar (Fin 2) (e * m) := by
      rw [hM₁, hM₀, mul_assoc, mul_assoc, ← map_mul, ← map_mul]
      simp
    rw [h1, conjSLn_mul_scalar]
    apply Subtype.ext
    rw [coe_conjSLn, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    congr 1
    rw [coe_inv_eq_nonsing_inv]
    exact (Matrix.coe_units_inv M₁)

end Descent

section RankOne

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)

theorem rationalRoots_eq_of_orbitLength_one_kd264alg {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) :
    rationalRoots S.ρ (rootCharHom a) i = componentRoots (rootCharHom a) i := by
  obtain ⟨-, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  rw [hs1] at hs
  have hstab : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i :=
    fun γ hγ => by
      rw [← hs]
      exact ⟨γ, hγ, rfl⟩
  ext γ
  constructor
  · rintro ⟨k, δ, hδ, rfl⟩
    induction k with
    | zero => exact hδ
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hstab _ ih
  · intro hγ
    exact ⟨0, γ, hγ, rfl⟩

theorem rationalComponent_le_rootSpan_kd264alg {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) :
    rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan τ L (componentRoots (rootCharHom a) i) := by
  have h1 : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ rationalSpan S.ρ S.Γ (rootCharHom a) i :=
    Subgroup.commutator_le_self _
  refine h1.trans (inf_le_left.trans ?_)
  rw [rationalRoots_eq_of_orbitLength_one_kd264alg S hT i hs1]

variable [CharP L 2]

theorem exists_mem_rationalComponent_conj_eq_rankOne_kd264alg {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (h1 : compRank (componentRoots (rootCharHom a) i) = 1)
    (hn : (componentRoots (rootCharHom a) i).ncard = 2)
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (hQ : 4 ≤ S.D.q) {y : ModGL τ L}
    (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y) :
    ∃ w ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      ∀ r ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, y * r * y⁻¹ = w * r * w⁻¹ := by
  classical
  obtain ⟨β, hβ, hΨ⟩ := exists_pair_of_rank_one i hn
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  haveI : NeZero (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := ⟨hs0.ne'⟩
  have hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) :=
    twistInner_of_twistKind_eq_innerT S CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds
      hT i (CFSG.LocalAnalysis.GLTheoremA.RationalModel.twistKind_eq_inner_of_compRank_eq_one S i h1)
  obtain ⟨σ, z, hσ, hzZ, hnorm, hz⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.exists_untwistT_Z S hT i hs0 hinner
  have hσ1 : ∀ c, σ c = c ^ S.D.q := fun c => by rw [hσ, hs1, pow_one]
  set ψ : SL(2, L) →* ModGL τ L := rootSL2 τ L β with hψdef
  have hψ : IsSLFrame ψ (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.rankOneSigma β) :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.isSLFrame_rootSL2 hβ
  have hΨf : componentRoots (rootCharHom a) i =
      frameRoots (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.rankOneSigma β) := by
    rw [hΨ, CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.frameRoots_rankOneSigma]
  have hψS : ∀ A, ψ A ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := fun A => by
    rw [hΨf, ← hψ.range]
    exact ⟨A, rfl⟩
  have hFz : ∀ A : SL(2, L), S.D.step (z * ψ A * z⁻¹) =
      z * ψ (Matrix.SpecialLinearGroup.map σ.toRingHom A) * z⁻¹ := by
    intro A
    have h := hz (ψ A) (hψS A)
    rw [hs1] at h
    rw [← frobGL_rootSL2 σ hβ A]
    exact h
  have huZ : z⁻¹ * y * z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) :=
    mul_mem (mul_mem (inv_mem hzZ) hyZ) hzZ
  obtain ⟨M, hM⟩ := exists_conj_frame_of_mem_kd264alg i two_pos hψ hΨf huZ
  have hyA : ∀ A : SL(2, L), y * (z * ψ A * z⁻¹) * y⁻¹ = z * ψ (conjSLn M A) * z⁻¹ := by
    intro A
    rw [← hM A]
    group
  have hcomm : ∀ A : SL(2, L), Matrix.SpecialLinearGroup.map σ.toRingHom (conjSLn M A) =
      conjSLn M (Matrix.SpecialLinearGroup.map σ.toRingHom A) := by
    intro A
    have e2 : S.D.step (y * (z * ψ A * z⁻¹) * y⁻¹) = y * S.D.step (z * ψ A * z⁻¹) * y⁻¹ := by
      rw [map_mul, map_mul, map_inv, hyF]
    rw [hyA, hFz, hFz, hyA] at e2
    apply CFSG.RankThree.Chevalley.rootSL2_injective_of_field (K := L) β
    have e3 := mul_left_cancel (mul_right_cancel e2)
    exact e3
  have hsurj : Function.Surjective (Matrix.SpecialLinearGroup.map σ.toRingHom : SL(2, L) → _) := by
    intro A
    refine ⟨Matrix.SpecialLinearGroup.map σ.symm.toRingHom A, ?_⟩
    apply Subtype.ext
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  have hC : ∀ A : SL(2, L),
      conjSLn (M⁻¹ * Matrix.GeneralLinearGroup.map σ.toRingHom M) A = A := by
    intro A
    obtain ⟨A₀, rfl⟩ := hsurj A
    rw [conjSLn_mul, ← map_conjSLn, hcomm, ← conjSLn_mul,
      inv_mul_cancel, conjSLn_one]
  obtain ⟨c, hc⟩ := exists_scalar_of_commute_conjSLn_kd264alg _ hC
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 := congrArg Matrix.det hc
    rw [Matrix.scalar_apply, Matrix.diagonal_zero, Matrix.det_zero] at h1
    exact (Matrix.isUnits_det_units _).ne_zero h1
  set u : Lˣ := Units.mk0 c hc0 with hu
  have hMu : Matrix.GeneralLinearGroup.map σ.toRingHom M =
      M * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
    have h1 : M⁻¹ * Matrix.GeneralLinearGroup.map σ.toRingHom M =
        Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
      apply Units.ext
      rw [hc, Matrix.GeneralLinearGroup.coe_scalar, hu, Units.val_mk0]
    rw [← h1, mul_inv_cancel_left]
  have hq2 : 2 ≤ S.D.q := by omega
  obtain ⟨A₁, hA₁σ, hA₁⟩ := exists_sl2_fixed_of_map_eq_mul_scalar_kd264alg σ hq2 hσ1 M u hMu
  set w : ModGL τ L := z * ψ A₁ * z⁻¹ with hw
  have hwR : w ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
    haveI : Fact r.Prime := ⟨hr⟩
    haveI : CharP L r := hchar
    have hσ' : ∀ c, σ c = c ^ (r ^ (e * 1)) := fun c => by rw [hσ1, hq, mul_one]
    have hQ' : 4 ≤ r ^ (e * 1) := by rw [mul_one, ← hq]; exact hQ
    obtain ⟨t, ht⟩ := CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_unit_sq_ne_one (L := L) σ hσ'
      (by omega) hQ'
    have hperf := CFSG.HardMathSupport.Timmesfeld.CrossChar.isPerfect_componentRootSpan_of_sq_ne_one
      (K := fixSubfield σ) (χ := rootCharHom a) ht i
    have hmem : ∀ i j, (A₁ : Matrix (Fin 2) (Fin 2) L) i j ∈ fixSubfield σ := by
      intro i j
      have h2 := congrArg (fun X : SL(2, L) => (X : Matrix (Fin 2) (Fin 2) L) i j) hA₁σ
      simpa [Matrix.SpecialLinearGroup.map_apply_coe] using h2
    let A₁' : SL(2, fixSubfield σ) := ⟨Matrix.of fun i j => ⟨_, hmem i j⟩, by
      apply (fixSubfield σ).subtype.injective
      rw [RingHom.map_det, map_one]
      have : (fixSubfield σ).subtype.mapMatrix (Matrix.of fun i j => (⟨_, hmem i j⟩ :
          fixSubfield σ)) = (A₁ : Matrix (Fin 2) (Fin 2) L) := by
        ext i j
        rfl
      rw [this, A₁.2]⟩
    have hA₁' : Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype A₁' = A₁ := by
      apply Subtype.ext
      ext i j
      rfl
    have hcmem : rootSL2 τ (fixSubfield σ) β A₁' ∈
        componentRootSpan (fixSubfield σ) (rootCharHom a) i := by
      change rootSL2 τ (fixSubfield σ) β A₁' ∈
        rootSpan τ (fixSubfield σ) (componentRoots (rootCharHom a) i)
      have hrange : rootSpan τ (fixSubfield σ) {β, -β} = (rootSL2 τ (fixSubfield σ) β).range := by
        rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hβ]
        simp only [rootSpan, iSup_insert, iSup_singleton]
      rw [hΨ, hrange]
      exact ⟨A₁', rfl⟩
    have hιc : baseChangeGL (fixSubfield σ).subtype (rootSL2 τ (fixSubfield σ) β A₁') = ψ A₁ := by
      rw [CFSG.RankThree.Chevalley.baseChangeGL_rootSL2_of_field, hA₁']
    have hF : S.D.step (z * baseChangeGL (fixSubfield σ).subtype
        (⟨_, hcmem⟩ : ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i)).1 * z⁻¹) =
        z * baseChangeGL (fixSubfield σ).subtype
          (⟨_, hcmem⟩ : ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i)).1 * z⁻¹ := by
      change S.D.step (z * baseChangeGL (fixSubfield σ).subtype (rootSL2 τ (fixSubfield σ) β A₁')
        * z⁻¹) = z * baseChangeGL (fixSubfield σ).subtype (rootSL2 τ (fixSubfield σ) β A₁') * z⁻¹
      rw [hιc, hFz, hA₁σ]
    have h2 := CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.pow_mem_rationalComponent_of_fixed S hT i
      hs hmin σ z hnorm hz hperf ⟨_, hcmem⟩ hF
    change (z * baseChangeGL (fixSubfield σ).subtype (rootSL2 τ (fixSubfield σ) β A₁') * z⁻¹) ^
      componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∈ _ at h2
    rw [hιc, hs1, pow_one] at h2
    exact h2
  refine ⟨w, hwR, fun r hr => ?_⟩
  have hrS := rationalComponent_le_rootSpan_kd264alg S hT i hs1 hr
  have hr' : z⁻¹ * r * z ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    refine (hnorm i _).2 ?_
    have e : z * (z⁻¹ * r * z) * z⁻¹ = r := by group
    rw [e]
    exact hrS
  rw [hΨf, ← hψ.range] at hr'
  obtain ⟨A, hA⟩ := hr'
  have hrA : r = z * ψ A * z⁻¹ := by
    rw [hA]
    group
  rw [hrA, hyA, hA₁ A, hw, map_mul, map_mul, map_inv]
  group

end RankOne

section UnitaryUntwist

open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremB

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)

theorem exists_unitary_untwist_kd264alg {ta : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ ta ∈ S.D.torus) (i : KernelComponent (rootCharHom ta)) {ν : ℕ}
    (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ)
    (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π b) (π a))
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e) :
    ∃ (σQ : L ≃+* L) (z : ModGL τ L),
      (∀ c, σQ c = c ^ (r ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i)))) ∧
      z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom ta)) ∧
      (∀ j : KernelComponent (rootCharHom ta), ∀ g : ModGL τ L,
        g ∈ rootSpan τ L (componentRoots (rootCharHom ta) j) ↔
          z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom ta) j)) ∧
      ∀ X : SL(ν, L), iterHom S.D.step (componentOrbitLength S.ρ
          (componentRoots (rootCharHom ta) i)) (z * ψ X * z⁻¹) =
        z * ψ (stdUnitary σQ.toRingHom X) * z⁻¹ := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  have : NeZero s := ⟨hs0.ne'⟩
  have : Fact r.Prime := ⟨hr⟩
  have : CharP L r := hchar
  obtain ⟨σQ, hσQ⟩ := exists_ringEquiv_frob (L := L) r (e * s)
  have hσc : ∀ c, σQ c = c ^ (r ^ (e * s)) := fun c => by
    have h1 : σQ c = iterateFrobenius L r (e * s) c := by
      rw [← hσQ]
      rfl
    rw [h1, iterateFrobenius_def]
  have hQ : S.D.q ^ s = r ^ (e * s) := by rw [hq, ← pow_mul]
  set Fs : ModGL τ L →* ModGL τ L := iterHom S.D.step s with hFs
  choose! ε hε using fun (a b : Fin ν) (hab : a ≠ b) => hψ.transv a b hab
  have hπne : ∀ a b : Fin ν, a ≠ b → π b ≠ π a := fun a b hab => (π.injective.ne hab).symm
  have hstepU : ∀ a b : Fin ν, a ≠ b → ∃ μ : Lˣ, ∀ c : L,
      Fs (pinnedX τ L (σ a b) c) = pinnedX τ L (σ (π b) (π a)) ((μ : L) * σQ c) := by
    intro a b hab
    obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S s (hψ.isRoot a b hab)
    refine ⟨Units.mk0 μ hμ0, fun c => ?_⟩
    rw [hFs, iterHom_eq_iterate, hμ, hπ a b hab, hσc, ← hQ]
    rfl
  choose! μ hμ using hstepU
  set β : Fin ν → Fin ν → Lˣ := fun a b =>
    μ a b * ε a b ^ (r ^ (e * s)) * (ε (π b) (π a))⁻¹ with hβ
  have hkey : ∀ (a b : Fin ν) (hab : a ≠ b) (t : L),
      Fs (ψ (Matrix.SpecialLinearGroup.transvection hab t)) =
        ψ (Matrix.SpecialLinearGroup.transvection (hπne a b hab) ((β a b : L) * σQ t)) := by
    intro a b hab t
    rw [hε a b hab t, hμ a b hab, hε (π b) (π a) (hπne a b hab)]
    congr 1
    rw [map_mul, hσc (ε a b : L), hβ]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    have h0 : (ε (π b) (π a) : L) ≠ 0 := Units.ne_zero _
    field_simp
  have hcoc : ∀ a b c : Fin ν, a ≠ b → b ≠ c → a ≠ c → β a c = -(β a b * β b c) := by
    intro a b c hab hbc hac
    have hcomm := Matrix.SpecialLinearGroup.commutatorElement_transvection hab hbc hac (1 : L) 1
    rw [mul_one] at hcomm
    have h1 := congrArg (fun X => Fs (ψ X)) hcomm
    simp only [map_commutatorElement] at h1
    rw [hkey a b hab, hkey b c hbc, hkey a c hac, map_one, mul_one, mul_one, mul_one,
      ← map_commutatorElement ψ,
      commutator_transvection_rev (hπne a b hab) (hπne b c hbc) (hπne a c hac),
      hε _ _ (hπne a c hac), hε _ _ (hπne a c hac)] at h1
    have h2 := pinnedX_injective τ L _ h1
    have h0 : (ε (π c) (π a) : L) ≠ 0 := Units.ne_zero _
    apply Units.ext
    have h3 := mul_left_cancel₀ h0 h2
    rw [Units.val_neg, Units.val_mul]
    exact h3.symm
  obtain ⟨d, hd⟩ := exists_units_of_cocycle hν β hcoc
  set M : GL (Fin ν) L := diagHom ν d * (permGL π : GL (Fin ν) L)⁻¹ with hMdef
  obtain ⟨B, hB⟩ := exists_specialLinear_conj_eq (n := ν) (by omega) M
  have hBconj : ∀ (a b : Fin ν) (hab : a ≠ b) (u : L),
      B * Matrix.SpecialLinearGroup.transvection (hπne a b hab) u * B⁻¹ =
        Matrix.SpecialLinearGroup.transvection (Ne.symm hab) ((d b : L) * u * ((d a)⁻¹ : Lˣ)) := by
    intro a b hab u
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe, hB]
    have hM : ∀ Y : Matrix (Fin ν) (Fin ν) L, (M : Matrix (Fin ν) (Fin ν) L) * Y *
        (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) = (diagHom ν d : Matrix (Fin ν) (Fin ν) L) *
          ((↑(permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) * Y *
            ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)) *
              (↑(diagHom ν d)⁻¹ : Matrix (Fin ν) (Fin ν) L) := by
      intro Y
      simp only [hMdef, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
    rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul,
      permGL_inv_mul_single_mul, diagHom_mul_one_add_single_mul d (Ne.symm hab) u]
  have hstd : ∀ X : SL(ν, L), ψ B * Fs (ψ X) * (ψ B)⁻¹ = ψ (stdUnitary σQ.toRingHom X) := by
    have h : (MulAut.conj (ψ B)).toMonoidHom.comp (Fs.comp ψ) =
        ψ.comp (stdUnitary σQ.toRingHom) := by
      refine MonoidHom.eq_of_eqOn_dense
        (CFSG.LinearGroups.special_linear_elementary_generation (n := ν) (K := L)) ?_
      rintro _ ⟨a, b, hab, t, rfl⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hkey a b hab t, ← map_mul, ← map_inv, ← map_mul, hBconj a b hab,
        stdUnitary_transvection]
      congr 2
      rw [hd a b hab]
      simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      have h0 : (d a : L) ≠ 0 := Units.ne_zero _
      have h0' : (d b : L) ≠ 0 := Units.ne_zero _
      field_simp
    intro X
    have := DFunLike.congr_fun h X
    simpa [MulAut.conj_apply] using this
  have hψS : ∀ X, ψ X ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) := fun X => by
    rw [hΨ, ← hψ.range]
    exact ⟨X, rfl⟩
  have hy₁ : ψ B ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom ta)) :=
    Subgroup.mem_sup_right (rootSpan_mono (fun γ hγ => hγ.1) (hψS B))
  obtain ⟨z, hzZ, hz⟩ := exists_lang_torus_sup_kernelRoots S hs0
    (fun γ hγ => outer_iterate_mem_kernelRoots S hT s hγ) hy₁
  refine ⟨σQ, z, hσc, hzZ, mem_componentRootSpan_iff_conj_of_mem hzZ, fun X => ?_⟩
  rw [← hstd X, map_mul, map_mul, map_inv, hz]
  group

end UnitaryUntwist

section UnitaryCore

open Matrix
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms

private noncomputable def invTransposeGL_kd264alg {L : Type} [Field L] {ν : ℕ} :
    GL (Fin ν) L →* GL (Fin ν) L where
  toFun N := ⟨((N⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)ᵀ,
    ((N : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)ᵀ,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' N N' := by
    apply Units.ext
    change (((N * N')⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)ᵀ =
      ((N⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)ᵀ *
        ((N'⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)ᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private noncomputable def stdGL_kd264alg {L : Type} [Field L] {ν : ℕ} (σ : L ≃+* L) :
    GL (Fin ν) L →* GL (Fin ν) L :=
  invTransposeGL_kd264alg.comp (Matrix.GeneralLinearGroup.map σ.toRingHom)

private theorem coe_stdGL_kd264alg {L : Type} [Field L] {ν : ℕ} (σ : L ≃+* L)
    (N : GL (Fin ν) L) :
    ((stdGL_kd264alg σ N : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) =
      (((N : Matrix (Fin ν) (Fin ν) L).map σ)⁻¹)ᵀ := by
  change ((((Matrix.GeneralLinearGroup.map σ.toRingHom N)⁻¹ : GL (Fin ν) L) :
    Matrix (Fin ν) (Fin ν) L))ᵀ = _
  rw [Matrix.coe_units_inv]
  rfl

private theorem toGL_stdUnitary_kd264alg {L : Type} [Field L] {ν : ℕ} (σ : L ≃+* L)
    (A : SL(ν, L)) :
    Matrix.SpecialLinearGroup.toGL (stdUnitary σ.toRingHom A) =
      stdGL_kd264alg σ (Matrix.SpecialLinearGroup.toGL A) := by
  apply Units.ext
  rw [coe_stdGL_kd264alg]
  change ((stdUnitary σ.toRingHom A : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) = _
  rw [coe_stdUnitary]
  rfl

private theorem toGL_conjSLn_kd264alg {L : Type} [Field L] {ν : ℕ} (M : GL (Fin ν) L)
    (A : SL(ν, L)) :
    Matrix.SpecialLinearGroup.toGL (conjSLn M A) = M * Matrix.SpecialLinearGroup.toGL A * M⁻¹ := by
  apply Units.ext
  change ((conjSLn M A : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) = _
  rw [coe_conjSLn, Units.val_mul, Units.val_mul]
  rfl

private theorem stdUnitary_conjSLn_kd264alg {L : Type} [Field L] {ν : ℕ} (σ : L ≃+* L)
    (M : GL (Fin ν) L) (A : SL(ν, L)) :
    stdUnitary σ.toRingHom (conjSLn M A) = conjSLn (stdGL_kd264alg σ M) (stdUnitary σ.toRingHom A) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_stdUnitary_kd264alg, toGL_conjSLn_kd264alg, toGL_conjSLn_kd264alg, map_mul, map_mul,
    map_inv, toGL_stdUnitary_kd264alg]

private theorem stdGL_scalar_kd264alg {L : Type} [Field L] {ν : ℕ} (σ : L ≃+* L) (μ : Lˣ) :
    stdGL_kd264alg σ (Matrix.GeneralLinearGroup.scalar (Fin ν) μ) =
      Matrix.GeneralLinearGroup.scalar (Fin ν) (Units.map (σ.toRingHom : L →* L) μ)⁻¹ := by
  rw [stdGL_kd264alg, MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_scalar]
  apply Units.ext
  change (((Matrix.GeneralLinearGroup.scalar (Fin ν) (Units.map (σ.toRingHom : L →* L) μ))⁻¹ :
    GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)ᵀ = _
  rw [← map_inv, Matrix.GeneralLinearGroup.coe_scalar]
  simp only [Matrix.scalar_apply, Matrix.diagonal_transpose]

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)

theorem range_le_rationalComponent_of_perfect_kd264alg {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) {C : Type*}
    [Group C] (hC : commutator C = ⊤) (θ : C →* ModGL τ L)
    (hθS : ∀ c, θ c ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    (hθF : ∀ c, S.D.step (θ c) = θ c) :
    θ.range ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  have hCp : Group.IsPerfect C := Group.isPerfect_def.2 hC
  have hM : ∀ c, θ c ∈ S.D.model := fun c =>
    ⟨rootSpan_le_adjointGroup L _ (hθS c), hθF c⟩
  have hΓ : ∀ c, θ c ∈ S.Γ := map_mem_commutator_of_perfect hCp θ S.D.model hM
  have hRS : ∀ c, θ c ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i := by
    intro c
    refine Subgroup.mem_inf.2 ⟨?_, hΓ c⟩
    rw [rationalRoots_eq_of_orbitLength_one_kd264alg S hT i hs1]
    exact hθS c
  rintro _ ⟨c, rfl⟩
  exact map_mem_commutator_of_perfect hCp θ _ hRS c

theorem centerQuotientHom_mem_innAutDerived_unitaryFrame_kd264alg [CharP L 2] {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) {ν : ℕ}
    (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σf : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σf) (hΨ : componentRoots (rootCharHom a) i = frameRoots σf)
    (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a' b, a' ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σf a' b) = σf (π b) (π a'))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (h32 : (ν, S.D.q) ≠ (3, 2)) {y : ModGL τ L}
    (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y)
    (hy : MulAut.conj y ∈
      CFSG.GroupActions.subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    centerQuotientHom _ (CFSG.GroupActions.subgroupStabRestrict _ ⟨MulAut.conj y, hy⟩) ∈
      innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc2 : CharP L 2 := inferInstance
  obtain ⟨σ₂, hσ₂⟩ := exists_ringEquiv_frob (L := L) 2 1
  set R := rationalComponent S.ρ S.Γ (rootCharHom a) i with hR
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨σQ, z, hσQ, hzZ, hnorm, hconj⟩ :=
    exists_unitary_untwist_kd264alg S hT i hν hψ hΨ π hπ hr hchar he hq
  rw [hs1] at hσQ hconj
  have hF : ∀ X : SL(ν, L), S.D.step (z * ψ X * z⁻¹) = z * ψ (stdUnitary σQ.toRingHom X) * z⁻¹ :=
    hconj
  have hσq : ∀ c, σQ c = c ^ S.D.q := fun c => by rw [hσQ, mul_one, hq]
  set C := CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ) with hCdef
  have hσQ' : ∀ c, σQ c = c ^ (r ^ (e * 1)) := hσQ
  have hCq := (stdUnitary_fixSubgroup (ν := ν) hr (f := e * 1) (by omega) σQ hσQ' hν).2.1
    (by rw [mul_one, ← hq]; exact h32)
  have hCperf : commutator C = ⊤ := hCq.1.commutator_eq_top
  have hCmem : ∀ X : SL(ν, L), X ∈ C ↔ stdUnitary σQ.toRingHom X = X := fun X => by
    rw [hCdef, CFSG.RankThree.Classical2.mem_fixSubgroup, stdUnitaryEquiv_apply]
  have hψS : ∀ X, ψ X ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := fun X => by
    rw [hΨ, ← hψ.range]
    exact ⟨X, rfl⟩
  have hkerne : ψ.ker ≠ ⊤ := by
    intro h
    have h01 : (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ := by simp
    obtain ⟨ε, hε⟩ := hψ.transv _ _ h01
    have h1 : Matrix.SpecialLinearGroup.transvection h01 (1 : L) ∈ ψ.ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hε, mul_one, ← pinnedX_zero τ L (σf _ _)] at h1
    exact Units.ne_zero _ (pinnedX_injective τ L _ h1)
  have hSLq : CFSG.IsQuasisimple SL(ν, L) := isQuasisimple_specialLinearGroup hν
  have hker : ψ.ker ≤ Subgroup.center SL(ν, L) := by
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hSLq ψ.ker with h | h
    · exact h
    · exact absurd h hkerne
  let θ : C →* ModGL τ L := (MulAut.conj z).toMonoidHom.comp (ψ.comp C.subtype)
  have hθ : ∀ c : C, θ c = z * ψ c * z⁻¹ := fun c => rfl
  have hθS : ∀ c : C, θ c ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := fun c => by
    rw [hθ]
    exact (hnorm i _).1 (hψS c)
  have hθF : ∀ c : C, S.D.step (θ c) = θ c := fun c => by
    rw [hθ, hF, (hCmem c).1 c.2]
  have hθR1 : θ.range ≤ R :=
    range_le_rationalComponent_of_perfect_kd264alg S hT i hs1 hCperf θ hθS hθF
  have hpre : ∀ g ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i, ∃ X : SL(ν, L),
      g = z * ψ X * z⁻¹ ∧ stdUnitary σQ.toRingHom X * X⁻¹ ∈ Subgroup.center SL(ν, L) := by
    intro g hg
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
    rw [rationalRoots_eq_of_orbitLength_one_kd264alg S hT i hs1] at hg1
    have h1 : z⁻¹ * g * z ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := (hnorm i _).2 (by
      have e : z * (z⁻¹ * g * z) * z⁻¹ = g := by group
      rw [e]
      exact hg1)
    rw [hΨ, ← hψ.range] at h1
    obtain ⟨X, hX⟩ := h1
    have hgX : g = z * ψ X * z⁻¹ := by rw [hX]; group
    refine ⟨X, hgX, hker ?_⟩
    have hgF : S.D.step g = g := ((Subgroup.commutator_le_self S.D.model) hg2).2
    rw [hgX, hF] at hgF
    have h2 : ψ (stdUnitary σQ.toRingHom X) = ψ X := by
      have := hgF
      exact mul_right_cancel (mul_left_cancel this)
    rw [MonoidHom.mem_ker, map_mul, map_inv, h2, mul_inv_cancel]
  have hθR2 : R ≤ θ.range := by
    rw [hR, rationalComponent, Subgroup.commutator_le]
    intro g hg g' hg'
    obtain ⟨X, rfl, hc⟩ := hpre g hg
    obtain ⟨X', rfl, hc'⟩ := hpre g' hg'
    set c := stdUnitary σQ.toRingHom X * X⁻¹ with hcdef
    set c' := stdUnitary σQ.toRingHom X' * X'⁻¹ with hc'def
    have hX : stdUnitary σQ.toRingHom X = c * X := by rw [hcdef, inv_mul_cancel_right]
    have hX' : stdUnitary σQ.toRingHom X' = c' * X' := by rw [hc'def, inv_mul_cancel_right]
    have hcomm : ∀ (w : SL(ν, L)) (hw : w ∈ Subgroup.center SL(ν, L)) (v : SL(ν, L)),
        Commute w v := fun w hw v => (Subgroup.mem_center_iff.1 hw v).symm
    have hfixc : stdUnitary σQ.toRingHom ⁅X, X'⁆ = ⁅X, X'⁆ := by
      rw [map_commutatorElement, hX, hX']
      exact CFSG.HardMathSupport.Timmesfeld.LangTorus.CycFamily.commutatorElement_central_mul
        (hcomm c hc X) (hcomm c hc X') (hcomm c hc c') (hcomm c' hc' X) (hcomm c' hc' X')
    refine ⟨⟨⁅X, X'⁆, (hCmem _).2 hfixc⟩, ?_⟩
    rw [hθ]
    simp only [commutatorElement_def, map_mul, map_inv]
    group
  have hθR : θ.range = R := le_antisymm hθR1 hθR2
  have huZ : z⁻¹ * y * z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) :=
    mul_mem (mul_mem (inv_mem hzZ) hyZ) hzZ
  obtain ⟨M, hM⟩ := exists_conj_frame_of_mem_kd264alg i (by omega) hψ hΨ huZ
  have hyA : ∀ A : SL(ν, L), y * (z * ψ A * z⁻¹) * y⁻¹ = z * ψ (conjSLn M A) * z⁻¹ := by
    intro A
    rw [← hM A]
    group
  have hMinv : ∀ A : SL(ν, L), ψ (conjSLn M⁻¹ A) = (z⁻¹ * y * z)⁻¹ * ψ A * (z⁻¹ * y * z) := by
    intro A
    have h1 := hM (conjSLn M⁻¹ A)
    rw [← conjSLn_mul, mul_inv_cancel, conjSLn_one] at h1
    rw [← h1]
    group
  have hcomm : ∀ A : SL(ν, L), ψ (conjSLn (stdGL_kd264alg σQ M) (stdUnitary σQ.toRingHom A)) =
      ψ (conjSLn M (stdUnitary σQ.toRingHom A)) := by
    intro A
    have e2 : S.D.step (y * (z * ψ A * z⁻¹) * y⁻¹) = y * S.D.step (z * ψ A * z⁻¹) * y⁻¹ := by
      rw [map_mul, map_mul, map_inv, hyF]
    rw [hyA, hF, hF, hyA, stdUnitary_conjSLn_kd264alg] at e2
    exact mul_right_cancel (mul_left_cancel e2)
  have hstdsurj : Function.Surjective (stdUnitary (ν := ν) σQ.toRingHom) := fun X =>
    ⟨(stdUnitaryEquiv (ν := ν) σQ).symm X, (stdUnitaryEquiv (ν := ν) σQ).apply_symm_apply X⟩
  set Dm : GL (Fin ν) L := M⁻¹ * stdGL_kd264alg σQ M with hDm
  have hDψ : ∀ B : SL(ν, L), ψ (conjSLn Dm B) = ψ B := by
    intro B
    obtain ⟨A, rfl⟩ := hstdsurj B
    rw [hDm, conjSLn_mul, hMinv, hcomm, ← hM]
    group
  haveI : Group.IsPerfect SL(ν, L) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hν
  have hDtriv : ∀ B : SL(ν, L), conjSLn Dm B = B := by
    have h1 : onCenterQuotient (conjSLnAut_kd264alg Dm) = 1 := by
      ext x
      obtain ⟨B, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(ν, L)) x
      rw [onCenterQuotient_apply_mk]
      change (QuotientGroup.mk' (Subgroup.center SL(ν, L))) (conjSLn Dm B) =
        (QuotientGroup.mk' (Subgroup.center SL(ν, L))) B
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hDψ, inv_mul_cancel]
    have h2 := onCenterQuotient_eq_one_imp (conjSLnAut_kd264alg Dm) h1
    intro B
    have := congrArg (fun φ : MulAut SL(ν, L) => φ B) h2
    exact this
  obtain ⟨c, hc⟩ := exists_scalar_of_commute_conjSLn_kd264alg Dm hDtriv
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 := congrArg Matrix.det hc
    haveI : Nonempty (Fin ν) := ⟨⟨0, by omega⟩⟩
    rw [Matrix.scalar_apply, Matrix.diagonal_zero, Matrix.det_zero] at h1
    exact (Matrix.isUnits_det_units _).ne_zero h1
  set u : Lˣ := Units.mk0 c hc0 with hu
  have hMu : stdGL_kd264alg σQ M = M * Matrix.GeneralLinearGroup.scalar (Fin ν) u := by
    have h1 : Dm = Matrix.GeneralLinearGroup.scalar (Fin ν) u := by
      apply Units.ext
      rw [hc, Matrix.GeneralLinearGroup.coe_scalar, hu, Units.val_mk0]
    rw [← h1, hDm, mul_inv_cancel_left]
  obtain ⟨μ₀, hμ₀⟩ := IsAlgClosed.exists_pow_nat_eq (u : L) (n := S.D.q + 1) (by omega)
  have hμ0 : μ₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hμ₀
    exact u.ne_zero hμ₀.symm
  set μ : Lˣ := Units.mk0 μ₀ hμ0 with hμ
  set G : GL (Fin ν) L := M * Matrix.GeneralLinearGroup.scalar (Fin ν) μ with hG
  have hσμ : Units.map (σQ.toRingHom : L →* L) μ = u * μ⁻¹ := by
    apply Units.ext
    show σQ μ₀ = (u : L) * μ₀⁻¹
    rw [hσq, ← hμ₀, pow_succ]
    field_simp
  have hGstd : stdGL_kd264alg σQ G = G := by
    rw [hG, map_mul, hMu, stdGL_scalar_kd264alg, hσμ, mul_assoc, ← map_mul, _root_.mul_inv_rev,
      inv_inv,
      mul_comm μ u⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
  have hGu : ((G : Matrix (Fin ν) (Fin ν) L).map σQ)ᵀ * G = 1 := by
    have h1 := congrArg (fun g : GL (Fin ν) L => (g : Matrix (Fin ν) (Fin ν) L)) hGstd
    simp only [coe_stdGL_kd264alg] at h1
    have hdet : IsUnit ((G : Matrix (Fin ν) (Fin ν) L).map σQ).det := by
      have h0 : ((G : Matrix (Fin ν) (Fin ν) L).map σQ).det =
          σQ (G : Matrix (Fin ν) (Fin ν) L).det := (RingHom.map_det σQ.toRingHom _).symm
      rw [h0]
      exact (Matrix.isUnits_det_units G).map σQ
    calc ((G : Matrix (Fin ν) (Fin ν) L).map σQ)ᵀ * (G : Matrix (Fin ν) (Fin ν) L) =
        ((G : Matrix (Fin ν) (Fin ν) L).map σQ)ᵀ *
          (((G : Matrix (Fin ν) (Fin ν) L).map σQ)⁻¹)ᵀ := by rw [h1]
      _ = 1 := by
        rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.transpose_one]
  have hGM : ∀ A : SL(ν, L), conjSLn G A = conjSLn M A := fun A => by
    rw [hG, conjSLn_mul_scalar]
  have hGuGL : G ∈ unitaryGL_kd264alg σQ := hGu
  let φ : MulAut C := CFSG.GroupActions.subgroupStabRestrict _ ⟨conjSLnAut_kd264alg G,
    map_conjSLnAut_unitaryFix_kd264alg hGuGL⟩
  have hφ : ∀ X : C, ((φ X : SL(ν, L))) = conjSLn G X := fun X => rfl
  have hσ₂c : ∀ c, σ₂ c = c ^ 2 := fun c => by
    have h1 : σ₂ c = iterateFrobenius L 2 1 c := by rw [← hσ₂]; rfl
    rw [h1, iterateFrobenius_def, pow_one]
  have hσσ₂ : ∀ c, σQ (σ₂ c) = σ₂ (σQ c) := fun c => by
    rw [hσq, hσq, hσ₂c, hσ₂c, ← pow_mul, ← pow_mul, mul_comm]
  have hφinn : φ ∈ innAutDerived C := by
    haveI := hc2
    exact mem_innAutDerived_of_unitary_conj_kd264alg (by omega) σQ σ₂ hσ₂c hσσ₂ G hGu φ hφ
  let θ' : C →* R := θ.codRestrict R (fun c => hθR ▸ ⟨c, rfl⟩)
  have hθ'surj : Function.Surjective θ' := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ : x ∈ θ.range := hθR ▸ hx
    exact ⟨c, Subtype.ext hc⟩
  have hθ'ker : θ'.ker ≤ Subgroup.center C := by
    intro c hc
    have h1 : θ c = 1 := congrArg Subtype.val hc
    rw [hθ] at h1
    have h2 : ψ (c : SL(ν, L)) = 1 := by
      have : z * ψ c * z⁻¹ = z * 1 * z⁻¹ := by rw [h1]; group
      exact mul_right_cancel (mul_left_cancel this)
    have h3 := hker h2
    rw [Subgroup.mem_center_iff] at h3 ⊢
    intro d
    exact Subtype.ext (h3 d)
  refine centerQuotientHom_mem_innAutDerived_of_surjective_kd264alg hCperf θ' hθ'surj hθ'ker
    (φ := φ) ?_ hφinn
  intro x
  apply Subtype.ext
  change θ (φ x) = y * θ x * y⁻¹
  rw [hθ, hθ, hφ, hGM, hyA]

end UnitaryCore

section Orders

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms

theorem card_eq_of_compAlgEight_kd264alg {X : Type} [Group X] (e : TauCeti.ValidLieTypeIndex)
    (he : ∃ q : TauCeti.PrimePower, (e.1 = .A 1 q ∨ e.1 = .twistedA 2 q) ∧ q.card = 8)
    (hX : Nonempty (X ≃* (TauCeti.CFSGIndex.lie e).Group)) :
    Nat.card X = 504 ∨ Nat.card X = 5515776 := by
  obtain ⟨ei, hv⟩ := e
  obtain ⟨eX⟩ := hX
  obtain ⟨q, hq, hqcard⟩ := he
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hq with hA | htw
  · subst hA
    left
    have hk : Nat.card (GaloisField 2 3) = 8 := by
      rw [GaloisField.card 2 3 (by norm_num)]
      norm_num
    exact (Nat.card_congr eX.toEquiv).trans (card_catGroup_A_one_eight hk hqcard)
  · subst htw
    right
    exact (Nat.card_congr eX.toEquiv).trans (card_catGroup_twistedA_two_eight hqcard)

theorem centerQuotientHom_mem_innAutDerived_of_mulEquiv_kd264alg {J R : Type*} [Group J]
    [Group R] (e : J ≃* R) {φ : MulAut J} {α : MulAut R} (h : ∀ j, e (φ j) = α (e j))
    (hα : centerQuotientHom R α ∈ innAutDerived (R ⧸ Subgroup.center R)) :
    centerQuotientHom J φ ∈ innAutDerived (J ⧸ Subgroup.center J) := by
  let eZ : J ⧸ Subgroup.center J ≃* R ⧸ Subgroup.center R :=
    QuotientGroup.congr (Subgroup.center J) (Subgroup.center R) e (Subgroup.map_center_eq e)
  have hmk : ∀ j : J, eZ (QuotientGroup.mk j) = QuotientGroup.mk (e j) := fun j => rfl
  have h2 : MulAut.congr eZ (centerQuotientHom J φ) = centerQuotientHom R α := by
    ext x
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center R) x
    obtain ⟨j, rfl⟩ := e.surjective r
    have hx : (QuotientGroup.mk' (Subgroup.center R)) (e j) = eZ (QuotientGroup.mk j) :=
      (hmk j).symm
    rw [hx]
    change eZ ((centerQuotientHom J φ) (eZ.symm (eZ (QuotientGroup.mk j)))) = _
    rw [MulEquiv.symm_apply_apply]
    change eZ ((onCenterQuotient φ) ((QuotientGroup.mk' (Subgroup.center J)) j)) =
      (onCenterQuotient α) (eZ ((QuotientGroup.mk' (Subgroup.center J)) j))
    rw [onCenterQuotient_apply_mk]
    change eZ (QuotientGroup.mk (φ j)) = (onCenterQuotient α) (eZ (QuotientGroup.mk j))
    rw [hmk, hmk, h]
    exact (onCenterQuotient_apply_mk α (e j)).symm
  rw [← mem_innAutDerived_congr eZ, h2]
  exact hα

theorem two_pow_le_of_dvd_kd264alg {k z N : ℕ} (hz : Odd z)
    (hN : N = 504 ∨ N = 5515776) (h : 2 ^ k ∣ N * z) : k ≤ 9 ∧ (N = 504 → k ≤ 3) := by
  have h' : 2 ^ k ∣ N :=
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hz)).dvd_of_dvd_mul_right h
  rcases hN with rfl | rfl
  · have h8 : 2 ^ k ∣ 2 ^ 3 * 63 := by
      rw [show (2 : ℕ) ^ 3 * 63 = 504 by norm_num]
      exact h'
    have h3 : 2 ^ k ∣ 2 ^ 3 :=
      (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 63)).dvd_of_dvd_mul_right h8
    have hk := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h3
    exact ⟨by omega, fun _ => hk⟩
  · have h9' : 2 ^ k ∣ 2 ^ 9 * 10773 := by
      rw [show (2 : ℕ) ^ 9 * 10773 = 5515776 by norm_num]
      exact h'
    have h9 : 2 ^ k ∣ 2 ^ 9 :=
      (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 10773)).dvd_of_dvd_mul_right h9'
    exact ⟨(Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h9, fun h => by norm_num at h⟩

end Orders

section TypeAEight

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)

theorem orbitLength_eq_one_of_rankOne_kd264alg [CharP L 2]
    (hq8 : S.D.q = 8) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (h1 : compRank (componentRoots (rootCharHom a) i) = 1)
    (hn : (componentRoots (rootCharHom a) i).ncard = 2)
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hN : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 504 ∨
      Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 5515776) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 := by
  classical
  obtain ⟨K, _, _, f, -, hKcard, hfeq, -, hK4, g, hgsurj, hgker⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.RationalModel.exists_slCover_rationalComponent_rankOne S hT i h1
      hn hQS
  have hs0 := (outer_componentOrbitLength_spec S hT i).1
  have hK : Nat.card K =
      2 ^ (3 * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
    rw [hKcard, hfeq, hq8, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
  have hperf : commutator SL(2, K) = ⊤ :=
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK4).commutator_eq_top
  exact (card_centerQuotient_eq_504_of_surjective_SL_two hs0 hK g hgsurj hgker hperf hN).1

theorem orbitLength_eq_one_of_unitaryFrame_kd264alg [CharP L 2] (hq8 : S.D.q = 8)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L}
    {σf : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σf)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σf) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a' b, a' ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σf a' b) = σf (π b) (π a'))
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hN : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 504 ∨
      Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 5515776) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 := by
  classical
  obtain ⟨K, _, _, f, -, hKcard, hfeq, hring, h32, g, hgsurj, hgker⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.RationalModel.exists_suCover_rationalComponent_unitaryFrame S hT
      i hν hψ hΨ π hπ hQS
  have hs0 := (outer_componentOrbitLength_spec S hT i).1
  have hQ : ringChar L ^ f =
      2 ^ (3 * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
    rw [hfeq, hq8, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
  have hrL : ringChar L = 2 := ringChar.eq L 2
  haveI : Fact (ringChar L).Prime := ⟨hrL ▸ Nat.prime_two⟩
  haveI : CharP K (ringChar L) := hring ▸ ringChar.charP K
  obtain ⟨hqs, -⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (F := K) (p := ringChar L) (f := f) hKcard hν h32
  have hperf : commutator ↥(StatedSU ν (ringChar L ^ f) K) = ⊤ := hqs.1.commutator_eq_top
  generalize hQv : ringChar L ^ f = Q at hKcard g hgsurj hgker hperf
  have hQ2 : Q = 2 ^ (3 * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) :=
    hQv.symm.trans hQ
  subst hQ2
  exact (card_centerQuotient_eq_5515776_of_surjective_statedSU hν hs0 hKcard g hgsurj hgker hperf
    hN).2.1

theorem centerQuotientHom_mem_innAutDerived_typeA_kd264alg [CharP L 2]
    (hq8 : S.D.q = 8) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hN : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 504 ∨
      Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 5515776)
    {y : ModGL τ L} (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y)
    (hy : MulAut.conj y ∈
      CFSG.GroupActions.subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    centerQuotientHom _ (CFSG.GroupActions.subgroupStabRestrict _ ⟨MulAut.conj y, hy⟩) ∈
      innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  rcases CFSG.LocalAnalysis.GLTheoremA.RationalModel.typeA_frame_cases S Nat.prime_three hT hap h1
    i hA with ⟨hr1, hn⟩ | h | h
  · have hs1 := orbitLength_eq_one_of_rankOne_kd264alg S hq8 hT i hr1 hn hQS hN
    obtain ⟨w, hwR, hw⟩ := exists_mem_rationalComponent_conj_eq_rankOne_kd264alg S hT i hr1 hn
      hs1 (by omega) hyZ hyF
    have hres : CFSG.GroupActions.subgroupStabRestrict _ ⟨MulAut.conj y, hy⟩ =
        MulAut.conj (⟨w, hwR⟩ : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
      refine MulEquiv.ext fun r => Subtype.ext ?_
      rw [CFSG.GroupActions.subgroupStabRestrict_apply]
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hw _ r.2
    rw [hres, CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj]
    exact inner_le_innAutDerived _ ⟨_, rfl⟩
  · obtain ⟨ν, ψ, σf, π, hν, hψ, hΨ, hπ⟩ := h
    exfalso
    obtain ⟨K, _, _, f, -, hKcard, hfeq, -, g, hgsurj, hgker⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.RationalModel.exists_slCover_rationalComponent_splitFrame S hT
        i hν hψ hΨ π hπ
    have hs0 := (outer_componentOrbitLength_spec S hT i).1
    have hrL : ringChar L = 2 := ringChar.eq L 2
    have hE : Nat.card K =
        2 ^ (3 * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
      rw [hKcard, hfeq, hq8, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
    have hm2 := multiplicity_eq_two_of_compAlgEight (by omega) hs0 hE g hgsurj hgker
      (isQuasisimple_specialLinearGroup hν) hN
    omega
  · obtain ⟨ν, ψ, σf, π, hν, hψ, hΨ, hπ⟩ := h
    have hs1 := orbitLength_eq_one_of_unitaryFrame_kd264alg S hq8 hT i hν hψ hΨ π hπ hQS hN
    exact centerQuotientHom_mem_innAutDerived_unitaryFrame_kd264alg S hT i hν hψ hΨ π hπ hs1
      (by rw [hq8]; simp) hyZ hyF hy

theorem centerQuotientHom_mem_innAutDerived_of_langSetup_conj_kd264alg [CharP L 2]
    (hq8 : S.D.q = 8) {C : Type} [Group C] [Finite C] (ι : C →* ModGL τ L)
    (hι : Function.Injective ι) (hrange : ι.range = S.Γ) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hA : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
      (Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 504 ∨
        Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 5515776) →
      1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) + 1))
    {β : MulAut C} (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    {K : Subgroup C}
    (hK : IsComponentOf K (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β))
    (hN : Nat.card (↥K ⧸ Subgroup.center ↥K) = 504 ∨
      Nat.card (↥K ⧸ Subgroup.center ↥K) = 5515776)
    {φ : MulAut C} (hφ : φ ∈ CFSG.GroupActions.subgroupStabAut K) {y : ModGL τ L}
    (hφy : ∀ c, ι (φ c) = y * ι c * y⁻¹) (hyF : S.D.step y = y)
    (hyZ : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
      (Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 504 ∨
        Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 5515776) →
      MulAut.conj y ∈
        CFSG.GroupActions.subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
      y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a))) :
    centerQuotientHom ↥K (CFSG.GroupActions.subgroupStabRestrict K ⟨φ, hφ⟩) ∈
      innAutDerived (↥K ⧸ Subgroup.center ↥K) := by
  classical
  obtain ⟨i, hqs, hKR⟩ :=
    components_of_langSetup S Nat.prime_three ι hι hrange β hβ hT hap h1 hTame hK
  set R := rationalComponent S.ρ S.Γ (rootCharHom a) i with hRdef
  let eJ : ↥K ≃* ↥R := (K.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hKR)
  have heJ : ∀ k : K, (eJ k : ModGL τ L) = ι k := fun k => rfl
  have hNR : Nat.card (↥R ⧸ Subgroup.center ↥R) = 504 ∨
      Nat.card (↥R ⧸ Subgroup.center ↥R) = 5515776 := by
    have hc : Nat.card (↥K ⧸ Subgroup.center ↥K) = Nat.card (↥R ⧸ Subgroup.center ↥R) :=
      Nat.card_congr (QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥R) eJ
        (Subgroup.map_center_eq eJ)).toEquiv
    rw [← hc]
    exact hN
  have hAi := hA i hqs hNR
  have hyR : MulAut.conj y ∈ CFSG.GroupActions.subgroupStabAut R := by
    change R.map (MulAut.conj y).toMonoidHom = R
    have hcomp : (MulAut.conj y).toMonoidHom.comp ι = ι.comp φ.toMonoidHom := by
      ext c
      simp [MulAut.conj_apply, hφy]
    have hφK : K.map φ.toMonoidHom = K := hφ
    rw [← hKR, Subgroup.map_map, hcomp, ← Subgroup.map_map, hφK]
  have hcore := centerQuotientHom_mem_innAutDerived_typeA_kd264alg S hq8 hT hap h1 i hAi hqs hNR
    (hyZ i hqs hNR hyR) hyF hyR
  refine centerQuotientHom_mem_innAutDerived_of_mulEquiv_kd264alg eJ ?_ hcore
  intro k
  apply Subtype.ext
  rw [heJ, CFSG.GroupActions.subgroupStabRestrict_apply, CFSG.GroupActions.subgroupStabRestrict_apply,
    heJ, MulAut.conj_apply]
  exact hφy k

theorem centerQuotientHom_mem_innAutDerived_of_langSetup_kd264alg [CharP L 2]
    (hq8 : S.D.q = 8) {C : Type} [Group C] [Finite C] (ι : C →* ModGL τ L)
    (hι : Function.Injective ι) (hrange : ι.range = S.Γ) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hW : rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hA : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
      (Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 504 ∨
        Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 5515776) →
      1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) + 1))
    {x : C} (hx : ι x = rootDiagUnit τ a) {K : Subgroup C}
    (hK : IsComponentOf K
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)))
    (hN : Nat.card (↥K ⧸ Subgroup.center ↥K) = 504 ∨
      Nat.card (↥K ⧸ Subgroup.center ↥K) = 5515776)
    {w : C} (hxw : x * w = w * x) (hw : MulAut.conj w ∈ CFSG.GroupActions.subgroupStabAut K) :
    centerQuotientHom ↥K (CFSG.GroupActions.subgroupStabRestrict K ⟨MulAut.conj w, hw⟩) ∈
      innAutDerived (↥K ⧸ Subgroup.center ↥K) := by
  classical
  have hβ : ∀ c, ι (MulAut.conj x c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹ :=
    fun c => by rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hx]
  have hφy : ∀ c, ι (MulAut.conj w c) = ι w * ι c * (ι w)⁻¹ :=
    fun c => by rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hyΓ : ι w ∈ S.Γ := hrange ▸ ⟨w, rfl⟩
  have hyF : S.D.step (ι w) = ι w := ((Subgroup.commutator_le_self S.D.model) hyΓ).2
  have hyG : ι w ∈ adjointGroup τ L := ((Subgroup.commutator_le_self S.D.model) hyΓ).1
  have hyd : rootDiagUnit τ a * ι w * (rootDiagUnit τ a)⁻¹ = ι w := by
    rw [← hx, ← map_mul, ← map_inv, ← map_mul, hxw, mul_inv_cancel_right]
  have hyC : ι w ∈ toralCentralizer τ L a := mem_toralCentralizer.2 ⟨hyG, hyd⟩
  have hyZ : ι w ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) := by
    have h := CFSG.HardMathSupport.Timmesfeld.Steinberg.toralCentralizer_eq_toralRootGroup_of_stabilizer_le
      τ L a hW
    rw [h] at hyC
    exact hyC
  exact centerQuotientHom_mem_innAutDerived_of_langSetup_conj_kd264alg S hq8 ι hι hrange hT hap h1
    hTame hA hβ hK hN hw hφy hyF (fun _ _ _ _ => hyZ)

end TypeAEight

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
