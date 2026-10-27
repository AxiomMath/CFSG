module

public import CFSG.CharacterTheory.Semidihedral.OddLinearNormals

public noncomputable section

namespace CFSG.Wreathed.OddLinearTwoAutomorphisms

open scoped MatrixGroups
variable (F : Type*) [Field F] (V : Type*) [AddCommGroup V] [Module F V]

@[expose] def scalarHom : Fˣ →* (V ≃ₗ[F] V) where
  toFun := LinearEquiv.smulOfUnit
  map_one' := by ext v; exact one_smul F v
  map_mul' a b := by
    ext v
    exact mul_smul (a : F) (b : F) v

theorem scalarHom_apply (a : Fˣ) (v : V) : scalarHom F V a v = (a : F) • v := rfl

theorem scalarHom_central : (scalarHom F V).range ≤ Subgroup.center (V ≃ₗ[F] V) := by
  rintro g ⟨a, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro h
  ext v
  exact h.map_smul (a : F) v

theorem scalarHom_injective (hV : Module.finrank F V = 2) :
    Function.Injective (scalarHom F V) := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by rw [hV]; decide)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  intro a b hab
  apply Units.ext
  exact smul_left_injective F hv (congrArg (fun g : V ≃ₗ[F] V => g v) hab)

@[expose] def matrixEquiv (b : Module.Basis (Fin 2) F V) :
    GL (Fin 2) F ≃* (V ≃ₗ[F] V) :=
  (Matrix.GeneralLinearGroup.toLin' b).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F V)

theorem matrixEquiv_apply (b : Module.Basis (Fin 2) F V) (g : GL (Fin 2) F) (v : V) :
    matrixEquiv F V b g v =
      Fintype.linearCombination F (fun i => b i) ((g : Matrix (Fin 2) (Fin 2) F).mulVec
        (fun i => b.repr v i)) :=
  Matrix.GeneralLinearGroup.toLin'_apply b g v

theorem matrixEquiv_scalar (b : Module.Basis (Fin 2) F V) (a : Fˣ) :
    matrixEquiv F V b (Matrix.GeneralLinearGroup.scalar (Fin 2) a) = scalarHom F V a := by
  ext v
  rw [matrixEquiv_apply, Matrix.GeneralLinearGroup.coe_scalar]
  have hs : (Matrix.scalar (Fin 2) (a : F)).mulVec (fun i => b.repr v i) =
      (a : F) • (fun i => b.repr v i) := by
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal]
  rw [hs, map_smul]
  change (a : F) • _ = (a : F) • v
  congr 1
  simp [Fintype.linearCombination_apply]

theorem scalarHom_det (hV : Module.finrank F V = 2)
    (a : Fˣ) : (scalarHom F V a).det = a ^ 2 := by
  apply Units.ext
  have hs : (scalarHom F V a).toLinearMap = (a : F) • LinearMap.id := by ext; rfl
  rw [LinearEquiv.coe_det, hs, LinearMap.det_smul, hV, LinearMap.det_id, mul_one]
  rfl

theorem imageSL_id_eq_ker_det :
    CFSG.Semidihedral.OddLinearNormals.imageSL (RingHom.id F) =
      (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker := by
  rw [CFSG.Semidihedral.OddLinearNormals.imageSL]
  have he : CFSG.Semidihedral.OddLinearNormals.entrywiseSL (RingHom.id F) =
      (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F) := by
    ext g i j
    rfl
  rw [he, Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]

theorem normal_odd_matrix_scalar [Finite F] (hFodd : Odd (Nat.card F))
    (hF : 3 ≤ Nat.card F) (R : Subgroup (GL (Fin 2) F))
    (hRnormal : R.Normal) (hRodd : Odd (Nat.card R)) :
    R ≤ (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F).range := by
  let : R.Normal := hRnormal
  let : (CFSG.Semidihedral.OddLinearNormals.imageSL (RingHom.id F)).Normal := by
    rw [imageSL_id_eq_ker_det]
    infer_instance
  let B : Subgroup (GL (Fin 2) F) := ⊤
  let T : Subgroup B := R.subgroupOf B
  have hTcard : Nat.card T = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show R ≤ B from le_top)).toEquiv
  intro r hr
  have hscalar := CFSG.Semidihedral.OddLinearNormals.normal_odd_matrix_overgroup_scalar
    hFodd hF (RingHom.id F) (fun _ _ h => h) B le_top inferInstance T inferInstance
    (hTcard ▸ hRodd) ⟨r, Subgroup.mem_top _⟩ hr
  rw [← Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr hscalar

theorem normal_odd_is_scalar [Finite F] [FiniteDimensional F V]
    (hFodd : Odd (Nat.card F)) (hF : 3 ≤ Nat.card F)
    (hV : Module.finrank F V = 2) (R : Subgroup (V ≃ₗ[F] V))
    (hRnormal : R.Normal) (hRodd : Odd (Nat.card R)) :
    R ≤ (scalarHom F V).range := by
  let b := Module.finBasisOfFinrankEq F V hV
  let e := matrixEquiv F V b
  let T := R.comap e.toMonoidHom
  have hTodd : Odd (Nat.card T) :=
    hRodd.of_dvd_nat (R.card_comap_dvd_of_injective e.toMonoidHom e.injective)
  have hTscalar := normal_odd_matrix_scalar F hFodd hF T
    (hRnormal.comap e.toMonoidHom) hTodd
  intro r hr
  have hpre : e.symm r ∈ T := by
    change e (e.symm r) ∈ R
    rwa [e.apply_symm_apply]
  obtain ⟨a, ha⟩ := hTscalar hpre
  refine ⟨a, ?_⟩
  have hm := congrArg e ha
  rw [e.apply_symm_apply] at hm
  exact (matrixEquiv_scalar F V b a).symm.trans hm

variable {F V} in
theorem mem_scalarHom_range_iff {g : V ≃ₗ[F] V} :
    g ∈ (scalarHom F V).range ↔ ∃ a : Fˣ, ∀ v : V, g v = (a : F) • v := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, scalarHom_apply F V a⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, LinearEquiv.ext (fun v => (ha v).symm)⟩

theorem normal_odd_scalar_unique [Finite F] [FiniteDimensional F V]
    (hFodd : Odd (Nat.card F)) (hF : 3 ≤ Nat.card F)
    (hV : Module.finrank F V = 2) (R : Subgroup (V ≃ₗ[F] V))
    (hRnormal : R.Normal) (hRodd : Odd (Nat.card R))
    (g : V ≃ₗ[F] V) (hg : g ∈ R) :
    ∃! a : Fˣ, g = scalarHom F V a := by
  obtain ⟨a, ha⟩ := normal_odd_is_scalar F V hFodd hF hV R hRnormal hRodd hg
  refine ⟨a, ha.symm, ?_⟩
  intro c hc
  exact scalarHom_injective F V hV (hc.symm.trans ha.symm)

theorem finite_automorphisms [Finite F] [FiniteDimensional F V]
    (hV : Module.finrank F V = 2) : Finite (V ≃ₗ[F] V) :=
  Finite.of_equiv (GL (Fin 2) F)
    (matrixEquiv F V (Module.finBasisOfFinrankEq F V hV)).toEquiv

private lemma twoCardArithmetic (q : ℕ) (hq : 1 ≤ q) :
    (q ^ 2 - 1) * (q ^ 2 - q) = q * (q - 1) ^ 2 * (q + 1) := by
  have h1 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    apply Nat.sub_eq_of_eq_add
    have hs : q - 1 + 1 = q := Nat.sub_add_cancel hq
    nlinarith [hs]
  have h2 : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one, ← pow_two]
  rw [h1, h2]
  ring

theorem card_matrix_two [Finite F] :
    Nat.card (GL (Fin 2) F) = Nat.card F * (Nat.card F - 1) ^ 2 * (Nat.card F + 1) := by
  let : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_GL_field, Fin.prod_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  rw [← Nat.card_eq_fintype_card]
  exact twoCardArithmetic (Nat.card F) (by have := Nat.card_pos (α := F); omega)

theorem card_automorphisms [Finite F] [FiniteDimensional F V]
    (hV : Module.finrank F V = 2) :
    Nat.card (V ≃ₗ[F] V) = Nat.card F * (Nat.card F - 1) ^ 2 * (Nat.card F + 1) := by
  rw [← Nat.card_congr (matrixEquiv F V (Module.finBasisOfFinrankEq F V hV)).toEquiv]
  exact card_matrix_two F

theorem scalarImage_isCyclic [Finite F] (A : Subgroup Fˣ) :
    IsCyclic (A.map (scalarHom F V)) := by
  let f : A →* A.map (scalarHom F V) :=
    ((scalarHom F V).comp A.subtype).codRestrict _ (fun a => ⟨a, a.property, rfl⟩)
  apply isCyclic_of_surjective f
  rintro ⟨g, a, ha, rfl⟩
  exact ⟨⟨a, ha⟩, rfl⟩

theorem original_two_dimensional_linear_automorphisms_scalar_normal_subgroups_and_order
    [Finite F] [FiniteDimensional F V] (hFodd : Odd (Nat.card F))
    (hF : 3 ≤ Nat.card F) (hV : Module.finrank F V = 2) :
    Function.Injective (scalarHom F V) ∧
      (scalarHom F V).range ≤ Subgroup.center (V ≃ₗ[F] V) ∧
      (∀ a : Fˣ, ∀ v : V, scalarHom F V a v = (a : F) • v) ∧
      (∀ a : Fˣ, (scalarHom F V a).det = a ^ 2) ∧
      (∀ R : Subgroup (V ≃ₗ[F] V), R.Normal → Odd (Nat.card R) →
        R ≤ (scalarHom F V).range) ∧
      Nat.card (V ≃ₗ[F] V) = Nat.card F * (Nat.card F - 1) ^ 2 * (Nat.card F + 1) :=
  ⟨scalarHom_injective F V hV, scalarHom_central F V,
    scalarHom_apply F V, scalarHom_det F V hV,
    normal_odd_is_scalar F V hFodd hF hV, card_automorphisms F V hV⟩
end CFSG.Wreathed.OddLinearTwoAutomorphisms
