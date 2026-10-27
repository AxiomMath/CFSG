module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeDataInputs
import CFSG.LinearAlgebra.SL2CoprimeOrder

public noncomputable section

namespace CFSG.Semidihedral.AllPrime

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups
open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

section Matrices

variable {F : Type} [Field F]

private theorem trace_eq_zero_of_anticomm (h2 : (2 : F) ≠ 0) {W : Matrix (Fin 2) (Fin 2) F}
    {g : GL (Fin 2) F}
    (h : W * (g : Matrix (Fin 2) (Fin 2) F) = -((g : Matrix (Fin 2) (Fin 2) F) * W)) :
    Matrix.trace W = 0 := by
  have hW : W = -((g : Matrix (Fin 2) (Fin 2) F) * W *
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by
    have h' := congrArg (· * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one,
      Matrix.neg_mul] at h'
    exact h'
  have htr : Matrix.trace ((g : Matrix (Fin 2) (Fin 2) F) * W *
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) = Matrix.trace W := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  have h3 : Matrix.trace W = -Matrix.trace W := by
    conv_lhs => rw [hW]
    rw [Matrix.trace_neg, htr]
  have h4 : (2 : F) * Matrix.trace W = 0 := by linear_combination h3
  exact (mul_eq_zero.mp h4).resolve_left h2

private theorem sl_mul_self_eq_neg_one_of_anticomm (h2 : (2 : F) ≠ 0)
    {W : Matrix.SpecialLinearGroup (Fin 2) F} {g : GL (Fin 2) F}
    (h : (W : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
      -((g : Matrix (Fin 2) (Fin 2) F) * W)) :
    W * W = -1 := by
  have htr := trace_eq_zero_of_anticomm h2 h
  have hcay :=
    CFSG.LinearAlgebra.mul_self_eq_trace_smul_sub_one (W : Matrix (Fin 2) (Fin 2) F) W.2
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, hcay, htr, zero_smul, zero_sub]
  rfl

private theorem exists_mul_eq_mul_J (h2 : (2 : F) ≠ 0) (g : GL (Fin 2) F)
    (htr : Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) = 0) :
    ∃ P : GL (Fin 2) F, g * P = P * MatrixCoverData.J F (Matrix.GeneralLinearGroup.det g) := by
  obtain ⟨a, b, c, d, hg⟩ : ∃ a b c d : F, (g : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have had : d = -a := by
    rw [Matrix.trace_fin_two, hg] at htr
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at htr
    linear_combination htr
  subst had
  have hdet : ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = -a * a - b * c := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hg, Matrix.det_fin_two_of]
    ring
  have hdet0 : -a * a - b * c ≠ 0 := by
    rw [← hdet]; exact Units.ne_zero _
  have key : ∀ P : Matrix (Fin 2) (Fin 2) F, (hP : P.det ≠ 0) →
      (g : Matrix (Fin 2) (Fin 2) F) * P = P * !![0, -(-a * a - b * c); 1, 0] →
      ∃ P : GL (Fin 2) F, g * P = P * MatrixCoverData.J F (Matrix.GeneralLinearGroup.det g) := by
    intro P hP h
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero P hP, Units.ext ?_⟩
    rw [Units.val_mul, Units.val_mul, MatrixCoverData.J_matrix, hdet]
    exact h
  by_cases hc : c = 0
  · subst hc
    by_cases hb : b = 0
    · subst hb
      have ha : a ≠ 0 := by
        intro ha; apply hdet0; rw [ha]; ring
      apply key !![1, a; 1, -a]
      · rw [Matrix.det_fin_two_of]
        intro h
        apply ha
        have h' : (2 : F) * a = 0 := by linear_combination -h
        exact (mul_eq_zero.mp h').resolve_left h2
      · rw [hg]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · apply key !![0, b; 1, -a]
      · rw [Matrix.det_fin_two_of]; simpa using hb
      · rw [hg]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
        ring
  · apply key !![1, a; 0, c]
    · rw [Matrix.det_fin_two_of]; simpa using hc
    · rw [hg]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem centralizer_SL_isCyclic_card [Finite F] (h2 : (2 : F) ≠ 0) (g : GL (Fin 2) F)
    (htr : Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) = 0) :
    IsCyclic ((Subgroup.centralizer {g}).comap
        (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F)) ∧
      (Nat.card ((Subgroup.centralizer {g}).comap
        (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F)) =
          Nat.card F + 1 ∨
        Nat.card ((Subgroup.centralizer {g}).comap
        (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F)) =
          Nat.card F - 1) := by
  set Cg := (Subgroup.centralizer {g}).comap
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F)
    with hCg
  obtain ⟨P, hP⟩ := exists_mul_eq_mul_J h2 g htr
  set a := Matrix.GeneralLinearGroup.det g with ha
  set φ := MatrixCoverData.slConjugation F P⁻¹ with hφ
  have hJ : MatrixCoverData.J F a = P⁻¹ * g * P := by
    rw [mul_assoc, hP, ← mul_assoc, inv_mul_cancel, one_mul]
  have hmem : ∀ X : Matrix.SpecialLinearGroup (Fin 2) F,
      φ X ∈ MatrixTorus.Torus F a ↔ X ∈ Cg := by
    intro X
    change Matrix.SpecialLinearGroup.toGL (φ X) ∈ Subgroup.centralizer {MatrixCoverData.J F a} ↔
      Matrix.SpecialLinearGroup.toGL X ∈ Subgroup.centralizer {g}
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, hφ,
      MatrixCoverData.slConjugation_toGL, inv_inv, hJ]
    constructor
    · intro h
      have h' : P * (P⁻¹ * Matrix.SpecialLinearGroup.toGL X * P * (P⁻¹ * g * P)) * P⁻¹ =
          P * (P⁻¹ * g * P * (P⁻¹ * Matrix.SpecialLinearGroup.toGL X * P)) * P⁻¹ := by rw [h]
      simpa only [mul_assoc, mul_inv_cancel, inv_mul_cancel_left, mul_inv_cancel_left,
        mul_one] using h'
    · intro h
      calc P⁻¹ * Matrix.SpecialLinearGroup.toGL X * P * (P⁻¹ * g * P)
          = P⁻¹ * (Matrix.SpecialLinearGroup.toGL X * g) * P := by group
        _ = P⁻¹ * (g * Matrix.SpecialLinearGroup.toGL X) * P := by rw [h]
        _ = P⁻¹ * g * P * (P⁻¹ * Matrix.SpecialLinearGroup.toGL X * P) := by group
  have hmap : Cg.map φ.toMonoidHom = MatrixTorus.Torus F a := by
    ext Y
    constructor
    · rintro ⟨X, hX, rfl⟩
      exact (hmem X).mpr hX
    · intro hY
      refine ⟨φ.symm Y, (hmem _).mp ?_, φ.apply_symm_apply Y⟩
      rw [MulEquiv.apply_symm_apply]
      exact hY
  let e : Cg ≃* MatrixTorus.Torus F a := (φ.subgroupMap Cg).trans (MulEquiv.subgroupCongr hmap)
  refine ⟨?_, ?_⟩
  · rw [e.isCyclic]
    by_cases hs : IsSquare (-(a : F))
    · exact MatrixTorus.split_torus_cyclic F a h2 hs
    · exact MatrixTorus.nonsplit_torus_cyclic F a hs
  · rw [Nat.card_congr e.toEquiv]
    by_cases hs : IsSquare (-(a : F))
    · exact Or.inr (MatrixTorus.split_torus_card F a h2 hs)
    · exact Or.inl (MatrixTorus.nonsplit_torus_card F a hs)

end Matrices

private theorem eq_of_comp_eq_of_perfect_II42 {Y E Q : Type*} [Group Y] [Group E] [Group Q]
    [Group.IsPerfect Y] {π : E →* Q} (hcen : π.ker ≤ Subgroup.center E)
    {β₁ β₂ : Y →* E} (h : ∀ y, π (β₁ y) = π (β₂ y)) : β₁ = β₂ := by
  have hmem : ∀ x, β₁ x * (β₂ x)⁻¹ ∈ Subgroup.center E := fun x => hcen (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel])
  let γ : Y →* Subgroup.center E :=
    { toFun := fun x => ⟨β₁ x * (β₂ x)⁻¹, hmem x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        have hc := Subgroup.mem_center_iff.1 (hmem y)
        change β₁ (x * y) * (β₂ (x * y))⁻¹ = β₁ x * (β₂ x)⁻¹ * (β₁ y * (β₂ y)⁻¹)
        rw [map_mul, map_mul, mul_inv_rev]
        calc β₁ x * β₁ y * ((β₂ y)⁻¹ * (β₂ x)⁻¹)
            = β₁ x * ((β₁ y * (β₂ y)⁻¹) * (β₂ x)⁻¹) := by group
          _ = β₁ x * ((β₂ x)⁻¹ * (β₁ y * (β₂ y)⁻¹)) := by rw [← hc]
          _ = β₁ x * (β₂ x)⁻¹ * (β₁ y * (β₂ y)⁻¹) := by group) }
  have hγ : ∀ x, γ x = 1 := by
    intro x
    have hx : x ∈ commutator Y := by
      rw [Group.IsPerfect.commutator_eq_top]
      trivial
    exact Abelianization.commutator_subset_ker γ hx
  ext x
  have := congrArg Subtype.val (hγ x)
  simp only [γ, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one] at this
  exact mul_inv_eq_one.1 this

section Layer

variable {G : Type} [Group G]

private theorem exists_layer_conj_matrix (t : G) {F : Type} [Field F] [Finite F]
    (hF4 : 4 ≤ Nat.card F) (A : Subgroup (F ≃+* F)) (hAodd : Odd (Nat.card A))
    (rho : Gamma t →* coordinateE F) (hrange : rho.range = OddFieldLift.Gamma F A)
    (eta : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F)
    (heta : ∀ x : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t),
      (rho (barKappa t x)).val =
        coordinatePSLAction F (ProjectiveSL2Cover.nativeQuotient F (eta x)))
    (s : C t) (hs2 : s ^ 2 = 1) :
    ∃ g : GL (Fin 2) F, coordinateGLAction F g = (rho (kappa t s)).val ∧
      ∀ (y : H t) (hy : y ∈ (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
        (hy' : nu t s * y * (nu t s)⁻¹ ∈
          (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)),
        Matrix.SpecialLinearGroup.toGL (eta ⟨nu t s * y * (nu t s)⁻¹, hy'⟩) =
          g * Matrix.SpecialLinearGroup.toGL (eta ⟨y, hy⟩) * g⁻¹ := by
  classical
  let Y := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
  have := SemilinearLayerModel.generalizedFitting_normal (Gamma t)
  have hYn : Y.Normal := Subgroup.Normal.comap inferInstance _
  have hF4' : ∃ u : Finset F, u.card = 4 := by
    have := Fintype.ofFinite F
    obtain ⟨u, -, hu⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hF4)
    exact ⟨u, hu⟩
  have := CFSG.LinearGroups.special_linear_dimension_two_perfect hF4'
  have : Group.IsPerfect Y :=
    Group.IsPerfect.ofSurjective (f := eta.symm.toMonoidHom) eta.symm.surjective
  set gs : OddFieldLift.Gamma F A := ⟨rho (kappa t s), hrange ▸ ⟨kappa t s, rfl⟩⟩ with hgs
  have hgs2 : gs ^ 2 = 1 := by
    apply Subtype.ext
    change rho (kappa t s) ^ 2 = 1
    rw [← map_pow, ← map_pow, hs2, map_one, map_one]
  have hD : (rho (kappa t s) : Equiv.Perm (Omega F)) ∈ coordinateD F :=
    MatrixCover.gamma_involution_mem_linear F A hAodd gs hgs2
  obtain ⟨g, hg⟩ := Principal.exists_coordinateGLAction_eq hD
  let cY : Y →* Y := MonoidHom.codRestrict ((MulAut.conj (nu t s)).toMonoidHom.comp Y.subtype) Y
    (fun y => hYn.conj_mem _ y.2 _)
  let β₁ : Y →* GL (Fin 2) F := (Matrix.SpecialLinearGroup.toGL.comp eta.toMonoidHom).comp cY
  let β₂ : Y →* GL (Fin 2) F :=
    (MulAut.conj g).toMonoidHom.comp (Matrix.SpecialLinearGroup.toGL.comp eta.toMonoidHom)
  have hcen : (coordinateGLAction F).ker ≤ Subgroup.center (GL (Fin 2) F) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [← Matrix.ProjGenLinGroup.mk_eq_one]
    apply coordinatePGLAction_injective F
    rw [map_one]
    exact hx
  have hπ : ∀ y, coordinateGLAction F (β₁ y) = coordinateGLAction F (β₂ y) := by
    intro y
    have h1 : coordinateGLAction F (Matrix.SpecialLinearGroup.toGL (eta (cY y))) =
        (rho (barKappa t (cY y : H t))).val := by
      rw [Principal.coordinateGLAction_toGL]
      exact (heta (cY y)).symm
    have h2 : coordinateGLAction F (Matrix.SpecialLinearGroup.toGL (eta y)) =
        (rho (barKappa t (y : H t))).val := by
      rw [Principal.coordinateGLAction_toGL]
      exact (heta y).symm
    change coordinateGLAction F (Matrix.SpecialLinearGroup.toGL (eta (cY y))) =
      coordinateGLAction F (g * Matrix.SpecialLinearGroup.toGL (eta y) * g⁻¹)
    rw [map_mul, map_mul, map_inv, hg, h1, h2]
    change (rho (barKappa t (nu t s * (y : H t) * (nu t s)⁻¹))).val = _
    rw [map_mul, map_mul, map_inv, barKappa_nu, map_mul, map_mul, map_inv]
    rfl
  have hβ := eq_of_comp_eq_of_perfect_II42 hcen hπ
  refine ⟨g, hg, fun y hy hy' => ?_⟩
  exact DFunLike.congr_fun hβ ⟨y, hy⟩

end Layer

section Frontier

private theorem frontier_layer_matrix_data {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (Λ : (frontierSetting S fS t p f).L₀ →* Matrix.SpecialLinearGroup (Fin 2) F)
      (g : GL (Fin 2) F),
      Nat.card F = p ^ f ∧
      (∀ x, Λ x = 1 ↔ (x : G) ∈ (frontierSetting S fS t p f).ON) ∧
      (∀ x : (frontierSetting S fS t p f).L₀, (x : G) * (fS (s n) : G) = (fS (s n) : G) * x →
        Matrix.SpecialLinearGroup.toGL (Λ x) * g = g * Matrix.SpecialLinearGroup.toGL (Λ x)) ∧
      ∀ w : (frontierSetting S fS t p f).L₀,
        (w : G) * (fS (s n) : G) * (w : G)⁻¹ = t * (fS (s n) : G) →
          (Λ w : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
            -((g : Matrix (Fin 2) (Fin 2) F) * (Λ w : Matrix (Fin 2) (Fin 2) F)) := by
  obtain ⟨-, ht2, -, hsC, hs2, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hG := CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨F, hfield, hfinite, A, rho, data⟩ :=
    actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨eta, heta1, heta, -⟩ := data.compatible_layer
  have hF4 : 4 ≤ Nat.card F := by rw [data.field_card]; omega
  have hodd : Odd (Nat.card F) := by rw [data.field_card]; exact hpodd.pow
  have h2 : (2 : F) ≠ 0 := OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have := SemilinearLayerModel.generalizedFitting_normal (Gamma t)
  have hYn : ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).Normal :=
    Subgroup.Normal.comap inferInstance _
  set s' : C t := ⟨(fS (s n) : G), hsC⟩ with hs'
  have hs'2 : s' ^ 2 = 1 := by
    apply Subtype.ext
    change (fS (s n) : G) ^ 2 = 1
    have := pow_orderOf_eq_one (fS (s n) : G)
    rwa [hs2] at this
  obtain ⟨g, hg, hconj⟩ := exists_layer_conj_matrix t hF4 A data.field_group_odd rho
    data.full_image eta heta s' hs'2
  have hmemY : ∀ x : (frontierSetting S fS t p f).L₀,
      nu t (⟨(x : G), Subgroup.map_subtype_le _ x.2⟩ : C t) ∈
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := fun x => by
    have h : (⟨(x : G), Subgroup.map_subtype_le _ x.2⟩ : C t) ∈ localLayerPreimage t := by
      obtain ⟨y, hy, hyx⟩ := x.2
      have : y = ⟨(x : G), Subgroup.map_subtype_le _ x.2⟩ := Subtype.ext hyx
      rw [← this]
      exact hy
    exact h
  have hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) F) ≠ 1 := by
    intro h
    have h00 := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) F =>
      (X : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h00
    apply h2
    linear_combination -h00
  refine ⟨F, hfield, hfinite, layerQuotientHom t eta, g, data.field_card, ?_, ?_, ?_⟩
  · intro x
    change x ∈ (layerQuotientHom t eta).ker ↔ _
    rw [layerQuotientHom_ker, frontierSetting_ON S fS t p f]
    rfl
  · intro x hxs
    set x' : C t := ⟨(x : G), Subgroup.map_subtype_le _ x.2⟩ with hx'
    have hy := hmemY x
    have hsx : s' * x' * s'⁻¹ = x' := by
      apply Subtype.ext
      change (fS (s n) : G) * x * (fS (s n) : G)⁻¹ = x
      rw [← hxs, mul_inv_cancel_right]
    have hy' : nu t s' * nu t x' * (nu t s')⁻¹ ∈
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := hYn.conj_mem _ hy _
    have h := hconj (nu t x') hy hy'
    have heq : (⟨nu t s' * nu t x' * (nu t s')⁻¹, hy'⟩ :
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) = ⟨nu t x', hy⟩ := by
      apply Subtype.ext
      change nu t s' * nu t x' * (nu t s')⁻¹ = nu t x'
      rw [← map_inv, ← map_mul, ← map_mul, hsx]
    rw [heq] at h
    change Matrix.SpecialLinearGroup.toGL (eta ⟨nu t x', hy⟩) * g =
      g * Matrix.SpecialLinearGroup.toGL (eta ⟨nu t x', hy⟩)
    calc Matrix.SpecialLinearGroup.toGL (eta ⟨nu t x', hy⟩) * g
        = g * Matrix.SpecialLinearGroup.toGL (eta ⟨nu t x', hy⟩) * g⁻¹ * g := by rw [← h]
      _ = g * Matrix.SpecialLinearGroup.toGL (eta ⟨nu t x', hy⟩) := by group
  · intro w hws
    set w' : C t := ⟨(w : G), Subgroup.map_subtype_le _ w.2⟩ with hw'
    have hy := hmemY w
    set W := Matrix.SpecialLinearGroup.toGL (eta ⟨nu t w', hy⟩) with hW
    have hws' : w' * s' * w'⁻¹ * s'⁻¹ = tInC t := by
      apply Subtype.ext
      change (w : G) * (fS (s n) : G) * (w : G)⁻¹ * (fS (s n) : G)⁻¹ = t
      rw [hws, mul_inv_cancel_right]
    have hWact : coordinateGLAction F W = (rho (kappa t w')).val := by
      rw [hW, Principal.coordinateGLAction_toGL]
      exact (heta ⟨nu t w', hy⟩).symm
    have hκt : kappa t (tInC t) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    have hker : W * g * W⁻¹ * g⁻¹ ∈ (coordinateGLAction F).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hWact, hg]
      have e : (rho (kappa t w')).val * (rho (kappa t s')).val * ((rho (kappa t w')).val)⁻¹ *
          ((rho (kappa t s')).val)⁻¹ = (rho (kappa t (w' * s' * w'⁻¹ * s'⁻¹))).val := by
        simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [e, hws', hκt, map_one]
      rfl
    have hcen : (coordinateGLAction F).ker ≤ Subgroup.center (GL (Fin 2) F) := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      rw [← Matrix.ProjGenLinGroup.mk_eq_one]
      apply coordinatePGLAction_injective F
      rw [map_one]
      exact hx
    have hcW := hcen hker
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcW
    obtain ⟨c, hc⟩ := hcW
    have hc2 : c ^ 2 = 1 := by
      have hdet := congrArg Matrix.GeneralLinearGroup.det hc
      rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_mul, map_mul, map_mul,
        map_inv, map_inv] at hdet
      rw [hdet]
      simp only [mul_inv_cancel_comm]
      rw [mul_inv_cancel]
    have hc' : c = 1 ∨ c = -1 := by
      have h0 : ((c : F) - 1) * ((c : F) + 1) = 0 := by
        have := congrArg Units.val hc2
        push_cast at this
        linear_combination this
      rcases mul_eq_zero.mp h0 with h | h
      · exact Or.inl (Units.ext (by push_cast; linear_combination h))
      · exact Or.inr (Units.ext (by push_cast; linear_combination h))
    rcases hc' with rfl | rfl
    ·
      exfalso
      rw [map_one] at hc
      have hWg : g * W * g⁻¹ = W := by
        have h1 : W * g = g * W := by
          calc W * g = (W * g * W⁻¹ * g⁻¹) * g * W := by group
            _ = g * W := by rw [← hc, one_mul]
        rw [← h1, mul_inv_cancel_right]
      have hy' : nu t s' * nu t w' * (nu t s')⁻¹ ∈
          (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := hYn.conj_mem _ hy _
      have h := hconj (nu t w') hy hy'
      rw [← hW, hWg, hW] at h
      have h' := eta.injective (Matrix.SpecialLinearGroup.toGL_injective h)
      have h'' : nu t (s' * w' * s'⁻¹ * w'⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        have := congrArg Subtype.val h'
        change nu t s' * nu t w' * (nu t s')⁻¹ = nu t w' at this
        rw [this, mul_inv_cancel]
      have hsw : s' * w' * s'⁻¹ * w'⁻¹ = (tInC t)⁻¹ := by
        rw [← hws']
        group
      rw [hsw, map_inv, inv_eq_one] at h''
      apply hneg
      rw [← heta1]
      have : (⟨nu t (tInC t), QuaternionDoubleCoverUniqueness.central_involution_mem_preimage
          (nu t (tInC t)) (barKappa t) (barKappa_kernel t)
            (CFSG.generalizedFitting (Gamma t))⟩ :
          (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) = 1 := Subtype.ext h''
      rw [this, map_one]
    ·
      have h1 : W * g = Matrix.GeneralLinearGroup.scalar (Fin 2) (-1) * g * W := by
        rw [hc]
        group
      have h1' := congrArg Units.val h1
      rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at h1'
      change (eta ⟨nu t w', hy⟩ : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
        -((g : Matrix (Fin 2) (Fin 2) F) * (eta ⟨nu t w', hy⟩ : Matrix (Fin 2) (Fin 2) F))
      have e : (Matrix.scalar (Fin 2) (((-1 : Fˣ) : F))) = -1 := by
        rw [Units.val_neg, Units.val_one, map_neg, map_one]
      rw [e, Matrix.neg_mul, Matrix.one_mul, Matrix.neg_mul] at h1'
      exact h1'

private theorem sd_quarter_conj_s_II42 (n : ℕ) (hn : 4 ≤ n) :
    r n ^ 2 ^ (n - 3) * s n * (r n ^ 2 ^ (n - 3))⁻¹ = z n * s n := by
  have h1 := sd_s_conj_quarter hn
  have hv2 : r n ^ 2 ^ (n - 3) * r n ^ 2 ^ (n - 3) = z n := by
    rw [← pow_add, z, half, ← two_mul, ← pow_succ', show n - 3 + 1 = n - 2 by omega]
  calc r n ^ 2 ^ (n - 3) * s n * (r n ^ 2 ^ (n - 3))⁻¹
      = r n ^ 2 ^ (n - 3) * (s n * r n ^ 2 ^ (n - 3) * (s n)⁻¹)⁻¹ * s n := by group
    _ = r n ^ 2 ^ (n - 3) * r n ^ 2 ^ (n - 3) * s n := by rw [h1, inv_inv]
    _ = z n * s n := by rw [hv2]

private theorem frontier_quarter_data {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∃ v ∈ (frontierSetting S fS t p f).D, v ∈ (frontierSetting S fS t p f).L₀ ∧
      v * (fS (s n) : G) * v⁻¹ = t * (fS (s n) : G) ∧
      (∀ c ∈ (frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).L₀,
        v * c * v⁻¹ * c ∈ (frontierSetting S fS t p f).ON) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F)
        (Λ : (frontierSetting S fS t p f).L₀ →* Matrix.SpecialLinearGroup (Fin 2) F)
        (g : GL (Fin 2) F),
        Nat.card F = p ^ f ∧ Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) = 0 ∧
        (∀ x, Λ x = 1 ↔ (x : G) ∈ (frontierSetting S fS t p f).ON) ∧
        ∀ x : (frontierSetting S fS t p f).L₀, (x : G) ∈ (frontierSetting S fS t p f).C →
          Matrix.SpecialLinearGroup.toGL (Λ x) ∈ Subgroup.centralizer {g} := by
  obtain ⟨hz, ht2, -, -, -, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hG := CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨F, hfield, hfinite, Λ, g, hcard, hker, hcomm, hanti⟩ :=
    frontier_layer_matrix_data hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
      hmodel
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact hpodd.pow
  have h2 : (2 : F) ≠ 0 := OddFieldSL2.two_ne_zero_of_odd_card F hodd
  set v : G := FocalFusion.ambientHom n (S : Subgroup G) fS (r n ^ 2 ^ (n - 3)) with hv
  have := sdFourSubgroup_isKleinFour hn
  have hvD : v ∈ (frontierSetting S fS t p f).D := by
    rw [frontierSetting_D hn S fS t ht p f]
    exact Subgroup.mem_map_of_mem _ (sd_kleinFour_facts hn (sdFourSubgroup n)).2.2.1
  have hvC : v ∈ C t := frontier_S_le_C hn S fS t ht p f (ambientHom_mem _ fS _)
  have hvL : v ∈ (frontierSetting S fS t p f).L₀ := by
    obtain ⟨F', hfield', hfinite', A', rho', data'⟩ :=
      actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf
        hmodel
    have hx4 : orderOf (⟨v, hvC⟩ : C t) = 4 := by
      rw [Subgroup.orderOf_mk, hv, orderOf_ambientHom, orderOf_sdV hn]
    exact ⟨_, actual_order_four_image_mem_layer n hn S fS hG t ht2 F' A' p f rho' data' _ hx4,
      rfl⟩
  have hvs : v * (fS (s n) : G) * v⁻¹ = t * (fS (s n) : G) := by
    have hιz : FocalFusion.ambientHom n (S : Subgroup G) fS (z n) = t := hz
    have hιs : FocalFusion.ambientHom n (S : Subgroup G) fS (s n) = (fS (s n) : G) := rfl
    rw [hv, ← hιz, ← hιs, ← map_inv, ← map_mul, ← map_mul, sd_quarter_conj_s_II42 n hn, map_mul]
  have hD := hanti ⟨v, hvL⟩ hvs
  have hD2 := sl_mul_self_eq_neg_one_of_anticomm h2 hD
  have htr : Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) = 0 := by
    apply trace_eq_zero_of_anticomm h2 (g := Matrix.SpecialLinearGroup.toGL (Λ ⟨v, hvL⟩))
    change (g : Matrix (Fin 2) (Fin 2) F) * (Λ ⟨v, hvL⟩ : Matrix (Fin 2) (Fin 2) F) =
      -((Λ ⟨v, hvL⟩ : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F))
    rw [hD, neg_neg]
  have hsT : (fS (s n) : G) ∈ (frontierSetting S fS t p f).T :=
    (frontierSetting S fS t p f).x₂_mem_T
  refine ⟨v, hvD, hvL, hvs, ?_, F, hfield, hfinite, Λ, g, hcard, htr, hker, ?_⟩
  ·
    intro c hc
    have hcs : c * (fS (s n) : G) = (fS (s n) : G) * c :=
      ((Subgroup.mem_centralizer_iff.mp hc.1) _ hsT).symm
    set w : (frontierSetting S fS t p f).L₀ := ⟨v, hvL⟩ * (⟨c, hc.2⟩)⁻¹ with hw
    have hws : (w : G) * (fS (s n) : G) * (w : G)⁻¹ = t * (fS (s n) : G) := by
      rw [hw, Subgroup.coe_mul, Subgroup.coe_inv]
      calc v * c⁻¹ * (fS (s n) : G) * (v * c⁻¹)⁻¹
          = v * (c⁻¹ * ((fS (s n) : G) * c)) * v⁻¹ := by group
        _ = v * (c⁻¹ * (c * (fS (s n) : G))) * v⁻¹ := by rw [hcs]
        _ = v * (fS (s n) : G) * v⁻¹ := by group
        _ = t * (fS (s n) : G) := hvs
    have hW2 := sl_mul_self_eq_neg_one_of_anticomm h2 (hanti w hws)
    set Dm := Λ ⟨v, hvL⟩ with hDm
    set X := Λ ⟨c, hc.2⟩ with hX
    have hΛw : Λ w = Dm * X⁻¹ := by rw [hw, map_mul, map_inv]
    rw [hΛw] at hW2
    have h1 : X⁻¹ * Dm * X⁻¹ = Dm := by
      have h := hW2.trans hD2.symm
      have h' : Dm * (X⁻¹ * Dm * X⁻¹) = Dm * Dm := by
        rw [← h]
        group
      exact mul_left_cancel h'
    have h1' : Dm * X = X⁻¹ * Dm := by
      calc Dm * X = X⁻¹ * (X * (X⁻¹ * Dm * X⁻¹) * X) := by rw [h1]; group
        _ = X⁻¹ * Dm := by group
    have h3 : Λ (⟨v, hvL⟩ * ⟨c, hc.2⟩ * (⟨v, hvL⟩)⁻¹ * ⟨c, hc.2⟩) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, ← hDm, ← hX]
      calc Dm * X * Dm⁻¹ * X = X⁻¹ * Dm * Dm⁻¹ * X := by rw [h1']
        _ = 1 := by group
    exact (hker _).mp h3
  ·
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm x ((Subgroup.mem_centralizer_iff.mp hx) _ hsT).symm

private theorem frontier_oddCore_image {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (Cg : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
      (φ : (oddCoreIn (frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).L₀ :
        Subgroup G) →* Cg),
      IsCyclic Cg ∧ ¬ p ∣ Nat.card Cg ∧
        ∀ k, φ k = 1 ↔ (k : G) ∈ (frontierSetting S fS t p f).ON := by
  obtain ⟨-, -, -, -, -, F, hfield, hfinite, Λ, g, hcard, htr, hker, hcent⟩ :=
    frontier_quarter_data hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact hpodd.pow
  have h2 : (2 : F) ≠ 0 := OddFieldSL2.two_ne_zero_of_odd_card F hodd
  obtain ⟨hcyc, hcardCg⟩ := centralizer_SL_isCyclic_card h2 g htr
  have hKL : oddCoreIn (frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).L₀ ≤
      (frontierSetting S fS t p f).L₀ := inf_le_right
  refine ⟨F, hfield, hfinite, (Subgroup.centralizer {g}).comap
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F),
    (Λ.comp (Subgroup.inclusion hKL)).codRestrict _
      (fun k => hcent _ (oddCoreIn_le _ k.2.1)), hcyc, ?_, fun k => ?_⟩
  · have hpf : p ∣ p ^ f := dvd_pow_self p (by omega)
    have hpos : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
    rcases hcardCg with h | h <;> rw [h, hcard] <;> intro hdvd
    · exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hpf).mp hdvd))
    · have h' : p ∣ p ^ f - 1 + 1 := by rw [Nat.sub_add_cancel hpos]; exact hpf
      exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hdvd).mp h'))
  · constructor
    · intro h
      exact (hker _).mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((hker _).mpr h)

theorem frontier_II42i {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∃ d ∈ (frontierSetting S fS t p f).D, d ∈ (frontierSetting S fS t p f).L₀ ∧
      ∀ c ∈ (frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).L₀,
        Odd (orderOf c) → d * c * d⁻¹ * c ∈ (frontierSetting S fS t p f).ON := by
  obtain ⟨v, hvD, hvL, -, hinv, -⟩ :=
    frontier_quarter_data hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  exact ⟨v, hvD, hvL, fun c hc _ => hinv c hc⟩

theorem frontier_V3_cyclic {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∃ g ∈ (frontierSetting S fS t p f).N,
      oddCoreIn (frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).L₀ ≤
        Subgroup.zpowers g ⊔ (frontierSetting S fS t p f).ON := by
  obtain ⟨F, hfield, hfinite, Cg, φ, hcyc, -, hker⟩ :=
    frontier_oddCore_image hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  have := hcyc
  obtain ⟨⟨γ, k₀, rfl⟩, hγ⟩ := IsCyclic.exists_generator (α := φ.range)
  refine ⟨(k₀ : G), (frontierSetting S fS t p f).C_le_N (oddCoreIn_le _ k₀.2.1), ?_⟩
  intro k hk
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hγ ⟨φ ⟨k, hk⟩, ⟨k, hk⟩, rfl⟩)
  have h1 : φ (k₀ ^ m) = φ ⟨k, hk⟩ := by
    have := congrArg Subtype.val hm
    rw [map_zpow]
    simpa using this
  have h2 : φ ((k₀ ^ m)⁻¹ * ⟨k, hk⟩) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
  have h3 := (hker _).mp h2
  have e : k = (k₀ : G) ^ m * ((((k₀ ^ m)⁻¹ * ⟨k, hk⟩ : (oddCoreIn
      (frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).L₀ : Subgroup G))) : G) := by
    simp
  rw [e]
  exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers _ _) h3

theorem frontier_V3_order {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ¬ (frontierSetting S fS t p f).p ∣ (frontierSetting S fS t p f).ON.relIndex
      (oddCoreIn (frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).L₀) := by
  obtain ⟨F, hfield, hfinite, Cg, φ, -, hpCg, hker⟩ :=
    frontier_oddCore_image hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  have hkerφ : φ.ker = (frontierSetting S fS t p f).ON.subgroupOf
      (oddCoreIn (frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).L₀) := by
    ext k
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  rw [Subgroup.relIndex, ← hkerφ, Subgroup.index_ker]
  intro h
  exact hpCg (h.trans (Subgroup.card_subgroup_dvd_card _))

theorem frontier_V3_centralized {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (_hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (_hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (_hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ c ∈ (frontierSetting S fS t p f).D ⊓
        Subgroup.centralizer ((frontierSetting S fS t p f).T : Set G),
      ∀ k ∈ oddCoreIn (frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).L₀,
        c * k * c⁻¹ * k⁻¹ ∈ (frontierSetting S fS t p f).ON := by
  intro c hc k hk
  rw [frontier_F₀_eq_T n hn S fS t ht p f] at hc
  have h := (Subgroup.mem_centralizer_iff.mp (oddCoreIn_le _ hk.1)) c hc
  rw [h, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem _

theorem frontier_V3_inverted {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∃ d ∈ (frontierSetting S fS t p f).D,
      d ∉ Subgroup.centralizer ((frontierSetting S fS t p f).T : Set G) ∧
      ∀ k ∈ oddCoreIn (frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).L₀,
        d * k * d⁻¹ * k ∈ (frontierSetting S fS t p f).ON := by
  obtain ⟨-, ht2, -, -, -, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  obtain ⟨v, hvD, -, hvs, hinv, -⟩ :=
    frontier_quarter_data hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  refine ⟨v, hvD, fun hvC => ?_, fun k hk => hinv k ⟨oddCoreIn_le _ hk.1, hk.2⟩⟩
  have h := (Subgroup.mem_centralizer_iff.mp hvC) _ (frontierSetting S fS t p f).x₂_mem_T
  have e : v * (fS (s n) : G) * v⁻¹ = (fS (s n) : G) := by
    change (fS (s n) : G) * v = v * (fS (s n) : G) at h
    rw [← h, mul_inv_cancel_right]
  rw [hvs] at e
  have ht1 : t = 1 := by
    have e' : t * (fS (s n) : G) = 1 * (fS (s n) : G) := by rw [e, one_mul]
    exact mul_right_cancel e'
  rw [ht1, orderOf_one] at ht2
  exact absurd ht2 (by norm_num)

end Frontier

end CFSG.Semidihedral.AllPrime
