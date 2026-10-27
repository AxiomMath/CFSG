module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearBasic
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong

public section

namespace CFSG.QuasithinUnique.K1

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification

variable {K : Type} [Field K] {n : ℕ}

theorem eq_of_proj_eq_of_mul_self_eq_one [CharP K 2] (hn : 1 ≤ n)
    {g T : SpecialLinearGroup (Fin n) K} (hg : g * g = 1) (hT : T * T = 1)
    (h : proj n K g = proj n K T) : g = T := by
  have hz : g⁻¹ * T ∈ scalars n K := proj_eq_proj_iff.mp h
  have hcen : g⁻¹ * T ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) :=
    scalars_le_center n K hz
  have hcomm : g * (g⁻¹ * T) = (g⁻¹ * T) * g := Subgroup.mem_center_iff.mp hcen g
  have hTg : T * g⁻¹ = g⁻¹ * T := by
    have h1 : T = g⁻¹ * T * g := by
      rw [← hcomm]
      group
    calc T * g⁻¹ = g⁻¹ * T * g * g⁻¹ := by rw [← h1]
      _ = g⁻¹ * T := by group
  have hsq : (g⁻¹ * T) * (g⁻¹ * T) = 1 := by
    calc (g⁻¹ * T) * (g⁻¹ * T) = g⁻¹ * (T * g⁻¹) * T := by group
      _ = g⁻¹ * (g⁻¹ * T) * T := by rw [hTg]
      _ = (g * g)⁻¹ * (T * T) := by group
      _ = 1 := by rw [hg, hT]; group
  obtain ⟨c, -, hc⟩ := hz
  have h2 : (scalar (Fin n) (c : K)) * (scalar (Fin n) (c : K)) = 1 := by
    have := congrArg (fun w : SpecialLinearGroup (Fin n) K => (w : Matrix (Fin n) (Fin n) K)) hsq
    simpa only [Matrix.SpecialLinearGroup.coe_mul, hc, Matrix.SpecialLinearGroup.coe_one] using
      this
  have hcc : (c : K) * (c : K) = 1 := by
    have := congrFun₂ h2 ⟨0, hn⟩ ⟨0, hn⟩
    simpa [Matrix.scalar_apply, Matrix.diagonal_mul_diagonal] using this
  have hc1 : (c : K) = 1 := by
    have h' : ((c : K) - 1) ^ 2 = 0 := by
      linear_combination hcc + (1 - (c : K)) * (CharP.cast_eq_zero K 2)
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h')
  have hz1 : g⁻¹ * T = 1 := by
    apply Subtype.ext
    rw [hc, hc1, map_one]
    rfl
  exact inv_mul_eq_one.mp hz1

@[expose] noncomputable def stdAut (A : GL (Fin n) K) (σ : K ≃+* K) (ε : ℕ) :
    MulAut (SpecialLinearGroup (Fin n) K) :=
  CatalogueBHigherLinearAction.slConjugation n K A *
    CatalogueBHigherLinearField.slFieldAut (Fin n) K σ * CatalogueBGraphForm.slGraphAut n K ^ ε

theorem descendAut_stdAut (A : GL (Fin n) K) (σ : K ≃+* K) (ε : ℕ) :
    descendAut n K (stdAut A σ ε) = conjAut n K A * fieldAut n K σ * dualAut n K ^ ε := by
  simp only [stdAut, map_mul, map_pow]
  rfl

theorem fixes_transvection [CharP K 2] (hn : 1 ≤ n) (Φ : MulAut (SpecialLinearGroup (Fin n) K))
    (hΦ : ∀ u ∈ unitriangular n K, descendAut n K Φ (proj n K u) = proj n K u)
    {i j : Fin n} (hij : i < j) (t : K) :
    Φ (Matrix.SpecialLinearGroup.transvection hij.ne t) =
      Matrix.SpecialLinearGroup.transvection hij.ne t := by
  have hTT := transvection_mul_self_of_charTwo (K := K) hij.ne t
  have h1 := hΦ _ (transvection_mem_unitriangular hij t)
  rw [descendAut_proj] at h1
  refine eq_of_proj_eq_of_mul_self_eq_one hn ?_ hTT h1
  rw [← map_mul, hTT, map_one]

theorem coe_mul_coe_inv (A : GL (Fin n) K) :
    (A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem coe_inv_mul_coe (A : GL (Fin n) K) :
    ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem conj_eq_of_conj_one_add (A : GL (Fin n) K) {X Y : Matrix (Fin n) (Fin n) K}
    (h : (A : Matrix (Fin n) (Fin n) K) * (1 + X) *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + Y) :
    (A : Matrix (Fin n) (Fin n) K) * X * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Y := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, coe_mul_coe_inv] at h
  exact add_left_cancel h

theorem mul_eq_mul_of_conj_eq (A : GL (Fin n) K) {E : Matrix (Fin n) (Fin n) K}
    (h : (A : Matrix (Fin n) (Fin n) K) * E *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = E) :
    (A : Matrix (Fin n) (Fin n) K) * E = E * (A : Matrix (Fin n) (Fin n) K) := by
  calc (A : Matrix (Fin n) (Fin n) K) * E
      = ((A : Matrix (Fin n) (Fin n) K) * E *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * (A : Matrix (Fin n) (Fin n) K) := by
        rw [Matrix.mul_assoc _ _ (A : Matrix (Fin n) (Fin n) K), coe_inv_mul_coe, Matrix.mul_one]
    _ = E * (A : Matrix (Fin n) (Fin n) K) := by rw [h]

theorem map_one_add_single (σ : K ≃+* K) (i j : Fin n) (t : K) :
    ((1 : Matrix (Fin n) (Fin n) K) + single i j t).map σ = 1 + single i j (σ t) := by
  ext k l
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, single_apply]
  split_ifs <;> simp

theorem coe_stdAut_zero (A : GL (Fin n) K) (σ : K ≃+* K) (g : SpecialLinearGroup (Fin n) K) :
    ((stdAut A σ 0 g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (A : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K).map σ *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have h : stdAut A σ 0 g = CatalogueBHigherLinearAction.slConjugation n K A
      (CatalogueBHigherLinearField.slFieldAut (Fin n) K σ g) := by
    simp [stdAut]
  rw [h, coe_slConjugation]
  congr 2

theorem coe_stdAut_one (A : GL (Fin n) K) (σ : K ≃+* K) (g : SpecialLinearGroup (Fin n) K) :
    ((stdAut A σ 1 g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (A : Matrix (Fin n) (Fin n) K) *
        (((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map σ *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have h : stdAut A σ 1 g = CatalogueBHigherLinearAction.slConjugation n K A
      (CatalogueBHigherLinearField.slFieldAut (Fin n) K σ
        (CatalogueBGraphForm.slGraphAut n K g)) := by
    simp [stdAut]
  rw [h, coe_slConjugation]
  congr 2

theorem conj_mul_conj (A Ainv E F : Matrix (Fin n) (Fin n) K) (hAinvA : Ainv * A = 1) :
    (A * E * Ainv) * (A * F * Ainv) = A * (E * F) * Ainv := by
  calc (A * E * Ainv) * (A * F * Ainv) = A * E * (Ainv * A) * F * Ainv := by
        simp only [Matrix.mul_assoc]
    _ = A * (E * F) * Ainv := by rw [hAinvA, Matrix.mul_one, Matrix.mul_assoc A E F]

theorem conj_single_of_fixes_one (A : GL (Fin n) K) (σ : K ≃+* K)
    (hfix : ∀ {i j : Fin n} (hij : i < j) (t : K),
      stdAut A σ 1 (Matrix.SpecialLinearGroup.transvection hij.ne t) =
        Matrix.SpecialLinearGroup.transvection hij.ne t)
    {i j : Fin n} (hij : i < j) :
    (A : Matrix (Fin n) (Fin n) K) * single j i (-1 : K) *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = single i j (1 : K) := by
  have h := congrArg (fun g : SpecialLinearGroup (Fin n) K => (g : Matrix (Fin n) (Fin n) K))
    (hfix hij 1)
  rw [coe_stdAut_one, Matrix.SpecialLinearGroup.transvection_inv,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.transpose_add, Matrix.transpose_one, transpose_single, map_one_add_single, map_neg,
    map_one] at h
  exact conj_eq_of_conj_one_add A h

theorem false_of_fixes_one (hn : 3 ≤ n) (A : GL (Fin n) K) (σ : K ≃+* K)
    (hfix : ∀ {i j : Fin n} (hij : i < j) (t : K),
      stdAut A σ 1 (Matrix.SpecialLinearGroup.transvection hij.ne t) =
        Matrix.SpecialLinearGroup.transvection hij.ne t) : False := by
  have h01 : (⟨0, by omega⟩ : Fin n) < ⟨1, by omega⟩ := by simp [Fin.lt_def]
  have h12 : (⟨1, by omega⟩ : Fin n) < ⟨2, by omega⟩ := by simp [Fin.lt_def]
  have e01 := conj_single_of_fixes_one A σ hfix h01
  have e12 := conj_single_of_fixes_one A σ hfix h12
  have hprod : single (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) (1 : K) *
      single (⟨1, by omega⟩ : Fin n) (⟨2, by omega⟩ : Fin n) (1 : K) = 0 := by
    rw [← e01, ← e12, conj_mul_conj _ _ _ _ (coe_inv_mul_coe A),
      single_mul_single_of_ne _ _ _ _ (fin_mk_ne _ _ (by omega)), Matrix.mul_zero,
      Matrix.zero_mul]
  rw [single_mul_single_same] at hprod
  have h := congrFun₂ hprod ⟨0, by omega⟩ ⟨2, by omega⟩
  rw [single_apply_same] at h
  simp at h

theorem exists_matrix_of_fixes_zero (hn : 3 ≤ n) (A : GL (Fin n) K) (σ : K ≃+* K)
    (hfix : ∀ {i j : Fin n} (hij : i < j) (t : K),
      stdAut A σ 0 (Matrix.SpecialLinearGroup.transvection hij.ne t) =
        Matrix.SpecialLinearGroup.transvection hij.ne t) :
    σ = 1 ∧ ∃ a b : K, a ≠ 0 ∧ (A : Matrix (Fin n) (Fin n) K) =
      a • (1 : Matrix (Fin n) (Fin n) K) +
        b • single (⟨0, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n) (1 : K) := by
  have hconj : ∀ {i j : Fin n} (_ : i < j) (t : K), (A : Matrix (Fin n) (Fin n) K) *
      single i j (σ t) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = single i j t := by
    intro i j hij t
    have h := congrArg (fun g : SpecialLinearGroup (Fin n) K => (g : Matrix (Fin n) (Fin n) K))
      (hfix hij t)
    rw [coe_stdAut_zero, Matrix.SpecialLinearGroup.transvection_coe, map_one_add_single] at h
    exact conj_eq_of_conj_one_add A h
  have hcomm : ∀ i j : Fin n, (i : ℕ) + 1 = (j : ℕ) → (A : Matrix (Fin n) (Fin n) K) *
      single i j (1 : K) = single i j (1 : K) * (A : Matrix (Fin n) (Fin n) K) := by
    intro i j hij
    have hlt : i < j := by
      rw [Fin.lt_def]
      omega
    have h := hconj hlt 1
    rw [map_one] at h
    exact mul_eq_mul_of_conj_eq A h
  have h01 : (⟨0, by omega⟩ : Fin n) < ⟨1, by omega⟩ := by simp [Fin.lt_def]
  have hσ : ∀ t, σ t = t := by
    intro t
    have hEc := mul_eq_mul_of_conj_eq A (by
      have h := hconj h01 1
      rwa [map_one] at h)
    have hEc' : (A : Matrix (Fin n) (Fin n) K) *
        single (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) (1 : K) *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        single (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) (1 : K) := by
      have h := hconj h01 1
      rwa [map_one] at h
    have h2 := hconj h01 t
    have hs : single (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) (σ t) =
        σ t • single (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) (1 : K) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hs, Matrix.mul_smul, Matrix.smul_mul, hEc'] at h2
    have h3 := congrFun₂ h2 ⟨0, by omega⟩ ⟨1, by omega⟩
    simpa [Matrix.smul_apply, single_apply_same] using h3
  refine ⟨RingEquiv.ext hσ, ?_⟩
  obtain ⟨a, b, hab⟩ := eq_smul_one_add_single_of_commute (n := n) (by omega)
    (A : Matrix (Fin n) (Fin n) K) hcomm
  refine ⟨a, b, ?_, hab⟩
  rintro rfl
  have hE : single (⟨0, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n) (1 : K) *
      single (⟨0, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n) (1 : K) = 0 :=
    single_mul_single_of_ne _ _ _ _ (fin_mk_ne _ _ (by omega)) _
  have hAA : (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 0 := by
    rw [hab, zero_smul, zero_add, Matrix.smul_mul, Matrix.mul_smul, hE, smul_zero, smul_zero]
  have hunit : IsUnit ((A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K)) := by
    rw [← Units.val_mul]
    exact Units.isUnit _
  rw [hAA, isUnit_zero_iff] at hunit
  have := congrFun₂ hunit ⟨0, by omega⟩ ⟨0, by omega⟩
  simp at this

theorem eq_scalar_mul_toGL_transvection (hn : 3 ≤ n) (A : GL (Fin n) K) {a b : K} (ha : a ≠ 0)
    (hil : (⟨0, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩)
    (hA : (A : Matrix (Fin n) (Fin n) K) = a • (1 : Matrix (Fin n) (Fin n) K) +
      b • single (⟨0, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n) (1 : K)) :
    A = Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 a ha) *
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hil (b / a)) := by
  have hab : a * (b / a) = b := by field_simp
  apply Units.ext
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.transvection_coe, hA,
    Matrix.scalar_apply, Units.val_mk0, ← Matrix.smul_eq_diagonal_mul, smul_add]
  simp only [Matrix.smul_single, smul_eq_mul, mul_one, hab]

theorem slConjugation_eq_conj_transvection (hn : 3 ≤ n) (A : GL (Fin n) K) {a b : K}
    (ha : a ≠ 0) (hil : (⟨0, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩)
    (hA : (A : Matrix (Fin n) (Fin n) K) = a • (1 : Matrix (Fin n) (Fin n) K) +
      b • single (⟨0, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n) (1 : K))
    (g : SpecialLinearGroup (Fin n) K) :
    CatalogueBHigherLinearAction.slConjugation n K A g =
      Matrix.SpecialLinearGroup.transvection hil (b / a) * g *
        (Matrix.SpecialLinearGroup.transvection hil (b / a))⁻¹ := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CatalogueBHigherLinearAction.toGL_slConjugation,
    eq_scalar_mul_toGL_transvection hn A ha hil hA, map_mul, map_mul, map_inv]
  set s := Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 a ha) with hs
  have hscen : s ∈ Subgroup.center (GL (Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  have hcomm := Subgroup.mem_center_iff.mp hscen
  set Y := Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hil (b / a))
  set G := Matrix.SpecialLinearGroup.toGL g
  calc (s * Y) * G * (s * Y)⁻¹ = s * (Y * G * Y⁻¹) * s⁻¹ := by group
    _ = (Y * G * Y⁻¹) * s * s⁻¹ := by rw [← hcomm (Y * G * Y⁻¹)]
    _ = Y * G * Y⁻¹ := by group

theorem exists_inner_of_matrix (hn : 3 ≤ n) (A : GL (Fin n) K) {a b : K} (ha : a ≠ 0)
    (hA : (A : Matrix (Fin n) (Fin n) K) = a • (1 : Matrix (Fin n) (Fin n) K) +
      b • single (⟨0, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n) (1 : K)) :
    ∃ x : projectiveSL n K, ∀ y : projectiveSL n K,
      descendAut n K (CatalogueBHigherLinearAction.slConjugation n K A) y = x⁻¹ * y * x := by
  have hil : (⟨0, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := fin_mk_ne _ _ (by omega)
  refine ⟨(proj n K (Matrix.SpecialLinearGroup.transvection hil (b / a)))⁻¹, fun y => ?_⟩
  obtain ⟨g, rfl⟩ := proj_surjective n K y
  rw [descendAut_proj, slConjugation_eq_conj_transvection hn A ha hil hA, map_mul, map_mul,
    map_inv, inv_inv]

theorem inner_of_fixes_unitriangular [Finite K] [CharP K 2] (hn : 3 ≤ n)
    (β : MulAut (projectiveSL n K))
    (hβ : ∀ u ∈ unitriangular n K, β (proj n K u) = proj n K u) :
    ∃ x : projectiveSL n K, ∀ y : projectiveSL n K, β y = x⁻¹ * y * x := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) (n := n) hn
  obtain ⟨A, σ, ε, hε, hβeq⟩ := hgen β
  have hdesc : descendAut n K (stdAut A σ ε) = β := by
    rw [descendAut_stdAut, ← hβeq]
  have hfix : ∀ {i j : Fin n} (hij : i < j) (t : K),
      stdAut A σ ε (Matrix.SpecialLinearGroup.transvection hij.ne t) =
        Matrix.SpecialLinearGroup.transvection hij.ne t := fun hij t =>
    fixes_transvection (by omega) _ (fun u hu => by rw [hdesc]; exact hβ u hu) hij t
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · obtain ⟨hσ, a, b, ha, hA⟩ := exists_matrix_of_fixes_zero hn A σ hfix
    subst hσ
    have hstd : stdAut A 1 0 = CatalogueBHigherLinearAction.slConjugation n K A := by
      simp [stdAut]
    rw [hstd] at hdesc
    obtain ⟨x, hx⟩ := exists_inner_of_matrix hn A ha hA
    exact ⟨x, fun y => by rw [← hdesc]; exact hx y⟩
  · exact (false_of_fixes_one hn A σ hfix).elim

theorem sylowCentralizingAutInner_projectiveSL [Finite K] [CharP K 2] (hn : 3 ≤ n) :
    SylowCentralizingAutInner (projectiveSL n K) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := K) 2 hn1
  have hQ₀ : IsSylowTwoOf (projUnitriangular n K) ⊤ := by
    rw [← hS]
    exact isSylowTwoOf_top_iff.mpr ⟨S.isPGroup', S.not_dvd_index⟩
  refine sylowCentralizingAutInner_of_sylow _ hQ₀ fun β hβ => ?_
  exact inner_of_fixes_unitriangular hn β fun u hu => hβ _ (Subgroup.mem_map_of_mem _ hu)

end CFSG.QuasithinUnique.K1
