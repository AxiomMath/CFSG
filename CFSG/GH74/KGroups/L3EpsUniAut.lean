module

public import CFSG.GH74.KGroups.L3EpsUniBlock
public import CFSG.GH74.Generic.S45.LUniFix
public import CFSG.GH74.KGroups.L3EpsBlockAut

public section

namespace CFSG.GH74.KGroups.L3Eps.Uni

open Matrix Subgroup CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.SubgroupLists
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
open CFSG.GH74.Generic.S45.Uni (class2_transpose scalar_of_comp det_unitary_norm ne_zero_of_unitary
  two_ne_zero_of_ne mkSU coe_mkSU)
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} {F : Type} [Field F]

theorem false_of_alt (h : UnitaryFieldData p f F) (h2 : (2 : F) ≠ 0) {A : Matrix (Fin 3) (Fin 3) F}
    (hAu : (A.map h.bar)ᵀ * A = 1) (hAA : A * A.map h.bar = (-1 : F) • 1) : False := by
  obtain ⟨-, hAt'⟩ := class2_transpose h hAu hAA
  have hd1 := det_unitary_norm h hAu
  have h3 : A.det = -A.det := by
    have := congrArg Matrix.det hAt'
    rw [det_transpose, det_smul, Fintype.card_fin, (by decide : Odd 3).neg_pow, one_pow] at this
    linear_combination this
  have h4 : A.det = 0 := by
    have : (2 : F) * A.det = 0 := by linear_combination h3
    exact (mul_eq_zero.1 this).resolve_left h2
  rw [h4, map_zero, zero_mul] at hd1
  exact zero_ne_one hd1

theorem involution_type (h : UnitaryFieldData p f F) (hp : p ≠ 2) (h5 : 5 ≤ p ^ f)
    {K : Type} [Group K] {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ)
    {σ : MulAut K} (hσ : σ * σ = 1) :
    (∃ A : GL (Fin 3) F,
        ((A : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1 ∧
        (∃ μ : F, (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) = μ • 1) ∧
        ∀ g : ↥(unitarySU p f F 3), ∃ g' : ↥(unitarySU p f F 3),
          (g' : GL (Fin 3) F) = A * g * A⁻¹ ∧ θ g' = σ (θ g)) ∨
    (∃ (φ : F ≃+* F) (A : GL (Fin 3) F), (∀ c, φ c = h.bar c) ∧
        ((A : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1 ∧
        (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F).map h.bar = 1 ∧
        ∀ g : ↥(unitarySU p f F 3), ∃ g' : ↥(unitarySU p f F 3),
          (g' : GL (Fin 3) F) = A * glAut φ (g : GL (Fin 3) F) * A⁻¹ ∧ θ g' = σ (θ g)) := by
  have hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f F 3) := by
    rw [hθ.ker]; exact unitaryScalars_le_center h 3
  obtain ⟨A, φ, hA, hAu, hlift, hinv⟩ :=
    exists_lift_unitarySU h hp h5 (le_refl 3) θ hθ.surj hker (σ : K ≃* K)
  obtain ⟨hφ, hcomp⟩ := hinv (fun x => by
    have := congrArg (fun φ : MulAut K => φ x) hσ
    simpa using this)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_ne h hp
  have hφφ : φ * φ = 1 := by
    rcases hφ with rfl | hb
    · ext c
      rfl
    · ext c
      change φ (φ c) = c
      rw [hb, hb, h.bar_bar]
  obtain ⟨μ, hμ⟩ := scalar_of_comp h h2 (le_refl 3) hφφ hA hcomp
  have hlift' : ∀ g : ↥(unitarySU p f F 3), ∃ g' : ↥(unitarySU p f F 3),
      (g' : GL (Fin 3) F) = A * glAut φ (g : GL (Fin 3) F) * A⁻¹ ∧ θ g' = σ (θ g) :=
    fun g => ⟨unitaryConjHom A φ hA g, rfl, hlift g⟩
  rcases hφ with rfl | hb
  · left
    refine ⟨A, hAu, ⟨μ, ?_⟩, fun g => ?_⟩
    · have hmap : (A : Matrix (Fin 3) (Fin 3) F).map (RingEquiv.refl F) = A := by
        ext i j
        rfl
      rw [hmap] at hμ
      exact hμ
    · have : glAut (RingEquiv.refl F) (g : GL (Fin 3) F) = g := by
        apply Units.ext
        ext i j
        rfl
      rw [← this]
      exact hlift' g
  · right
    refine ⟨φ, A, hb, hAu, ?_, hlift'⟩
    have hmapφ : (A : Matrix (Fin 3) (Fin 3) F).map φ = (A : Matrix (Fin 3) (Fin 3) F).map h.bar := by
      ext i j
      exact hb _
    rw [hmapφ] at hμ
    obtain ⟨hAt, hAt'⟩ := class2_transpose h hAu hμ
    have hA0 := ne_zero_of_unitary h (by omega) hAu
    have hμμ : μ * μ = 1 := by
      have h3 : (μ * μ - 1) • (A : Matrix (Fin 3) (Fin 3) F) = 0 := by
        rw [sub_smul, one_smul, ← smul_smul, ← hAt', ← hAt, sub_self]
      have := (smul_eq_zero.1 h3).resolve_right hA0
      linear_combination this
    rcases mul_self_eq_one_iff.1 hμμ with hμ1 | hμ1
    · rw [hμ1, one_smul] at hμ
      exact hμ
    · exfalso
      rw [hμ1] at hμ
      exact false_of_alt h h2 hAu hμ

section Commute

theorem form_of_commute_all (h : UnitaryFieldData p f F) (h5 : 5 ≤ p ^ f) {X : Matrix (Fin 3) (Fin 3) F}
    (hX : ∀ B : ↥(unitarySU p f F 2), X * leviMat (matU B) = leviMat (matU B) * X) :
    X 0 1 = 0 ∧ X 1 0 = 0 ∧ X 0 2 = 0 ∧ X 1 2 = 0 ∧ X 2 0 = 0 ∧ X 2 1 = 0 ∧ X 0 0 = X 1 1 := by
  obtain ⟨l, hl0, hl, hl1, hl2⟩ := exists_norm_one_ne h h5
  have hD := hX (dTestU h hl0 hl)
  have hJ := hX (jU h)
  rw [matU_dTestU] at hD
  rw [matU_jU] at hJ
  exact form_of_commute_levi hl0 hl1 hl2 hD hJ

theorem commute_levi_of_central (h : UnitaryFieldData p f F) (h5 : 5 ≤ p ^ f) (X : GL (Fin 3) F)
    (hX : ∀ B : ↥(unitarySU p f F 2),
      X * blockGL3 (B : GL (Fin 2) F) * X⁻¹ * (blockGL3 (B : GL (Fin 2) F))⁻¹ ∈
        Subgroup.center (GL (Fin 3) F)) (B : ↥(unitarySU p f F 2)) :
    X * blockGL3 (B : GL (Fin 2) F) = blockGL3 (B : GL (Fin 2) F) * X := by
  have := h.finite
  have := h.charP
  have : Fact p.Prime := ⟨h.prime⟩
  have hperf : Group.IsPerfect ↥(unitarySU p f F 2) :=
    isPerfect_statedSU_two h.card_eq_sq (by omega)
  exact perfect_commute_of_central_commutator hperf
    (blockGL3.comp (unitarySU p f F 2).subtype) X hX B

theorem scalar_mem_center (c : Fˣ) :
    (GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) F) ∈ Subgroup.center (GL (Fin 3) F) :=
  Subgroup.mem_center_iff.2 fun y => (commute_scalar c y).eq

theorem conj_scalar_mul (c : Fˣ) (E g : GL (Fin 3) F) :
    (GeneralLinearGroup.scalar (Fin 3) c * E) * g * (GeneralLinearGroup.scalar (Fin 3) c * E)⁻¹ =
      E * g * E⁻¹ := by
  have hz : ∀ y : GL (Fin 3) F, GeneralLinearGroup.scalar (Fin 3) c * y =
      y * GeneralLinearGroup.scalar (Fin 3) c := fun y => (commute_scalar c y).symm.eq
  calc (GeneralLinearGroup.scalar (Fin 3) c * E) * g * (GeneralLinearGroup.scalar (Fin 3) c * E)⁻¹
      = GeneralLinearGroup.scalar (Fin 3) c * (E * g * E⁻¹) * (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ := by
        group
    _ = E * g * E⁻¹ := by rw [hz, mul_inv_cancel_right]

end Commute

section B4

theorem bar_mul_jmat (h : UnitaryFieldData p f F) (B : ↥(unitarySU p f F 2)) :
    (matU B).map h.bar * !![0, 1; -1, 0] = !![0, 1; -1, 0] * matU B := by
  have hB := (mem_unitarySU_iff h).1 B.2
  have hinv : (matU B)⁻¹ = ((matU B).map h.bar)ᵀ := Matrix.inv_eq_left_inv hB.2
  have hadj : (matU B)⁻¹ = adjugate (matU B) := by
    rw [Matrix.inv_def]
    have : (matU B).det = 1 := hB.1
    rw [this, Ring.inverse_one, one_smul]
  rw [hadj, Matrix.adjugate_fin_two] at hinv
  have e00 := congrFun (congrFun hinv 0) 0
  have e01 := congrFun (congrFun hinv 0) 1
  have e10 := congrFun (congrFun hinv 1) 0
  have e11 := congrFun (congrFun hinv 1) 1
  simp at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
    | linear_combination e00 | linear_combination -e00
    | linear_combination e01 | linear_combination -e01
    | linear_combination e10 | linear_combination -e10
    | linear_combination e11 | linear_combination -e11

@[expose] noncomputable def jGL (h : UnitaryFieldData p f F) : GL (Fin 3) F :=
  blockGL3 ((jU h : ↥(unitarySU p f F 2)) : GL (Fin 2) F)

theorem coe_jGL (h : UnitaryFieldData p f F) :
    ((jGL h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = leviMat !![0, 1; -1, 0] := rfl

theorem glAut_blockGL3_mul_jGL (h : UnitaryFieldData p f F) {φ : F ≃+* F} (hφ : ∀ c, φ c = h.bar c)
    (B : ↥(unitarySU p f F 2)) :
    glAut φ (blockGL3 (B : GL (Fin 2) F)) * jGL h = jGL h * blockGL3 (B : GL (Fin 2) F) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_glAut, coe_blockGL3, coe_jGL]
  have hmap : (leviMat (((B : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)).map φ =
      leviMat ((((B : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F).map h.bar) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [leviMat, hφ]
  rw [hmap, ← leviMat_mul, ← leviMat_mul]
  exact congrArg leviMat (bar_mul_jmat h B)

theorem aut_fixing_typeI (h : UnitaryFieldData p f F) (h5 : 5 ≤ p ^ f) (hq : Odd (p ^ f))
    {K : Type} [Group K] {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ)
    {σ : MulAut K} {A : GL (Fin 3) F}
    (hAA : ∃ μ : F, (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) = μ • 1)
    (hrel : ∀ g : ↥(unitarySU p f F 3), ∃ g' : ↥(unitarySU p f F 3),
      (g' : GL (Fin 3) F) = A * g * A⁻¹ ∧ θ g' = σ (θ g))
    (hfix : ∀ s ∈ levS hq θ, σ s = s) : σ = 1 ∨ σ = MulAut.conj (θ (dU hq)) := by
  have hcen : ∀ B : ↥(unitarySU p f F 2),
      A * blockGL3 (B : GL (Fin 2) F) = blockGL3 (B : GL (Fin 2) F) * A := by
    refine commute_levi_of_central h h5 A (fun B => ?_)
    obtain ⟨g', hg'GL, hg'θ⟩ := hrel (levU hq.pos B)
    rw [hfix _ (θ_levU_mem_levS hq B)] at hg'θ
    obtain ⟨c, -, -, hc⟩ := (theta_eq_iff h θ hθ.ker).1 hg'θ.symm
    have hform : (g' : GL (Fin 3) F) = blockGL3 (B : GL (Fin 2) F) * GeneralLinearGroup.scalar (Fin 3) c := by
      apply Units.ext
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar]
      exact hc
    have h1 : A * blockGL3 (B : GL (Fin 2) F) * A⁻¹ = g' := hg'GL.symm
    rw [h1, hform, mul_inv_eq_iff_eq_mul.2 (commute_scalar c _).eq]
    exact scalar_mem_center c
  have hM : ∀ B : ↥(unitarySU p f F 2),
      (A : Matrix (Fin 3) (Fin 3) F) * leviMat (matU B) = leviMat (matU B) * (A : Matrix (Fin 3) (Fin 3) F) := by
    intro B
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) (hcen B)
    simpa only [Units.val_mul, coe_blockGL3] using this
  obtain ⟨e01, e10, e02, e12, e20, e21, e00⟩ := form_of_commute_all h h5 hM
  obtain ⟨μ, hμ⟩ := hAA
  have hμ00 := congrFun (congrFun hμ 0) 0
  have hμ22 := congrFun (congrFun hμ 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, e01, e10, e02, e12, e20, e21] at hμ00 hμ22
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit A)
  rw [Matrix.det_fin_three] at hdet
  simp [e01, e10, e02, e12, e20, e21] at hdet
  have ha0 : (A : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := hdet.1.1
  have hAm : ((A : Matrix (Fin 3) (Fin 3) F) 0 0 - (A : Matrix (Fin 3) (Fin 3) F) 2 2) *
      ((A : Matrix (Fin 3) (Fin 3) F) 0 0 + (A : Matrix (Fin 3) (Fin 3) F) 2 2) = 0 := by
    linear_combination hμ00 - hμ22
  have hdiag : (A : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![(A : Matrix (Fin 3) (Fin 3) F) 0 0, (A : Matrix (Fin 3) (Fin 3) F) 0 0,
        (A : Matrix (Fin 3) (Fin 3) F) 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonal, e01, e10, e02, e12, e20, e21, ← e00]
  obtain ⟨a, ha⟩ : ∃ a : F, (A : Matrix (Fin 3) (Fin 3) F) 0 0 = a := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : F, (A : Matrix (Fin 3) (Fin 3) F) 2 2 = m := ⟨_, rfl⟩
  rw [ha, hm] at hdiag hAm
  rw [ha] at ha0
  rcases mul_eq_zero.1 hAm with h1 | h1
  · left
    have hma : m = a := (sub_eq_zero.1 h1).symm
    have hAeq : A = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 a ha0) := by
      apply Units.ext
      rw [GeneralLinearGroup.coe_scalar, hdiag, hma]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, diagonal]
    have hcs : ∀ g : GL (Fin 3) F, A * g * A⁻¹ = g := fun g => by
      have := conj_scalar_mul (Units.mk0 a ha0) 1 g
      rw [hAeq]
      simpa using this
    ext x
    obtain ⟨g, rfl⟩ := hθ.surj x
    obtain ⟨g', hg'GL, hg'θ⟩ := hrel g
    have hgg : g' = g := Subtype.ext (by rw [hg'GL, hcs])
    rw [MulAut.one_apply, ← hg'θ, hgg]
  · right
    have hma : m = -a := by linear_combination h1
    have hAeq : A = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (-a) (neg_ne_zero.2 ha0)) *
        ((dU hq : ↥(unitarySU p f F 3)) : GL (Fin 3) F) := by
      apply Units.ext
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, hdiag, hma, coe_dU]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.scalar_apply, Matrix.mul_apply, diagonal]
    ext x
    obtain ⟨g, rfl⟩ := hθ.surj x
    obtain ⟨g', hg'GL, hg'θ⟩ := hrel g
    have hgg : g' = dU hq * g * (dU hq)⁻¹ := by
      apply Subtype.ext
      rw [hg'GL, hAeq, conj_scalar_mul]
      rfl
    rw [MulAut.conj_apply, ← hg'θ, hgg, map_mul, map_mul, map_inv]

theorem false_of_fixing_typeII (h : UnitaryFieldData p f F) (h5 : 5 ≤ p ^ f) (hq : Odd (p ^ f))
    {K : Type} [Group K] {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ)
    {σ : MulAut K} {φ : F ≃+* F} {A : GL (Fin 3) F} (hφ : ∀ c, φ c = h.bar c)
    (hAu : ((A : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1)
    (hAA : (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F).map h.bar = 1)
    (hrel : ∀ g : ↥(unitarySU p f F 3), ∃ g' : ↥(unitarySU p f F 3),
      (g' : GL (Fin 3) F) = A * glAut φ (g : GL (Fin 3) F) * A⁻¹ ∧ θ g' = σ (θ g))
    (hfix : ∀ s ∈ levS hq θ, σ s = s) : False := by
  have hcen : ∀ B : ↥(unitarySU p f F 2), (A * jGL h) * blockGL3 (B : GL (Fin 2) F) =
      blockGL3 (B : GL (Fin 2) F) * (A * jGL h) := by
    refine commute_levi_of_central h h5 (A * jGL h) (fun B => ?_)
    obtain ⟨g', hg'GL, hg'θ⟩ := hrel (levU hq.pos B)
    rw [hfix _ (θ_levU_mem_levS hq B)] at hg'θ
    obtain ⟨c, -, -, hc⟩ := (theta_eq_iff h θ hθ.ker).1 hg'θ.symm
    have hform : (g' : GL (Fin 3) F) =
        blockGL3 (B : GL (Fin 2) F) * GeneralLinearGroup.scalar (Fin 3) c := by
      apply Units.ext
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar]
      exact hc
    have hJ : glAut φ (blockGL3 (B : GL (Fin 2) F)) =
        jGL h * blockGL3 (B : GL (Fin 2) F) * (jGL h)⁻¹ :=
      eq_mul_inv_of_mul_eq (glAut_blockGL3_mul_jGL h hφ B)
    have h1 : A * (jGL h * blockGL3 (B : GL (Fin 2) F) * (jGL h)⁻¹) * A⁻¹ = g' := by
      rw [← hJ]
      exact hg'GL.symm
    have h2 : (A * jGL h) * blockGL3 (B : GL (Fin 2) F) * (A * jGL h)⁻¹ = g' := by
      rw [← h1]
      group
    rw [h2, hform, mul_inv_eq_iff_eq_mul.2 (commute_scalar c _).eq]
    exact scalar_mem_center c
  have hM : ∀ B : ↥(unitarySU p f F 2),
      ((A : Matrix (Fin 3) (Fin 3) F) * leviMat !![0, 1; -1, 0]) * leviMat (matU B) =
        leviMat (matU B) * ((A : Matrix (Fin 3) (Fin 3) F) * leviMat !![0, 1; -1, 0]) := by
    intro B
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) (hcen B)
    simpa only [Units.val_mul, coe_jGL, coe_blockGL3] using this
  obtain ⟨e01, e10, e02, e12, e20, e21, e00⟩ := form_of_commute_all h h5 hM
  simp [Matrix.mul_apply, Fin.sum_univ_three, leviMat] at e01 e10 e02 e12 e20 e21 e00
  have u00 := congrFun (congrFun hAu 0) 0
  have v00 := congrFun (congrFun hAA 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, e01, e02, e21, ← e00] at u00 v00
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_pow h hq
  apply h2
  linear_combination -(u00 + v00)

theorem aut_fixing_levS (h : UnitaryFieldData p f F) (hp : p ≠ 2) (h5 : 5 ≤ p ^ f) (hq : Odd (p ^ f))
    {K : Type} [Group K] {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ)
    {σ : MulAut K} (hσ : σ * σ = 1) (hfix : ∀ s ∈ levS hq θ, σ s = s) :
    σ = 1 ∨ σ = MulAut.conj (θ (dU hq)) := by
  rcases involution_type h hp h5 hθ hσ with ⟨A, hAu, hAA, hrel⟩ | ⟨φ, A, hφ, hAu, hAA, hrel⟩
  · exact aut_fixing_typeI h h5 hq hθ hAA hrel hfix
  · exact (false_of_fixing_typeII h h5 hq hθ hφ hAu hAA hrel hfix).elim

end B4

section Inner

theorem exists_conj_of_typeI (h : UnitaryFieldData p f F)
    {K : Type} [Group K] {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ)
    {σ : MulAut K} {A : GL (Fin 3) F}
    (hAu : ((A : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1)
    (hAA : ∃ μ : F, (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) = μ • 1)
    (hrel : ∀ g : ↥(unitarySU p f F 3), ∃ g' : ↥(unitarySU p f F 3),
      (g' : GL (Fin 3) F) = A * g * A⁻¹ ∧ θ g' = σ (θ g)) :
    ∃ y : K, MulAut.conj y = σ := by
  obtain ⟨μ, hμ⟩ := hAA
  set Am : Matrix (Fin 3) (Fin 3) F := (A : Matrix (Fin 3) (Fin 3) F) with hAm
  have hd0 : Am.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit A)).ne_zero
  have hdd : Am.det * Am.det = μ ^ 3 := by
    have := congrArg Matrix.det hμ
    rw [det_mul, det_smul, det_one, Fintype.card_fin] at this
    linear_combination this
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0] at hdd
    exact hd0 (mul_self_eq_zero.1 (by simpa using hdd))
  have hNd := det_unitary_norm h hAu
  have hNμ : h.bar μ * μ = 1 := by
    have h1 : ((Am * Am).map h.bar)ᵀ * (Am * Am) = 1 := by
      rw [Matrix.map_mul, transpose_mul]
      calc (Am.map h.bar)ᵀ * (Am.map h.bar)ᵀ * (Am * Am)
          = (Am.map h.bar)ᵀ * ((Am.map h.bar)ᵀ * Am) * Am := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hAu, Matrix.mul_one, hAu]
    rw [hμ] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] using h2
  set ν : F := μ / Am.det with hν
  have hν0 : ν ≠ 0 := div_ne_zero hμ0 hd0
  have hν3 : ν ^ 3 * Am.det = 1 := by
    rw [hν, div_pow]
    field_simp
    linear_combination -hdd
  have hNν : h.bar ν * ν = 1 := by
    have : h.bar ν * ν = (h.bar μ * μ) / (h.bar Am.det * Am.det) := by
      rw [hν, map_div₀]
      field_simp
    rw [this, hNμ, hNd, div_one]
  have hxu : (((ν • Am).map h.bar)ᵀ) * (ν • Am) = 1 := by
    have hm : (ν • Am).map h.bar = h.bar ν • Am.map h.bar := by
      ext i j
      simp
    rw [hm, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hAu, hNν, one_smul]
  have hxd : (ν • Am).det = 1 := by
    rw [det_smul, Fintype.card_fin, hν3]
  let x : ↥(unitarySU p f F 3) := mkSU h (ν • Am) hxu hxd
  have hxGL : (x : GL (Fin 3) F) = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ν hν0) * A := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_mkSU, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    rfl
  refine ⟨θ x, ?_⟩
  ext k
  obtain ⟨g, rfl⟩ := hθ.surj k
  obtain ⟨g', hg'GL, hg'θ⟩ := hrel g
  have hgg : g' = x * g * x⁻¹ := by
    apply Subtype.ext
    rw [hg'GL]
    show A * g * A⁻¹ = (x : GL (Fin 3) F) * g * (x : GL (Fin 3) F)⁻¹
    rw [hxGL, conj_scalar_mul]
  rw [← hg'θ, hgg, MulAut.conj_apply, map_mul, map_mul, map_inv]

end Inner




section B3

theorem dU_mul_self (hq : Odd (p ^ f)) : dU (p := p) (f := f) (F := F) hq * dU hq = 1 := by
  apply matU_ext
  rw [matU_mul, matU_dU, matU_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, diagonal]

theorem glAut_dU (hq : Odd (p ^ f)) (φ : F ≃+* F) :
    glAut φ ((dU hq : ↥(unitarySU p f F 3)) : GL (Fin 3) F) = ((dU hq : ↥(unitarySU p f F 3)) : GL (Fin 3) F) := by
  apply Units.ext
  rw [coe_glAut, coe_dU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal]

theorem gl_ne_zero (X : GL (Fin 3) F) : (X : Matrix (Fin 3) (Fin 3) F) ≠ 0 := by
  intro h0
  have hdet := ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit X)).ne_zero
  apply hdet
  rw [h0]
  simp

theorem levi_twist (β : F →+* F) {A : Matrix (Fin 3) (Fin 3) F} (hA : IsLevi A) (hm : A 2 2 ≠ 0)
    {B B' : Matrix (Fin 2) (Fin 2) F} {G : Matrix (Fin 3) (Fin 3) F} {c : F}
    (hG : G = c • leviMat B') (hGA : G * A = A * (leviMat B).map β) :
    c = 1 ∧ B' * !![A 0 0, A 0 1; A 1 0, A 1 1] = !![A 0 0, A 0 1; A 1 0, A 1 1] * B.map β := by
  obtain ⟨a1, a2, a3, a4⟩ := hA
  subst hG
  have e22 := congrFun (congrFun hGA 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, leviMat, a1, a2, a3, a4] at e22
  have hc : c = 1 := by
    have h1 : (c - 1) * A 2 2 = 0 := by linear_combination e22
    have := (mul_eq_zero.1 h1).resolve_right hm
    linear_combination this
  refine ⟨hc, ?_⟩
  subst hc
  have e00 := congrFun (congrFun hGA 0) 0
  have e01 := congrFun (congrFun hGA 0) 1
  have e10 := congrFun (congrFun hGA 1) 0
  have e11 := congrFun (congrFun hGA 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, leviMat, a1, a2, a3, a4]
    at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
    | linear_combination e00 | linear_combination e01 | linear_combination e10 | linear_combination e11

theorem K2_ne_scalar (h : UnitaryFieldData p f F) (h2 : (2 : F) ≠ 0) {A : Matrix (Fin 3) (Fin 3) F}
    (hA : IsLevi A) (hAu : (A.map h.bar)ᵀ * A = 1) (hAA : A * A.map h.bar = 1) (c : F) :
    !![A 0 0, A 0 1; A 1 0, A 1 1] * !![0, 1; -1, 0] ≠ c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  intro hK
  obtain ⟨a1, a2, a3, a4⟩ := hA
  have k00 := congrFun (congrFun hK 0) 0
  have k01 := congrFun (congrFun hK 0) 1
  have k10 := congrFun (congrFun hK 1) 0
  have k11 := congrFun (congrFun hK 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at k00 k01 k10 k11
  have u00 := congrFun (congrFun hAu 0) 0
  have v00 := congrFun (congrFun hAA 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, a1, a3, k01] at u00 v00
  apply h2
  have hA01 : A 0 1 = -A 1 0 := by linear_combination -k00 + k11
  rw [hA01] at v00
  linear_combination -(u00 + v00)

theorem mul_scalar_eq_smul {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (c : F) :
    M * Matrix.scalar (Fin n) c = c • M := by
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal]

theorem toSL2_injective (h : UnitaryFieldData p f F) : Function.Injective (toSL2 h) := by
  intro B B' hB
  apply matU_ext
  exact congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) hB

theorem solvable_of_typeII (h : UnitaryFieldData p f F) (hq : Odd (p ^ f))
    {K : Type} [Group K] {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ)
    {σ : MulAut K} {φ : F ≃+* F} {A : GL (Fin 3) F} (hφ : ∀ c, φ c = h.bar c)
    (hAu : ((A : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1)
    (hAA : (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F).map h.bar = 1)
    (hrel : ∀ g : ↥(unitarySU p f F 3), ∃ g' : ↥(unitarySU p f F 3),
      (g' : GL (Fin 3) F) = A * glAut φ (g : GL (Fin 3) F) * A⁻¹ ∧ θ g' = σ (θ g))
    (hσt : σ (θ (dU hq)) = θ (dU hq))
    (P : Subgroup K) (hPS : P ≤ levS hq θ)
    (hP : ∀ s ∈ P, σ s * s⁻¹ ∈ Subgroup.zpowers (θ (dU hq))) : Group.IsSolvable ↥P := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_pow h hq
  have hALevi : IsLevi (A : Matrix (Fin 3) (Fin 3) F) := by
    obtain ⟨g₁, hg₁GL, hg₁θ⟩ := hrel (dU hq)
    rw [hσt] at hg₁θ
    obtain ⟨c, -, hc3, hc⟩ := (theta_eq_iff h θ hθ.ker).1 hg₁θ.symm
    have hc3' : (c : F) ^ 3 = 1 := by simpa using congrArg (fun u : Fˣ => (u : F)) hc3
    have hform : (g₁ : GL (Fin 3) F) = ((dU hq : ↥(unitarySU p f F 3)) : GL (Fin 3) F) *
        GeneralLinearGroup.scalar (Fin 3) c := by
      apply Units.ext
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar]
      exact hc
    rw [glAut_dU] at hg₁GL
    have h1 : A * ((dU hq : ↥(unitarySU p f F 3)) : GL (Fin 3) F) * A⁻¹ =
        ((dU hq : ↥(unitarySU p f F 3)) : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c := by
      rw [← hg₁GL, hform]
    have h3 : ((dU hq : ↥(unitarySU p f F 3)) : GL (Fin 3) F) * A⁻¹ =
        A⁻¹ * (((dU hq : ↥(unitarySU p f F 3)) : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c) := by
      calc ((dU hq : ↥(unitarySU p f F 3)) : GL (Fin 3) F) * A⁻¹
          = A⁻¹ * (A * ((dU hq : ↥(unitarySU p f F 3)) : GL (Fin 3) F) * A⁻¹) := by group
        _ = _ := by rw [h1]
    have hM' : ((dNeg : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * ((dNeg : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) *
          Matrix.scalar (Fin 3) (c : F) := by
      rw [dNeg_coe_eq_diagonal]
      have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) h3
      simp only [Units.val_mul, coe_dU, GeneralLinearGroup.coe_scalar] at this
      rw [this, Matrix.mul_assoc]
    have hc1 := eq_one_of_dNeg_scalar h2 (gl_ne_zero A⁻¹) hc3' hM'
    have hc1' : c = 1 := Units.ext hc1
    rw [hc1', map_one, mul_one] at h1
    have h4 : A * ((dU hq : ↥(unitarySU p f F 3)) : GL (Fin 3) F) =
        ((dU hq : ↥(unitarySU p f F 3)) : GL (Fin 3) F) * A := mul_inv_eq_iff_eq_mul.1 h1
    refine isLevi_of_commute h2 ?_
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) h4
    simpa only [Units.val_mul, coe_dU] using this
  have hm : (A : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := by
    obtain ⟨a1, a2, a3, a4⟩ := hALevi
    have hdet := ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit A)).ne_zero
    intro h0
    apply hdet
    rw [Matrix.det_fin_three]
    simp [a1, a2, a3, a4, h0]
  set A₂ : Matrix (Fin 2) (Fin 2) F :=
    !![(A : Matrix (Fin 3) (Fin 3) F) 0 0, (A : Matrix (Fin 3) (Fin 3) F) 0 1;
      (A : Matrix (Fin 3) (Fin 3) F) 1 0, (A : Matrix (Fin 3) (Fin 3) F) 1 1] with hA₂
  have ht2 : θ (dU hq) * θ (dU hq) = 1 := by rw [← map_mul, dU_mul_self, map_one]
  let θL : ↥(unitarySU p f F 2) →* K := θ.comp (levU hq.pos)
  let Ph : Subgroup ↥(unitarySU p f F 2) := P.comap θL
  have hKrel : ∀ B ∈ Ph, ∃ ε : F, ε * ε = 1 ∧
      (A₂ * !![0, 1; -1, 0]) * matU B = ε • (matU B * (A₂ * !![0, 1; -1, 0])) := by
    intro B hB
    have hs := hP _ hB
    obtain ⟨g', hg'GL, hg'θ⟩ := hrel (levU hq.pos B)
    have hGA : matU g' * (A : Matrix (Fin 3) (Fin 3) F) =
        (A : Matrix (Fin 3) (Fin 3) F) * (leviMat (matU B)).map h.bar := by
      have h1 : (g' : GL (Fin 3) F) * A = A * glAut φ ((levU hq.pos B : ↥(unitarySU p f F 3)) : GL (Fin 3) F) := by
        rw [hg'GL]
        group
      have h2' := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) h1
      simp only [Units.val_mul, coe_glAut] at h2'
      have hmap : (matU (levU hq.pos B)).map φ = (leviMat (matU B)).map h.bar := by
        rw [matU_levU]
        ext i j
        exact hφ _
      rw [hmap] at h2'
      exact h2'
    obtain ⟨B', c, ε, hε, hB', hg'⟩ : ∃ (B' : ↥(unitarySU p f F 2)) (c : F) (ε : F), ε * ε = 1 ∧
        matU B' = ε • matU B ∧ matU g' = c • leviMat (matU B') := by
      rcases mem_zpowers_involution ht2 hs with h0 | h0
      · have h0' : σ (θ (levU hq.pos B)) = θ (levU hq.pos B) := mul_inv_eq_one.1 h0
        rw [h0'] at hg'θ
        obtain ⟨c, -, -, hc⟩ := (theta_eq_iff h θ hθ.ker).1 hg'θ.symm
        refine ⟨B, c, 1, by simp, by simp, ?_⟩
        rw [hc, mul_scalar_eq_smul, matU_levU]
      · have h0' : σ (θ (levU hq.pos B)) = θ (dU hq) * θ (levU hq.pos B) := mul_inv_eq_iff_eq_mul.1 h0
        rw [h0'] at hg'θ
        have hd : θ (dU hq) * θ (levU hq.pos B) = θ (levU hq.pos (negI h * B)) := by
          rw [map_mul, levU_negI h hq, map_mul]
        rw [hd] at hg'θ
        obtain ⟨c, -, -, hc⟩ := (theta_eq_iff h θ hθ.ker).1 hg'θ.symm
        refine ⟨negI h * B, c, -1, by simp, ?_, ?_⟩
        · rw [matU_mul, matU_negI]
          simp
        · rw [hc, mul_scalar_eq_smul, matU_levU]
    obtain ⟨-, htw⟩ := levi_twist h.bar hALevi hm hg' hGA
    rw [hB'] at htw
    refine ⟨ε, hε, ?_⟩
    have hbj := bar_mul_jmat h B
    calc (A₂ * !![0, 1; -1, 0]) * matU B = A₂ * (!![0, 1; -1, 0] * matU B) := by rw [Matrix.mul_assoc]
      _ = A₂ * ((matU B).map h.bar * !![0, 1; -1, 0]) := by rw [hbj]
      _ = (A₂ * (matU B).map h.bar) * !![0, 1; -1, 0] := by rw [Matrix.mul_assoc]
      _ = (ε • matU B * A₂) * !![0, 1; -1, 0] := by rw [← htw]
      _ = ε • (matU B * (A₂ * !![0, 1; -1, 0])) := by
        rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc]
  have hK2 : ∀ c : F, A₂ * !![0, 1; -1, 0] ≠ c • (1 : Matrix (Fin 2) (Fin 2) F) := fun c =>
    K2_ne_scalar h h2 hALevi hAu hAA c
  let P' : Subgroup SL(2, F) := Ph.map (toSL2 h)
  have hP'solv : Group.IsSolvable ↥P' := by
    refine isSolvable_of_twisted (K := A₂ * !![0, 1; -1, 0]) hK2 P' ?_
    rintro _ ⟨B, hB, rfl⟩
    exact hKrel B hB
  have hPhsolv : Group.IsSolvable ↥Ph := by
    have hinj : Function.Injective ((toSL2 h).subgroupMap Ph) := by
      intro x y hxy
      have := congrArg Subtype.val hxy
      exact Subtype.ext (toSL2_injective h this)
    exact Group.isSolvable_of_isSolvable_injective hinj
  let ψ : ↥Ph →* ↥P := (θL.comp Ph.subtype).codRestrict P (fun B => B.2)
  have hsurj : Function.Surjective ψ := by
    intro s
    obtain ⟨B, hB⟩ := hPS s.2
    have hBP : B ∈ Ph := by
      show θL B ∈ P
      rw [show θL B = (s : K) from hB]
      exact s.2
    exact ⟨⟨B, hBP⟩, Subtype.ext hB⟩
  exact Group.isSolvable_of_surjective hsurj

theorem graph_solvable_levS (h : UnitaryFieldData p f F) (hp : p ≠ 2) (h5 : 5 ≤ p ^ f) (hq : Odd (p ^ f))
    {K : Type} [Group K] {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ)
    {σ : MulAut K} (hσ : σ * σ = 1)
    (hout : σ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner K)
    (hσt : σ (θ (dU hq)) = θ (dU hq)) (P : Subgroup K) (hPS : P ≤ levS hq θ)
    (hP : ∀ s ∈ P, σ s * s⁻¹ ∈ Subgroup.zpowers (θ (dU hq))) : Group.IsSolvable ↥P := by
  rcases involution_type h hp h5 hθ hσ with ⟨A, hAu, hAA, hrel⟩ | ⟨φ, A, hφ, hAu, hAA, hrel⟩
  · exfalso
    obtain ⟨y, hy⟩ := exists_conj_of_typeI h hθ hAu hAA hrel
    exact hout ⟨y, hy⟩
  · exact solvable_of_typeII h hq hθ hφ hAu hAA hrel hσt P hPS hP

end B3


end CFSG.GH74.KGroups.L3Eps.Uni
