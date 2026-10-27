module

public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthPatternSpLift
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCShortRoot

public section

namespace CFSG.ClassicalInvolution.RouteD.LeviModel

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply mat_elt)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Steinberg.Sp (blockMat)
open scoped MatrixGroups
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
open CFSG.ClassicalInvolution.RouteD (ker_proj_eq_center)
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
  (odd_symplectic_automorphism_semilinear_representation)

variable {F : Type} [Field F]

abbrev Mat4 (F : Type) := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F

theorem exists_semilinear_lift' [Finite F] (hodd : ringChar F ≠ 2) (h4 : 4 ≤ Nat.card F)
    {X : Type} [Group X] (ψ : StatedSp 2 F →* X) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F))
    (τ : X ≃* X) (hstab : ∀ x, τ (ψ x) ∈ ψ.range) (hstab' : ∀ x, τ.symm (ψ x) ∈ ψ.range) :
    ∃ (A : gsp 2 F) (σ : F ≃+* F), ∀ x : StatedSp 2 F,
      τ (ψ x) = ψ (conjSp 2 F A (fieldSp 2 F σ x)) := by
  classical
  have hperf : Group.IsPerfect (StatedSp 2 F) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple 2 F (by norm_num)
      (Or.inl (Or.inr h4))).1
  have hmem : ∀ y : X, y ∈ ψ.range → τ y ∈ ψ.range := by
    rintro _ ⟨x, rfl⟩
    exact hstab x
  have hmem' : ∀ y : X, y ∈ ψ.range → τ.symm y ∈ ψ.range := by
    rintro _ ⟨x, rfl⟩
    exact hstab' x
  let τC : ψ.range ≃* ψ.range :=
    { toFun := fun y => ⟨τ y, hmem y y.2⟩
      invFun := fun y => ⟨τ.symm y, hmem' y y.2⟩
      left_inv := fun y => Subtype.ext (τ.symm_apply_apply _)
      right_inv := fun y => Subtype.ext (τ.apply_symm_apply _)
      map_mul' := fun a b => Subtype.ext (map_mul τ (a : X) (b : X)) }
  obtain ⟨β, hβ, -⟩ := exists_mulEquiv_of_central_cover (π := proj 2 F) (proj_surjective)
    (ker_proj_eq_center 2) (θ := ψ.rangeRestrict) ψ.rangeRestrict_surjective
    (by rwa [MonoidHom.ker_rangeRestrict]) τC
  obtain ⟨hall, -, -⟩ := odd_symplectic_automorphism_semilinear_representation (r := 2) hodd le_rfl
  obtain ⟨A, σ, hAσ⟩ := hall β
  refine ⟨A, σ, ?_⟩
  let α : StatedSp 2 F →* StatedSp 2 F :=
    (conjSp 2 F A).toMonoidHom.comp (fieldSp 2 F σ).toMonoidHom
  have hα : ∀ x, proj 2 F (α x) = β (proj 2 F x) := fun x => by
    rw [hAσ, MulAut.mul_apply, fieldAut_proj, conjAut_proj]
    rfl
  intro x
  have := congrArg Subtype.val (hβ α hα x)
  exact this.symm

theorem fin_two_zero_ne_one : (0 : Fin 2) ≠ 1 := by decide

noncomputable def E01 (F : Type) [Field F] : Mat4 F :=
  Matrix.single (Sum.inl 0) (Sum.inl 1) 1 - Matrix.single (Sum.inr 1) (Sum.inr 0) 1

noncomputable def E10 (F : Type) [Field F] : Mat4 F :=
  Matrix.single (Sum.inl 1) (Sum.inl 0) 1 - Matrix.single (Sum.inr 0) (Sum.inr 1) 1

theorem mat_shortBlock_upper (c : F) :
    mat 2 F (shortBlock F fin_two_zero_ne_one (sl2Upper c)) = 1 + c • E01 F := by
  rw [shortBlock_sl2Upper, mat_elt]
  rfl

theorem mat_shortBlock_lower (c : F) :
    mat 2 F (shortBlock F fin_two_zero_ne_one (sl2Lower c)) = 1 + c • E10 F := by
  rw [shortBlock_sl2Lower, mat_elt]
  rfl

theorem map_E01 (σ : F ≃+* F) : (E01 F).map σ = E01 F := by
  ext a b
  simp [E01, Matrix.single_apply]

theorem map_one_add_smul (σ : F ≃+* F) (s : F) {M : Mat4 F} (hM : M.map σ = M) :
    (1 + s • M).map σ = 1 + σ s • M := by
  ext a b
  have := congrFun (congrFun hM a) b
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
    map_mul] at this ⊢
  rw [this]
  by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

theorem mat_conjSp_fieldSp (A : gsp 2 F) (σ : F ≃+* F) (x : StatedSp 2 F) :
    mat 2 F (conjSp 2 F A (fieldSp 2 F σ x)) =
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) * (mat 2 F x).map σ *
        (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) := by
  rw [mat_apply, coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp, mat_apply]

theorem sigma_eq_one (A : gsp 2 F) (σ : F ≃+* F)
    (hfix : ∀ B : SL(2, F), conjSp 2 F A (fieldSp 2 F σ (shortBlock F fin_two_zero_ne_one B)) =
      shortBlock F fin_two_zero_ne_one B) : σ = 1 := by
  set a : Mat4 F := ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) with ha
  set b : Mat4 F := (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) with hb
  have hab : a * b = 1 := by
    rw [ha, hb, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hup : ∀ s : F, a * (1 + σ s • E01 F) * b = 1 + s • E01 F := by
    intro s
    have h := congrArg (mat 2 F) (hfix (sl2Upper s))
    rw [mat_conjSp_fieldSp, mat_shortBlock_upper, ← ha, ← hb,
      map_one_add_smul σ s (map_E01 σ)] at h
    exact h
  have h1 : a * E01 F * b = E01 F := by
    have h := hup 1
    simp only [map_one, one_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hab,
      Matrix.mul_assoc] at h
    have h' : a * (E01 F * b) = E01 F := add_left_cancel h
    rwa [← Matrix.mul_assoc] at h'
  have key : ∀ s : F, σ s • E01 F = s • E01 F := by
    intro s
    have h := hup s
    have e : a * (1 + σ s • E01 F) * b = 1 + σ s • (a * E01 F * b) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hab, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_assoc]
    rw [e, h1] at h
    exact add_left_cancel h
  refine RingEquiv.ext fun s => ?_
  have := congrFun (congrFun (key s) (Sum.inl 0)) (Sum.inl 1)
  simpa [E01, Matrix.single_apply] using this

theorem shape_of_comm {a : Mat4 F} (h1 : a * E01 F = E01 F * a) (h2 : a * E10 F = E10 F * a) :
    a (Sum.inl 0) (Sum.inl 1) = 0 ∧ a (Sum.inl 0) (Sum.inr 0) = 0 ∧ a (Sum.inl 1) (Sum.inl 0) = 0 ∧
    a (Sum.inl 1) (Sum.inr 1) = 0 ∧ a (Sum.inr 0) (Sum.inl 0) = 0 ∧ a (Sum.inr 0) (Sum.inr 1) = 0 ∧
    a (Sum.inr 1) (Sum.inl 1) = 0 ∧ a (Sum.inr 1) (Sum.inr 0) = 0 ∧
    a (Sum.inl 0) (Sum.inl 0) = a (Sum.inl 1) (Sum.inl 1) ∧
    a (Sum.inr 0) (Sum.inr 0) = a (Sum.inr 1) (Sum.inr 1) ∧
    a (Sum.inl 1) (Sum.inr 0) = - a (Sum.inl 0) (Sum.inr 1) ∧
    a (Sum.inr 0) (Sum.inl 1) = - a (Sum.inr 1) (Sum.inl 0) := by
  have e := fun i j => congrFun (congrFun h1 i) j
  have f := fun i j => congrFun (congrFun h2 i) j
  have e1 := e (Sum.inl 0) (Sum.inl 1)
  have e2 := e (Sum.inl 1) (Sum.inl 1)
  have e3 := e (Sum.inr 0) (Sum.inl 1)
  have e4 := e (Sum.inr 1) (Sum.inl 1)
  have e5 := e (Sum.inl 0) (Sum.inr 0)
  have e6 := e (Sum.inl 1) (Sum.inr 0)
  have e7 := e (Sum.inr 0) (Sum.inr 0)
  have e8 := e (Sum.inr 1) (Sum.inr 0)
  have f1 := f (Sum.inl 0) (Sum.inl 0)
  have f2 := f (Sum.inr 1) (Sum.inl 0)
  have f3 := f (Sum.inl 0) (Sum.inr 1)
  have f4 := f (Sum.inr 1) (Sum.inr 1)
  simp [E01, E10, Matrix.mul_apply, Matrix.single_apply] at e1 e2 e3 e4 e5 e6 e7 e8 f1 f2 f3 f4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  exacts [f1, f3, e2, e6, e3, e7, f2, f4, e1, e8.symm, e5.symm, by linear_combination e4]

theorem formJ_mul_entry (a : Mat4 F) (i j : Fin 2 ⊕ Fin 2) :
    (aᵀ * formJ 2 F * a) i j =
      a (Sum.inl 0) i * a (Sum.inr 0) j + a (Sum.inl 1) i * a (Sum.inr 1) j -
        a (Sum.inr 0) i * a (Sum.inl 0) j - a (Sum.inr 1) i * a (Sum.inl 1) j := by
  simp [formJ, Matrix.mul_apply, Matrix.fromBlocks]
  ring

theorem dichotomy_aux {α β γ δ μ : F} (hμ : μ ≠ 0) (hA : α * γ = 0) (hB : β * δ = 0)
    (hC : α * δ + β * γ = μ) : (β = 0 ∧ γ = 0) ∨ (α = 0 ∧ δ = 0) := by
  by_cases hα : α = 0
  · right
    refine ⟨hα, ?_⟩
    have hβ : β ≠ 0 := by
      rintro rfl
      apply hμ
      rw [← hC, hα]
      ring
    exact (mul_eq_zero.mp hB).resolve_left hβ
  · left
    have hγ : γ = 0 := (mul_eq_zero.mp hA).resolve_left hα
    refine ⟨?_, hγ⟩
    have hδ : δ ≠ 0 := by
      rintro rfl
      apply hμ
      rw [← hC, hγ]
      ring
    exact (mul_eq_zero.mp hB).resolve_right hδ

theorem dichotomy_of_shape (h2 : (2 : F) ≠ 0) {a : Mat4 F} {μ : F} (hμ : μ ≠ 0)
    (hJ : aᵀ * formJ 2 F * a = μ • formJ 2 F)
    (s2 : a (Sum.inl 0) (Sum.inr 0) = 0)
    (s3 : a (Sum.inl 1) (Sum.inl 0) = 0) (s5 : a (Sum.inr 0) (Sum.inl 0) = 0)
    (s8 : a (Sum.inr 1) (Sum.inr 0) = 0)
    (s9 : a (Sum.inl 0) (Sum.inl 0) = a (Sum.inl 1) (Sum.inl 1))
    (s10 : a (Sum.inr 0) (Sum.inr 0) = a (Sum.inr 1) (Sum.inr 1))
    (s11 : a (Sum.inl 1) (Sum.inr 0) = - a (Sum.inl 0) (Sum.inr 1))
    (s12 : a (Sum.inr 0) (Sum.inl 1) = - a (Sum.inr 1) (Sum.inl 0)) :
    (a (Sum.inl 0) (Sum.inr 1) = 0 ∧ a (Sum.inr 1) (Sum.inl 0) = 0) ∨
      (a (Sum.inl 0) (Sum.inl 0) = 0 ∧ a (Sum.inr 0) (Sum.inr 0) = 0) := by
  have eA := congrFun (congrFun hJ (Sum.inl 0)) (Sum.inl 1)
  have eB := congrFun (congrFun hJ (Sum.inr 0)) (Sum.inr 1)
  have eC := congrFun (congrFun hJ (Sum.inl 0)) (Sum.inr 0)
  rw [formJ_mul_entry] at eA eB eC
  simp [formJ] at eA eB eC
  refine dichotomy_aux (α := a (Sum.inl 0) (Sum.inl 0)) (β := a (Sum.inl 0) (Sum.inr 1))
    (γ := a (Sum.inr 1) (Sum.inl 0)) (δ := a (Sum.inr 0) (Sum.inr 0)) hμ ?_ ?_ ?_
  · rw [s3, s5, s12, ← s9] at eA
    have h : (2 : F) * (a (Sum.inl 0) (Sum.inl 0) * a (Sum.inr 1) (Sum.inl 0)) = 0 := by
      linear_combination -eA
    exact (mul_eq_zero.mp h).resolve_left h2
  · rw [s2, s11, s8, ← s10] at eB
    have h : (2 : F) * (a (Sum.inl 0) (Sum.inr 1) * a (Sum.inr 0) (Sum.inr 0)) = 0 := by
      linear_combination -eB
    exact (mul_eq_zero.mp h).resolve_left h2
  · rw [s3, s5, s11] at eC
    linear_combination eC

theorem comm_of_conj_eq {a b x : Mat4 F} (hba : b * a = 1) (h : a * x * b = x) :
    a * x = x * a := by
  calc a * x = a * x * (b * a) := by rw [hba, Matrix.mul_one]
    _ = (a * x * b) * a := by simp only [Matrix.mul_assoc]
    _ = x * a := by rw [h]

theorem map_one_ringEquiv (M : Mat4 F) : M.map (1 : F ≃+* F) = M := by
  ext i j
  rfl

theorem conj_longInv_of_centralizes_shortBlock (h2 : (2 : F) ≠ 0) (A : gsp 2 F) (σ : F ≃+* F)
    (hfix : ∀ B : SL(2, F), conjSp 2 F A (fieldSp 2 F σ (shortBlock F fin_two_zero_ne_one B)) =
      shortBlock F fin_two_zero_ne_one B) :
    σ = 1 ∧ (conjSp 2 F A (longInv F 2 0) = longInv F 2 0 ∨
      conjSp 2 F A (longInv F 2 0) = longInv F 2 1) := by
  have hσ := sigma_eq_one A σ hfix
  refine ⟨hσ, ?_⟩
  subst hσ
  set a : Mat4 F := ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) with ha
  set b : Mat4 F := (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) with hb
  have hab : a * b = 1 := by
    rw [ha, hb, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hba : b * a = 1 := by
    rw [ha, hb, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcomm : ∀ B : SL(2, F), a * mat 2 F (shortBlock F fin_two_zero_ne_one B) =
      mat 2 F (shortBlock F fin_two_zero_ne_one B) * a := by
    intro B
    have h := congrArg (mat 2 F) (hfix B)
    rw [mat_conjSp_fieldSp, map_one_ringEquiv, ← ha, ← hb] at h
    exact comm_of_conj_eq hba h
  have h1 : a * E01 F = E01 F * a := by
    have h := hcomm (sl2Upper 1)
    rw [mat_shortBlock_upper] at h
    simp only [one_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact add_left_cancel h
  have h2' : a * E10 F = E10 F * a := by
    have h := hcomm (sl2Lower 1)
    rw [mat_shortBlock_lower] at h
    simp only [one_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact add_left_cancel h
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ := shape_of_comm h1 h2'
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
  have hμ' : aᵀ * formJ 2 F * a = (μ : F) • formJ 2 F := hμ
  have hd := dichotomy_of_shape (a := a) h2 μ.ne_zero hμ' s2 s3 s5 s8 s9 s10 s11 s12
  have hconj : ∀ x : StatedSp 2 F, mat 2 F (conjSp 2 F A (fieldSp 2 F 1 x)) =
      a * mat 2 F x * b := fun x => by
    rw [mat_conjSp_fieldSp, map_one_ringEquiv]
  simp only [map_one, MulAut.one_apply] at hconj
  rcases hd with ⟨hβ, hγ⟩ | ⟨hα, hδ⟩
  · left
    apply mat_injective
    have hD : a * mat 2 F (longInv F 2 0) = mat 2 F (longInv F 2 0) * a := by
      rw [mat_longInv]
      ext i j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
        simp [mem_coords, s1, s2, s3, s4, s5, s6, s7, s8, s11, s12, hβ, hγ]
    rw [hconj, hD, Matrix.mul_assoc, hab, Matrix.mul_one]
  · right
    apply mat_injective
    have hα' : a (Sum.inl 1) (Sum.inl 1) = 0 := by rw [← s9]; exact hα
    have hδ' : a (Sum.inr 1) (Sum.inr 1) = 0 := by rw [← s10]; exact hδ
    have hD : a * mat 2 F (longInv F 2 0) = mat 2 F (longInv F 2 1) * a := by
      rw [mat_longInv, mat_longInv]
      ext i j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
        simp [mem_coords, s1, s2, s3, s4, s5, s6, s7, s8, hα, hα', hδ, hδ']
    rw [hconj, hD, Matrix.mul_assoc, hab, Matrix.mul_one]

theorem shortBlock_weyl_mul_longInv_zero :
    shortBlock F fin_two_zero_ne_one (weylMat F) * longInv F 2 0 =
      longInv F 2 1 * shortBlock F fin_two_zero_ne_one (weylMat F) := by
  apply mat_injective
  rw [map_mul, map_mul, mat_shortBlock, mat_longInv, mat_longInv]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [mem_coords, blockMat, weylMat, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two]

theorem shortBlock_weyl_mul_longInv_one :
    shortBlock F fin_two_zero_ne_one (weylMat F) * longInv F 2 1 =
      longInv F 2 0 * shortBlock F fin_two_zero_ne_one (weylMat F) := by
  apply mat_injective
  rw [map_mul, map_mul, mat_shortBlock, mat_longInv, mat_longInv]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [mem_coords, blockMat, weylMat, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two]

theorem neg_one_mem_range_shortBlock :
    longInv F 2 0 * longInv F 2 1 ∈ (shortBlock F (fin_two_zero_ne_one)).range := by
  refine ⟨-1, ?_⟩
  apply mat_injective
  rw [map_mul, mat_longInv, mat_longInv, mat_shortBlock]
  ext i j
  rw [Matrix.diagonal_mul_diagonal]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [mem_coords, blockMat, Matrix.one_apply]

end CFSG.ClassicalInvolution.RouteD.LeviModel
