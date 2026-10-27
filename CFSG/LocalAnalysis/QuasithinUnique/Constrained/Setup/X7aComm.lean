module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aAut
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearPureGraph
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearGraphFieldDescent
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

open scoped commutatorElement

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ComponentClassification

section Transvection

variable {F : Type*} [Field F]

@[expose] def IsTransvection (t : SL(3, F)) : Prop :=
  ∃ v w : Fin 3 → F, v ≠ 0 ∧ w ≠ 0 ∧ w ⬝ᵥ v = 0 ∧
    (t : Matrix (Fin 3) (Fin 3) F) = 1 + Matrix.vecMulVec v w

@[expose] def standardAutSL (F : Type*) [Field F] : Subgroup (MulAut SL(3, F)) :=
  Subgroup.closure (Set.range (CatalogueBHigherLinearAction.slConjugation 3 F) ∪
    Set.range (CatalogueBHigherLinearField.slFieldAut (Fin 3) F) ∪
    {CatalogueBGraphForm.slGraphAut 3 F})

theorem isTransvection_up3 {c : F} (hc : c ≠ 0) : IsTransvection (up3 0 0 c) := by
  refine ⟨Pi.single 0 1, Pi.single 1 c, ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp at this
  · intro h
    have := congrFun h 1
    simp [hc] at this
  · simp [dotProduct, Pi.single_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [up3_coe, upMat, Matrix.vecMulVec_apply]

theorem isTransvection_conj {t : SL(3, F)} (ht : IsTransvection t) (H : GL (Fin 3) F) :
    IsTransvection (CatalogueBHigherLinearAction.slConjugation 3 F H t) := by
  obtain ⟨v, w, hv, hw, hwv, hvw⟩ := ht
  have hH : (H : Matrix (Fin 3) (Fin 3) F) * ((H⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hH' : ((H⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (H : Matrix (Fin 3) (Fin 3) F) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨(H : Matrix (Fin 3) (Fin 3) F) *ᵥ v, w ᵥ* ((H⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F),
    ?_, ?_, ?_, ?_⟩
  · intro h
    apply hv
    have := congrArg (fun x => ((H⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) h
    simpa [Matrix.mulVec_mulVec, hH', Matrix.mulVec_zero] using this
  · intro h
    apply hw
    have := congrArg (fun x => x ᵥ* (H : Matrix (Fin 3) (Fin 3) F)) h
    simpa [Matrix.vecMul_vecMul, hH', Matrix.zero_vecMul] using this
  · rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hH', Matrix.vecMul_one, hwv]
  · rw [CatalogueBHigherLinearAction.slConjugation_matrix, hvw, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, hH]
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

end Transvection

section Base

variable {F : Type*} [Field F] [CharP F 2]

theorem one_add_one_F : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero (1 : F)

@[expose] def g0Mat : Matrix (Fin 3) (Fin 3) F := !![1, 1, 0; 1, 0, 1; 1, 1, 1]

@[expose] def g0InvMat : Matrix (Fin 3) (Fin 3) F := !![1, 1, 1; 0, 1, 1; 1, 0, 1]

@[expose] def t0Mat : Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

theorem g0Mat_mul_inv : (g0Mat : Matrix (Fin 3) (Fin 3) F) * g0InvMat = 1 := by
  have h2 := one_add_one_F (F := F)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g0Mat, g0InvMat, Matrix.mul_apply, Fin.sum_univ_three, h2]

theorem det_g0Mat : (g0Mat : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  have h2 := one_add_one_F (F := F)
  simp [g0Mat, Matrix.det_fin_three]
  linear_combination (-1 : F) * h2

theorem det_t0Mat : (t0Mat : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  have h2 := one_add_one_F (F := F)
  simp [t0Mat, Matrix.det_fin_three]
  linear_combination (-1 : F) * h2

@[expose] def g0 : SL(3, F) := ⟨g0Mat, det_g0Mat⟩

@[expose] def t0 : SL(3, F) := ⟨t0Mat, det_t0Mat⟩

theorem g0_inv_coe : (((g0 : SL(3, F))⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = g0InvMat := by
  have h1 : (((g0 : SL(3, F))⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
      ((g0 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h2 : ((g0 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * g0InvMat = 1 := g0Mat_mul_inv
  calc (((g0 : SL(3, F))⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)
      = (((g0 : SL(3, F))⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
        (((g0 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * g0InvMat) := by rw [h2, Matrix.mul_one]
    _ = (((g0 : SL(3, F))⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
        ((g0 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * g0InvMat := by rw [Matrix.mul_assoc]
    _ = g0InvMat := by rw [h1, Matrix.one_mul]

theorem isTransvection_t0 : IsTransvection (t0 : SL(3, F)) := by
  have h2 := one_add_one_F (F := F)
  refine ⟨![1, 1, 0], ![1, 1, 0], ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp at this
  · intro h
    have := congrFun h 0
    simp at this
  · simp [dotProduct, Fin.sum_univ_three, h2]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [t0, t0Mat, h2]

theorem graph_base : CatalogueBGraphForm.slGraphAut 3 F (g0 : SL(3, F)) * (g0 : SL(3, F))⁻¹ =
    t0 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, CatalogueBGraphForm.slGraphAut_matrix, g0_inv_coe]
  have h2 := one_add_one_F (F := F)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [t0, t0Mat, g0InvMat, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, h2]

theorem graphField_base (σ : F ≃+* F) :
    (CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ * CatalogueBGraphForm.slGraphAut 3 F)
        (g0 : SL(3, F)) * (g0 : SL(3, F))⁻¹ = t0 := by
  have hfix : CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ
      (CatalogueBGraphForm.slGraphAut 3 F (g0 : SL(3, F))) =
        CatalogueBGraphForm.slGraphAut 3 F (g0 : SL(3, F)) := by
    apply Subtype.ext
    ext i j
    show σ ((CatalogueBGraphForm.slGraphAut 3 F (g0 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) i j) = _
    rw [CatalogueBGraphForm.slGraphAut_matrix, g0_inv_coe]
    fin_cases i <;> fin_cases j <;> simp [g0InvMat]
  rw [MulAut.mul_apply, hfix]
  exact graph_base

theorem field_base {σ : F ≃+* F} (hσ : σ ≠ 1) :
    ∃ g t : SL(3, F), IsTransvection t ∧
      CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ g * g⁻¹ = t := by
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra h
    push Not at h
    exact hσ (RingEquiv.ext h)
  refine ⟨up3 0 0 x, up3 0 0 (σ x + x), isTransvection_up3 ?_, ?_⟩
  · intro h
    exact hx (by
      have : σ x = -x := eq_neg_of_add_eq_zero_left h
      rw [this, CharTwo.neg_eq])
  · have h1 : CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ (up3 0 0 x) = up3 0 0 (σ x) := by
      apply Subtype.ext
      ext i j
      show σ ((up3 0 0 x : Matrix (Fin 3) (Fin 3) F) i j) = _
      fin_cases i <;> fin_cases j <;> simp [up3_coe, upMat]
    rw [h1, up3_inv, up3_mul]
    congr 1 <;> simp

end Base

section Main

variable {F : Type} [Field F] [CharP F 2] [Finite F]

omit [CharP F 2] [Finite F] in
theorem conj_step {ψ₀ : MulAut SL(3, F)} (hψ₀ : ψ₀ ∈ standardAutSL F) (H : GL (Fin 3) F)
    {g₀ t₀ : SL(3, F)} (ht₀ : IsTransvection t₀) (h : ψ₀ g₀ * g₀⁻¹ = t₀) :
    ∃ (ψ : MulAut SL(3, F)) (g t : SL(3, F)), ψ ∈ standardAutSL F ∧
      ψ = CatalogueBHigherLinearAction.slConjugation 3 F H * ψ₀ *
        CatalogueBHigherLinearAction.slConjugation 3 F H⁻¹ ∧
      IsTransvection t ∧ ψ g * g⁻¹ = t := by
  have hmem : ∀ K : GL (Fin 3) F, CatalogueBHigherLinearAction.slConjugation 3 F K ∈
      standardAutSL F := fun K => Subgroup.subset_closure (Or.inl (Or.inl ⟨K, rfl⟩))
  refine ⟨_, CatalogueBHigherLinearAction.slConjugation 3 F H g₀,
    CatalogueBHigherLinearAction.slConjugation 3 F H t₀,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hmem H) hψ₀) (hmem H⁻¹), rfl,
    isTransvection_conj ht₀ H, ?_⟩
  have e1 : CatalogueBHigherLinearAction.slConjugation 3 F H⁻¹
      (CatalogueBHigherLinearAction.slConjugation 3 F H g₀) = g₀ := by
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  show CatalogueBHigherLinearAction.slConjugation 3 F H (ψ₀
      (CatalogueBHigherLinearAction.slConjugation 3 F H⁻¹
        (CatalogueBHigherLinearAction.slConjugation 3 F H g₀))) *
      (CatalogueBHigherLinearAction.slConjugation 3 F H g₀)⁻¹ =
        CatalogueBHigherLinearAction.slConjugation 3 F H t₀
  rw [e1, ← h, map_mul, map_inv]

omit [CharP F 2] [Finite F] in
theorem descendAut_conj_step (ψ₀ : MulAut SL(3, F)) (H : GL (Fin 3) F) :
    descendAut 3 F (CatalogueBHigherLinearAction.slConjugation 3 F H * ψ₀ *
        CatalogueBHigherLinearAction.slConjugation 3 F H⁻¹) =
      conjAut 3 F H * descendAut 3 F ψ₀ * (conjAut 3 F H)⁻¹ := by
  rw [map_mul, map_mul]
  have : descendAut 3 F (CatalogueBHigherLinearAction.slConjugation 3 F H⁻¹) =
      (conjAut 3 F H)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [this]
  rfl

theorem outer_involution_transvection_commutator {f : ℕ} (hf : 2 ≤ f) (hF : Nat.card F = 2 ^ f)
    (α : MulAut (projectiveSL 3 F)) (hα : α * α = 1)
    (hout : α ∉ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range) :
    ∃ (ψ : MulAut SL(3, F)) (g t : SL(3, F)), ψ ∈ standardAutSL F ∧ descendAut 3 F ψ = α ∧
      IsTransvection t ∧ ψ g * g⁻¹ = t := by
  have hf1 : 1 ≤ f := by omega
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, hαeq⟩ := hgen α
  have hmemF : ∀ τ : F ≃+* F, CatalogueBHigherLinearField.slFieldAut (Fin 3) F τ ∈
      standardAutSL F := fun τ => Subgroup.subset_closure (Or.inl (Or.inr ⟨τ, rfl⟩))
  have hmemG : CatalogueBGraphForm.slGraphAut 3 F ∈ standardAutSL F :=
    Subgroup.subset_closure (Or.inr rfl)
  interval_cases ε
  · rw [pow_zero, mul_one] at hαeq
    by_cases hσ : σ = 1
    · exfalso
      apply hout
      rw [hαeq, hσ, map_one, mul_one]
      refine mem_inner_of_sq_conjAut ?_
      rw [hσ, map_one, mul_one] at hαeq
      rw [← hαeq]
      exact hα
    · have hsq : (conjAut 3 F A * fieldAut 3 F σ) ^ 2 = 1 := by rw [pow_two, ← hαeq]; exact hα
      obtain ⟨-, -, H, hH⟩ := even_linear_field_involution_descent hf1 hF le_rfl A σ hσ hsq
      obtain ⟨g₀, t₀, ht₀, h₀⟩ := field_base hσ
      obtain ⟨ψ, g, t, hψ, hψeq, ht, hgt⟩ := conj_step (hmemF σ) H ht₀ h₀
      refine ⟨ψ, g, t, hψ, ?_, ht, hgt⟩
      rw [hψeq, descendAut_conj_step, hαeq, hH]
      rfl
  · rw [pow_one] at hαeq
    by_cases hσ : σ = 1
    · have hsq : (conjAut 3 F A * dualAut 3 F) ^ 2 = 1 := by
        rw [hσ, map_one, mul_one] at hαeq
        rw [pow_two, ← hαeq]
        exact hα
      obtain ⟨-, ⟨H, C, -, hconj, hcase⟩, -⟩ :=
        even_linear_pure_graph_involution_normal_forms hf1 hF le_rfl A hsq
      have hC : (C : Matrix (Fin 3) (Fin 3) F) = 1 := by
        rcases hcase with ⟨h1, -⟩ | ⟨r, hr, -⟩
        · exact h1
        · omega
      have hC1 : C = 1 := Units.ext hC
      rw [hC1, map_one, one_mul] at hconj
      obtain ⟨ψ, g, t, hψ, hψeq, ht, hgt⟩ :=
        conj_step hmemG H (isTransvection_t0 (F := F)) (graph_base (F := F))
      refine ⟨ψ, g, t, hψ, ?_, ht, hgt⟩
      rw [hψeq, descendAut_conj_step, hαeq, hσ, map_one, mul_one, hconj]
      rfl
    · have hsq : (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) ^ 2 = 1 := by
        rw [pow_two, ← hαeq]
        exact hα
      obtain ⟨-, -, H, hH⟩ := linear_graph_field_involution_descent Nat.prime_two hf1 hF le_rfl
        A σ hσ hsq
      obtain ⟨ψ, g, t, hψ, hψeq, ht, hgt⟩ := conj_step
        (Subgroup.mul_mem _ (hmemF σ) hmemG) H (isTransvection_t0 (F := F)) (graphField_base σ)
      refine ⟨ψ, g, t, hψ, ?_, ht, hgt⟩
      rw [hψeq, descendAut_conj_step, hαeq, hH, map_mul]
      rfl

end Main

section Intertw

variable {F : Type*} [Field F] {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

@[expose] def Intertwines (ρ : Representation (ZMod 2) SL(3, F) U) (b : U ≃ₗ[ZMod 2] U)
    (x y : SL(3, F)) : Prop := ∀ u, b (ρ x u) = ρ y (b u)

theorem Intertwines.mul {ρ : Representation (ZMod 2) SL(3, F) U} {b : U ≃ₗ[ZMod 2] U}
    {x y x' y' : SL(3, F)} (h : Intertwines ρ b x y) (h' : Intertwines ρ b x' y') :
    Intertwines ρ b (x * x') (y * y') := by
  intro u
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h, h']

theorem Intertwines.inv {ρ : Representation (ZMod 2) SL(3, F) U} {b : U ≃ₗ[ZMod 2] U}
    {x y : SL(3, F)} (h : Intertwines ρ b x y) : Intertwines ρ b x⁻¹ y⁻¹ := by
  intro u
  have h1 : b u = ρ y (b (ρ x⁻¹ u)) := by
    rw [← h]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [h1, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

end Intertw

section Rep

variable {F : Type} [Field F] [CharP F 2] [Finite F]
  {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]

theorem comm_mul_central {G : Type*} [Group G] (a c z w : G) (hz : ∀ g, g * z = z * g)
    (hw : ∀ g, g * w = w * g) :
    (a * z) * (c * w) * (a * z)⁻¹ * (c * w)⁻¹ = a * c * a⁻¹ * c⁻¹ := by
  simp only [_root_.mul_inv_rev]
  calc a * z * (c * w) * (z⁻¹ * a⁻¹) * (w⁻¹ * c⁻¹)
      = a * (z * c) * w * (z⁻¹ * a⁻¹) * (w⁻¹ * c⁻¹) := by group
    _ = a * (c * z) * w * (z⁻¹ * a⁻¹) * (w⁻¹ * c⁻¹) := by rw [← hz c]
    _ = a * c * (z * w * z⁻¹) * a⁻¹ * (w⁻¹ * c⁻¹) := by group
    _ = a * c * w * a⁻¹ * (w⁻¹ * c⁻¹) := by rw [← hz w]; group
    _ = a * c * (w * a⁻¹ * w⁻¹) * c⁻¹ := by group
    _ = a * c * a⁻¹ * c⁻¹ := by rw [← hw a⁻¹]; group

omit [CharP F 2] [Finite F] [Finite U] in
theorem intertwines_psi (ρ : Representation (ZMod 2) SL(3, F) U)
    (α : MulAut (projectiveSL 3 F)) (ψ : MulAut SL(3, F)) (hψ : descendAut 3 F ψ = α)
    (b : U ≃ₗ[ZMod 2] U)
    (hb : ∀ x : SL(3, F), ∃ y : SL(3, F), Intertwines ρ b x y ∧ proj 3 F y = α (proj 3 F x)) :
    ∀ x : SL(3, F), Intertwines ρ b x (ψ x) := by
  classical
  let T : Subgroup SL(3, F) :=
    { carrier := {x | Intertwines ρ b x (ψ x)}
      one_mem' := by
        intro u
        simp only [map_one, Module.End.one_apply]
      mul_mem' := fun {x y} hx hy => by
        have := Intertwines.mul hx hy
        rwa [← map_mul] at this
      inv_mem' := fun {x} hx => by
        have := Intertwines.inv hx
        rwa [← map_inv] at this }
  have hcomm : ∀ u v : SL(3, F), ⁅u, v⁆ ∈ T := by
    intro u v
    obtain ⟨yu, hu, hπu⟩ := hb u
    obtain ⟨yv, hv, hπv⟩ := hb v
    have hzu : (ψ u)⁻¹ * yu ∈ scalars 3 F := by
      rw [← proj_eq_proj_iff, hπu, ← hψ, descendAut_proj]
    have hzv : (ψ v)⁻¹ * yv ∈ scalars 3 F := by
      rw [← proj_eq_proj_iff, hπv, ← hψ, descendAut_proj]
    have hcu : ∀ g : SL(3, F), g * ((ψ u)⁻¹ * yu) = ((ψ u)⁻¹ * yu) * g := fun g =>
      Subgroup.mem_center_iff.mp (scalars_le_center 3 F hzu) g
    have hcv : ∀ g : SL(3, F), g * ((ψ v)⁻¹ * yv) = ((ψ v)⁻¹ * yv) * g := fun g =>
      Subgroup.mem_center_iff.mp (scalars_le_center 3 F hzv) g
    have h1 := ((hu.mul hv).mul hu.inv).mul hv.inv
    have h2 : yu * yv * yu⁻¹ * yv⁻¹ = ψ (u * v * u⁻¹ * v⁻¹) := by
      have e : ∀ (a z : SL(3, F)), a * (a⁻¹ * z) = z := fun a z => mul_inv_cancel_left a z
      have hyu : yu = ψ u * ((ψ u)⁻¹ * yu) := (e _ _).symm
      have hyv : yv = ψ v * ((ψ v)⁻¹ * yv) := (e _ _).symm
      rw [hyu, hyv]
      rw [comm_mul_central _ _ _ _ hcu hcv]
      simp [map_mul, map_inv]
    rw [h2] at h1
    exact h1
  have hperf : Group.IsPerfect SL(3, F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := F) (n := 3) le_rfl
  have hTtop : T = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := SL(3, F)), commutator_def]
    exact Subgroup.commutator_le.mpr fun u _ v _ => hcomm u v
  intro x
  have : x ∈ T := by rw [hTtop]; exact Subgroup.mem_top x
  exact this

omit [CharP F 2] [Finite F] in
theorem finrank_range_mul_sub_one_le (X Y : U →ₗ[ZMod 2] U) :
    Module.finrank (ZMod 2) (LinearMap.range (X * Y - 1)) ≤
      Module.finrank (ZMod 2) (LinearMap.range (X - 1)) +
        Module.finrank (ZMod 2) (LinearMap.range (Y - 1)) := by
  have hfin : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  have hle : LinearMap.range (X * Y - 1) ≤ LinearMap.range (X - 1) ⊔ LinearMap.range (Y - 1) := by
    rintro _ ⟨u, rfl⟩
    refine Submodule.mem_sup.mpr ⟨(X - 1) (Y u), ⟨Y u, rfl⟩, Y u - u, ⟨u, rfl⟩, ?_⟩
    simp [Module.End.mul_apply]
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

omit [CharP F 2] [Finite F] [Finite U] in
theorem finrank_range_conj (e : U ≃ₗ[ZMod 2] U) (T : U →ₗ[ZMod 2] U) :
    Module.finrank (ZMod 2) (LinearMap.range
        (e.toLinearMap ∘ₗ T ∘ₗ e.symm.toLinearMap)) =
      Module.finrank (ZMod 2) (LinearMap.range T) := by
  rw [LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ e.symm.range]
  exact LinearEquiv.finrank_map_eq e _

omit [CharP F 2] [Finite F] [Finite U] in
theorem finrank_range_symm_sub_one (b : U ≃ₗ[ZMod 2] U) :
    Module.finrank (ZMod 2) (LinearMap.range (b.symm.toLinearMap - 1)) =
      Module.finrank (ZMod 2) (LinearMap.range (b.toLinearMap - 1)) := by
  have h1 : b.symm.toLinearMap - 1 = b.symm.toLinearMap ∘ₗ (-(b.toLinearMap - 1)) := by
    refine LinearMap.ext fun u => ?_
    simp
  rw [h1, LinearMap.range_comp, LinearMap.range_neg]
  exact LinearEquiv.finrank_map_eq b.symm _

@[expose] def repEquiv (ρ : Representation (ZMod 2) SL(3, F) U) (g : SL(3, F)) : U ≃ₗ[ZMod 2] U :=
  LinearEquiv.ofLinearMap (ρ g) (ρ g⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

omit [CharP F 2] [Finite F] in
theorem commutator_rank_bound (ρ : Representation (ZMod 2) SL(3, F) U)
    (α : MulAut (projectiveSL 3 F)) (ψ : MulAut SL(3, F)) (hψ : descendAut 3 F ψ = α)
    (b : U ≃ₗ[ZMod 2] U)
    (hb : ∀ x : SL(3, F), ∃ y : SL(3, F), Intertwines ρ b x y ∧ proj 3 F y = α (proj 3 F x))
    (g t : SL(3, F)) (hgt : ψ g * g⁻¹ = t) :
    (∀ x : SL(3, F), ∀ u, b (ρ x u) = ρ (ψ x) (b u)) ∧
      (∀ u, b (ρ g (b.symm (ρ g⁻¹ u))) = ρ t u) ∧
      Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤
        2 * Module.finrank (ZMod 2) (LinearMap.range (b.toLinearMap - 1)) := by
  have hint := intertwines_psi ρ α ψ hψ b hb
  have hcomm : ∀ u, b (ρ g (b.symm (ρ g⁻¹ u))) = ρ t u := by
    intro u
    rw [hint g, LinearEquiv.apply_symm_apply, ← hgt, map_mul, Module.End.mul_apply]
  refine ⟨hint, hcomm, ?_⟩
  let Y : U →ₗ[ZMod 2] U := ρ g * b.symm.toLinearMap * ρ g⁻¹
  have hXY : ρ t = b.toLinearMap * Y := by
    refine LinearMap.ext fun u => ?_
    rw [← hcomm u]
    rfl
  have hYconj : Y - 1 = (repEquiv ρ g).toLinearMap ∘ₗ (b.symm.toLinearMap - 1) ∘ₗ
      (repEquiv ρ g).symm.toLinearMap := by
    refine LinearMap.ext fun u => ?_
    have h1 : ρ g (ρ g⁻¹ u) = u := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    simp [Y, repEquiv, Module.End.mul_apply, h1]
  calc Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1))
      = Module.finrank (ZMod 2) (LinearMap.range (b.toLinearMap * Y - 1)) := by rw [hXY]
    _ ≤ Module.finrank (ZMod 2) (LinearMap.range (b.toLinearMap - 1)) +
          Module.finrank (ZMod 2) (LinearMap.range (Y - 1)) :=
        finrank_range_mul_sub_one_le _ _
    _ = 2 * Module.finrank (ZMod 2) (LinearMap.range (b.toLinearMap - 1)) := by
        rw [hYconj, finrank_range_conj, finrank_range_symm_sub_one, two_mul]

theorem outer_involutions_have_transvection_commutators {f : ℕ} (hf : 2 ≤ f)
    (hF : Nat.card F = 2 ^ f) (α : MulAut (projectiveSL 3 F)) (hα : α * α = 1)
    (hout : α ∉ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range) :
    ∃ (ψ : MulAut SL(3, F)) (g t : SL(3, F)), ψ ∈ standardAutSL F ∧ descendAut 3 F ψ = α ∧
      IsTransvection t ∧ ψ g * g⁻¹ = t ∧
      ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
        (ρ : Representation (ZMod 2) SL(3, F) W) (b : W ≃ₗ[ZMod 2] W),
        (∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F) →
        (∀ x : SL(3, F), ∃ y : SL(3, F), Intertwines ρ b x y ∧ proj 3 F y = α (proj 3 F x)) →
        (∀ w, b (ρ g (b.symm (ρ g⁻¹ w))) = ρ t w) ∧
          Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤
            2 * Module.finrank (ZMod 2) (LinearMap.range (b.toLinearMap - 1)) := by
  obtain ⟨ψ, g, t, hψ, hψα, ht, hgt⟩ := outer_involution_transvection_commutator hf hF α hα hout
  refine ⟨ψ, g, t, hψ, hψα, ht, hgt, fun W _ _ _ ρ b _ hb => ?_⟩
  obtain ⟨-, hcomm, hrank⟩ := commutator_rank_bound ρ α ψ hψα b hb g t hgt
  exact ⟨hcomm, hrank⟩

end Rep

end CFSG.QuasithinUnique.Setup.X7a
