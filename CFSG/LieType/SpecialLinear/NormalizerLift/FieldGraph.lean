module

public import CFSG.LieType.SpecialLinear.NormalizerLift.Lift
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {H : Type*} [Group H]

omit [Finite F] [CharP F 2] in
theorem slConjugation_toGL (g h : SpecialLinearGroup (Fin n) F) :
    CatalogueBHigherLinearAction.slConjugation n F (SpecialLinearGroup.toGL g) h =
      g * h * g⁻¹ := by
  apply SpecialLinearGroup.toGL_injective
  rw [CatalogueBHigherLinearAction.toGL_slConjugation, map_mul, map_mul, map_inv]

omit [Finite F] [CharP F 2] in
theorem descendAut_injective (hn : 3 ≤ n) :
    Function.Injective (LinearFlag.descendAut n F) := by
  intro Φ Ψ h
  apply eq_of_comp_proj_eq (π := LinearFlag.proj n F)
    (show (LinearFlag.proj n F).ker ≤ scalars n F from (LinearFlag.ker_proj n F).le) hn
  intro g
  have hg := congrArg
    (fun φ : MulAut (LinearFlag.projectiveSL n F) => φ (LinearFlag.proj n F g)) h
  simpa only [LinearFlag.descendAut_proj] using hg

omit [Finite F] [CharP F 2] in
theorem slFieldAut_mul_slConjugation (σ : F ≃+* F) (A : GL (Fin n) F) :
    CatalogueBHigherLinearField.slFieldAut (Fin n) F σ *
        CatalogueBHigherLinearAction.slConjugation n F A =
      CatalogueBHigherLinearAction.slConjugation n F
          (CatalogueBHigherLinearField.glFieldEquiv (Fin n) σ A) *
        CatalogueBHigherLinearField.slFieldAut (Fin n) F σ := by
  have h := LinearFlag.slField_mul_slConjugation_mul_inv (K := F) (n := n) σ A
  calc CatalogueBHigherLinearField.slFieldAut (Fin n) F σ *
        CatalogueBHigherLinearAction.slConjugation n F A
      = (CatalogueBHigherLinearField.slFieldAut (Fin n) F σ *
          CatalogueBHigherLinearAction.slConjugation n F A *
          (CatalogueBHigherLinearField.slFieldAut (Fin n) F σ)⁻¹) *
          CatalogueBHigherLinearField.slFieldAut (Fin n) F σ := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = _ := by rw [h]

omit [Finite F] [CharP F 2] in
theorem slGraphAut_mul_slConjugation (A : GL (Fin n) F) :
    CatalogueBGraphForm.slGraphAut n F *
        CatalogueBHigherLinearAction.slConjugation n F A =
      CatalogueBHigherLinearAction.slConjugation n F
          (GeneralLinearGroup.inverseTranspose A) *
        CatalogueBGraphForm.slGraphAut n F := by
  have h := LinearFlag.slGraph_mul_slConjugation_mul_slGraph (K := F) (n := n) A
  have hδ : CatalogueBGraphForm.slGraphAut n F * CatalogueBGraphForm.slGraphAut n F = 1 :=
    LinearFlag.slGraph_mul_slGraph (K := F) (n := n)
  calc CatalogueBGraphForm.slGraphAut n F *
        CatalogueBHigherLinearAction.slConjugation n F A
      = (CatalogueBGraphForm.slGraphAut n F *
          CatalogueBHigherLinearAction.slConjugation n F A *
          CatalogueBGraphForm.slGraphAut n F) *
          CatalogueBGraphForm.slGraphAut n F := by
        rw [mul_assoc, hδ, mul_one]
    _ = _ := by rw [h]

omit [Finite F] [CharP F 2] in
theorem exists_conjAut_fieldAut_dualAut_mul (A : GL (Fin n) F) (σ : F ≃+* F) (ε : ℕ)
    (B : GL (Fin n) F) (τ : F ≃+* F) (η : ℕ) (hε : ε ≤ 1) (hη : η ≤ 1) :
    ∃ C : GL (Fin n) F,
      (LinearFlag.conjAut n F A * LinearFlag.fieldAut n F σ *
          LinearFlag.dualAut n F ^ ε) *
        (LinearFlag.conjAut n F B * LinearFlag.fieldAut n F τ *
          LinearFlag.dualAut n F ^ η) =
      LinearFlag.conjAut n F C * LinearFlag.fieldAut n F (σ * τ) *
        LinearFlag.dualAut n F ^ ((ε + η) % 2) := by
  have hδδ : LinearFlag.dualAut n F * LinearFlag.dualAut n F = 1 := by
    obtain ⟨-, -, -, hdd, -⟩ := LinearFlag.standard_automorphism_transport (n := n) (K := F)
    exact hdd
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl <;>
    rcases (show η = 0 ∨ η = 1 by omega) with rfl | rfl
  · refine ⟨A * GeneralLinearGroup.map (σ : F →+* F) B, ?_⟩
    simpa only [pow_zero, mul_one, Nat.add_zero, Nat.zero_add, Nat.reduceMod] using
      LinearFlag.conjAut_mul_fieldAut_mul (n := n) (K := F) A B σ τ
  · refine ⟨A * GeneralLinearGroup.map (σ : F →+* F) B, ?_⟩
    calc LinearFlag.conjAut n F A * LinearFlag.fieldAut n F σ *
          (LinearFlag.conjAut n F B * LinearFlag.fieldAut n F τ * LinearFlag.dualAut n F)
        = (LinearFlag.conjAut n F A * LinearFlag.fieldAut n F σ *
            (LinearFlag.conjAut n F B * LinearFlag.fieldAut n F τ)) *
              LinearFlag.dualAut n F := by group
      _ = LinearFlag.conjAut n F (A * GeneralLinearGroup.map (σ : F →+* F) B) *
            LinearFlag.fieldAut n F (σ * τ) * LinearFlag.dualAut n F ^ 1 := by
          rw [LinearFlag.conjAut_mul_fieldAut_mul, pow_one]
  · refine ⟨A * GeneralLinearGroup.map (σ : F →+* F)
      (GeneralLinearGroup.inverseTranspose B), ?_⟩
    calc (LinearFlag.conjAut n F A * LinearFlag.fieldAut n F σ * LinearFlag.dualAut n F) *
          (LinearFlag.conjAut n F B * LinearFlag.fieldAut n F τ)
        = LinearFlag.conjAut n F A * LinearFlag.fieldAut n F σ *
            (LinearFlag.dualAut n F *
              (LinearFlag.conjAut n F B * LinearFlag.fieldAut n F τ)) := by group
      _ = LinearFlag.conjAut n F A * LinearFlag.fieldAut n F σ *
            ((LinearFlag.dualAut n F * LinearFlag.conjAut n F B) *
              LinearFlag.fieldAut n F τ) := by group
      _ = LinearFlag.conjAut n F A * LinearFlag.fieldAut n F σ *
            ((LinearFlag.conjAut n F (GeneralLinearGroup.inverseTranspose B) *
              LinearFlag.dualAut n F) * LinearFlag.fieldAut n F τ) := by
          rw [LinearFlag.dualAut_mul_conjAut]
      _ = LinearFlag.conjAut n F A * LinearFlag.fieldAut n F σ *
            (LinearFlag.conjAut n F (GeneralLinearGroup.inverseTranspose B) *
              (LinearFlag.dualAut n F * LinearFlag.fieldAut n F τ)) := by group
      _ = LinearFlag.conjAut n F A * LinearFlag.fieldAut n F σ *
            (LinearFlag.conjAut n F (GeneralLinearGroup.inverseTranspose B) *
              (LinearFlag.fieldAut n F τ * LinearFlag.dualAut n F)) := by
          rw [LinearFlag.dualAut_mul_fieldAut]
      _ = ((LinearFlag.conjAut n F A * LinearFlag.fieldAut n F σ) *
            (LinearFlag.conjAut n F (GeneralLinearGroup.inverseTranspose B) *
              LinearFlag.fieldAut n F τ)) * LinearFlag.dualAut n F := by group
      _ = LinearFlag.conjAut n F (A * GeneralLinearGroup.map (σ : F →+* F)
            (GeneralLinearGroup.inverseTranspose B)) * LinearFlag.fieldAut n F (σ * τ) *
              LinearFlag.dualAut n F ^ 1 := by
          rw [LinearFlag.conjAut_mul_fieldAut_mul, pow_one]
  · refine ⟨A * GeneralLinearGroup.map (σ : F →+* F)
      (GeneralLinearGroup.inverseTranspose B), ?_⟩
    calc (LinearFlag.conjAut n F A * LinearFlag.fieldAut n F σ * LinearFlag.dualAut n F) *
          (LinearFlag.conjAut n F B * LinearFlag.fieldAut n F τ * LinearFlag.dualAut n F)
        = ((LinearFlag.conjAut n F A * LinearFlag.fieldAut n F σ) *
            (LinearFlag.dualAut n F *
              (LinearFlag.conjAut n F B * LinearFlag.fieldAut n F τ))) *
              LinearFlag.dualAut n F := by group
      _ = ((LinearFlag.conjAut n F A * LinearFlag.fieldAut n F σ) *
            ((LinearFlag.dualAut n F * LinearFlag.conjAut n F B) *
              LinearFlag.fieldAut n F τ)) * LinearFlag.dualAut n F := by group
      _ = ((LinearFlag.conjAut n F A * LinearFlag.fieldAut n F σ) *
            ((LinearFlag.conjAut n F (GeneralLinearGroup.inverseTranspose B) *
              LinearFlag.dualAut n F) * LinearFlag.fieldAut n F τ)) *
              LinearFlag.dualAut n F := by
          rw [LinearFlag.dualAut_mul_conjAut]
      _ = ((LinearFlag.conjAut n F A * LinearFlag.fieldAut n F σ) *
            (LinearFlag.conjAut n F (GeneralLinearGroup.inverseTranspose B) *
              (LinearFlag.dualAut n F * LinearFlag.fieldAut n F τ))) *
              LinearFlag.dualAut n F := by group
      _ = ((LinearFlag.conjAut n F A * LinearFlag.fieldAut n F σ) *
            (LinearFlag.conjAut n F (GeneralLinearGroup.inverseTranspose B) *
              (LinearFlag.fieldAut n F τ * LinearFlag.dualAut n F))) *
              LinearFlag.dualAut n F := by
          rw [LinearFlag.dualAut_mul_fieldAut]
      _ = ((LinearFlag.conjAut n F A * LinearFlag.fieldAut n F σ) *
            (LinearFlag.conjAut n F (GeneralLinearGroup.inverseTranspose B) *
              LinearFlag.fieldAut n F τ)) *
                (LinearFlag.dualAut n F * LinearFlag.dualAut n F) := by group
      _ = LinearFlag.conjAut n F (A * GeneralLinearGroup.map (σ : F →+* F)
            (GeneralLinearGroup.inverseTranspose B)) * LinearFlag.fieldAut n F (σ * τ) *
              LinearFlag.dualAut n F ^ 0 := by
          rw [hδδ, mul_one, LinearFlag.conjAut_mul_fieldAut_mul, pow_zero, mul_one]

omit [CharP F 2] in
theorem conjAut_fieldAut_dualAut_unique (hn : 3 ≤ n)
    {A A' : GL (Fin n) F} {σ σ' : F ≃+* F} {ε ε' : ℕ} (hε : ε ≤ 1) (hε' : ε' ≤ 1)
    (h : LinearFlag.conjAut n F A * LinearFlag.fieldAut n F σ *
          LinearFlag.dualAut n F ^ ε =
        LinearFlag.conjAut n F A' * LinearFlag.fieldAut n F σ' *
          LinearFlag.dualAut n F ^ ε') :
    σ = σ' ∧ ε = ε' :=
  ProjectivePlane.standard_form_unique hn hε hε' h

omit [CharP F 2] in
theorem stdAut_field_graph_unique (hn : 3 ≤ n)
    {A A' : GL (Fin n) F} {σ σ' : F ≃+* F} {ε ε' : ℕ} (hε : ε ≤ 1) (hε' : ε' ≤ 1)
    (h : CFSG.QuasithinUnique.K1.stdAut A σ ε =
      CFSG.QuasithinUnique.K1.stdAut A' σ' ε') :
    σ = σ' ∧ ε = ε' := by
  apply conjAut_fieldAut_dualAut_unique hn hε hε'
  have hdesc := congrArg (LinearFlag.descendAut n F) h
  simpa only [CFSG.QuasithinUnique.K1.descendAut_stdAut] using hdesc

omit [Finite F] [CharP F 2] in
theorem exists_stdAut_mul (hn : 3 ≤ n) (A₁ : GL (Fin n) F) (σ₁ : F ≃+* F) (ε₁ : ℕ)
    (A₂ : GL (Fin n) F) (σ₂ : F ≃+* F) (ε₂ : ℕ) (hε₁ : ε₁ ≤ 1) (hε₂ : ε₂ ≤ 1) :
    ∃ B : GL (Fin n) F,
      CFSG.QuasithinUnique.K1.stdAut A₁ σ₁ ε₁ *
          CFSG.QuasithinUnique.K1.stdAut A₂ σ₂ ε₂ =
        CFSG.QuasithinUnique.K1.stdAut B (σ₁ * σ₂) ((ε₁ + ε₂) % 2) := by
  obtain ⟨C, hC⟩ := exists_conjAut_fieldAut_dualAut_mul (n := n) (F := F)
    A₁ σ₁ ε₁ A₂ σ₂ ε₂ hε₁ hε₂
  refine ⟨C, ?_⟩
  apply descendAut_injective (n := n) (F := F) hn
  rw [map_mul, CFSG.QuasithinUnique.K1.descendAut_stdAut,
    CFSG.QuasithinUnique.K1.descendAut_stdAut,
    CFSG.QuasithinUnique.K1.descendAut_stdAut]
  exact hC

section FieldGraphParts

variable (π : SpecialLinearGroup (Fin n) F →* H)

omit [CharP F 2] in
theorem stdAut_stdData_one (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n) :
    CFSG.QuasithinUnique.K1.stdAut (stdData π hker hn 1).1
      (stdData π hker hn 1).2.1 (stdData π hker hn 1).2.2 = 1 := by
  apply eq_of_comp_proj_eq (π := π) hker hn
  intro g
  rw [← stdData_spec]
  simp

omit [CharP F 2] in
theorem stdData_one_eps (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n) :
    (stdData π hker hn 1).2.2 = 0 := by
  have h1 := stdAut_stdData_one π hker hn
  have h2 : CFSG.QuasithinUnique.K1.stdAut (1 : GL (Fin n) F) (1 : F ≃+* F) 0 = 1 := by
    simp [CFSG.QuasithinUnique.K1.stdAut]
  exact (stdAut_field_graph_unique hn (stdData_eps_le_one π hker hn 1) (by norm_num)
    (h1.trans h2.symm)).2

omit [CharP F 2] in
theorem stdData_one_field (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n) :
    (stdData π hker hn 1).2.1 = 1 := by
  have h1 := stdAut_stdData_one π hker hn
  have h2 : CFSG.QuasithinUnique.K1.stdAut (1 : GL (Fin n) F) (1 : F ≃+* F) 0 = 1 := by
    simp [CFSG.QuasithinUnique.K1.stdAut]
  exact (stdAut_field_graph_unique hn (stdData_eps_le_one π hker hn 1) (by norm_num)
    (h1.trans h2.symm)).1

@[expose] noncomputable def fieldPart (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n) :
    rangeNormalizer π →* (F ≃+* F) where
  toFun h := (stdData π hker hn h).2.1
  map_one' := stdData_one_field π hker hn
  map_mul' h₁ h₂ := by
    obtain ⟨C, hC⟩ := exists_stdAut_mul hn
      (stdData π hker hn h₁).1 (stdData π hker hn h₁).2.1 (stdData π hker hn h₁).2.2
      (stdData π hker hn h₂).1 (stdData π hker hn h₂).2.1 (stdData π hker hn h₂).2.2
      (stdData_eps_le_one π hker hn h₁) (stdData_eps_le_one π hker hn h₂)
    have h12 :
        CFSG.QuasithinUnique.K1.stdAut (stdData π hker hn (h₁ * h₂)).1
            (stdData π hker hn (h₁ * h₂)).2.1 (stdData π hker hn (h₁ * h₂)).2.2 =
          CFSG.QuasithinUnique.K1.stdAut (stdData π hker hn h₁).1
              (stdData π hker hn h₁).2.1 (stdData π hker hn h₁).2.2 *
            CFSG.QuasithinUnique.K1.stdAut (stdData π hker hn h₂).1
              (stdData π hker hn h₂).2.1 (stdData π hker hn h₂).2.2 := by
      simpa only [liftAut_eq_stdAut] using map_mul (liftAut π hker hn) h₁ h₂
    have heq :
        CFSG.QuasithinUnique.K1.stdAut (stdData π hker hn (h₁ * h₂)).1
            (stdData π hker hn (h₁ * h₂)).2.1 (stdData π hker hn (h₁ * h₂)).2.2 =
          CFSG.QuasithinUnique.K1.stdAut C
            ((stdData π hker hn h₁).2.1 * (stdData π hker hn h₂).2.1)
            (((stdData π hker hn h₁).2.2 + (stdData π hker hn h₂).2.2) % 2) :=
      h12.trans hC
    exact (stdAut_field_graph_unique hn (stdData_eps_le_one π hker hn (h₁ * h₂))
      (by have h := Nat.mod_lt ((stdData π hker hn h₁).2.2 +
        (stdData π hker hn h₂).2.2) (by norm_num : 0 < 2); omega) heq).1

@[expose] noncomputable def graphPart (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n) :
    rangeNormalizer π →* Multiplicative (ZMod 2) where
  toFun h := Multiplicative.ofAdd ((stdData π hker hn h).2.2 : ZMod 2)
  map_one' := by
    rw [stdData_one_eps π hker hn]
    rfl
  map_mul' h₁ h₂ := by
    obtain ⟨C, hC⟩ := exists_stdAut_mul hn
      (stdData π hker hn h₁).1 (stdData π hker hn h₁).2.1 (stdData π hker hn h₁).2.2
      (stdData π hker hn h₂).1 (stdData π hker hn h₂).2.1 (stdData π hker hn h₂).2.2
      (stdData_eps_le_one π hker hn h₁) (stdData_eps_le_one π hker hn h₂)
    have h12 :
        CFSG.QuasithinUnique.K1.stdAut (stdData π hker hn (h₁ * h₂)).1
            (stdData π hker hn (h₁ * h₂)).2.1 (stdData π hker hn (h₁ * h₂)).2.2 =
          CFSG.QuasithinUnique.K1.stdAut (stdData π hker hn h₁).1
              (stdData π hker hn h₁).2.1 (stdData π hker hn h₁).2.2 *
            CFSG.QuasithinUnique.K1.stdAut (stdData π hker hn h₂).1
              (stdData π hker hn h₂).2.1 (stdData π hker hn h₂).2.2 := by
      simpa only [liftAut_eq_stdAut] using map_mul (liftAut π hker hn) h₁ h₂
    have heq :
        CFSG.QuasithinUnique.K1.stdAut (stdData π hker hn (h₁ * h₂)).1
            (stdData π hker hn (h₁ * h₂)).2.1 (stdData π hker hn (h₁ * h₂)).2.2 =
          CFSG.QuasithinUnique.K1.stdAut C
            ((stdData π hker hn h₁).2.1 * (stdData π hker hn h₂).2.1)
            (((stdData π hker hn h₁).2.2 + (stdData π hker hn h₂).2.2) % 2) :=
      h12.trans hC
    have hε := (stdAut_field_graph_unique hn (stdData_eps_le_one π hker hn (h₁ * h₂))
      (by have h := Nat.mod_lt ((stdData π hker hn h₁).2.2 +
        (stdData π hker hn h₂).2.2) (by norm_num : 0 < 2); omega) heq).2
    rw [hε]
    rw [show Multiplicative.ofAdd ((stdData π hker hn h₁).2.2 : ZMod 2) *
        Multiplicative.ofAdd ((stdData π hker hn h₂).2.2 : ZMod 2) =
        Multiplicative.ofAdd (((stdData π hker hn h₁).2.2 : ZMod 2) +
          ((stdData π hker hn h₂).2.2 : ZMod 2)) from rfl]
    congr 1
    rw [ZMod.natCast_mod]
    push_cast
    ring

omit [Finite F] [CharP F 2] in
theorem stdAut_toGL_one (x : SpecialLinearGroup (Fin n) F) :
    CFSG.QuasithinUnique.K1.stdAut (SpecialLinearGroup.toGL x) (1 : F ≃+* F) 0 =
      MulAut.conj x := by
  apply MulEquiv.ext
  intro g
  rw [CFSG.QuasithinUnique.K1.stdAut, pow_zero, mul_one]
  simp only [MulAut.mul_apply, map_one, MulAut.one_apply, MulAut.conj_apply]
  exact slConjugation_toGL x g

omit [CharP F 2] in
theorem fieldPart_graphPart_range (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n)
    (x : SpecialLinearGroup (Fin n) F) :
    fieldPart π hker hn
        ⟨π x, Subgroup.le_normalizer (MonoidHom.mem_range.mpr ⟨x, rfl⟩)⟩ = 1 ∧
      graphPart π hker hn
        ⟨π x, Subgroup.le_normalizer (MonoidHom.mem_range.mpr ⟨x, rfl⟩)⟩ = 1 := by
  let hx : rangeNormalizer π :=
    ⟨π x, Subgroup.le_normalizer (MonoidHom.mem_range.mpr ⟨x, rfl⟩)⟩
  change fieldPart π hker hn hx = 1 ∧ graphPart π hker hn hx = 1
  have hstd :
      CFSG.QuasithinUnique.K1.stdAut (stdData π hker hn hx).1
          (stdData π hker hn hx).2.1 (stdData π hker hn hx).2.2 =
        CFSG.QuasithinUnique.K1.stdAut (SpecialLinearGroup.toGL x) (1 : F ≃+* F) 0 := by
    rw [stdAut_toGL_one]
    exact liftAut_range π hker hn x
  have huniq := stdAut_field_graph_unique hn
    (stdData_eps_le_one π hker hn hx) (by norm_num) hstd
  refine ⟨huniq.1, ?_⟩
  change Multiplicative.ofAdd ((stdData π hker hn hx).2.2 : ZMod 2) = 1
  rw [huniq.2]
  rfl

end FieldGraphParts

end CFSG.LieType.SpecialLinear
