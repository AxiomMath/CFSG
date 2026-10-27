module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinSemilin
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinL3

public section

namespace CFSG.QuasithinUnique.Fin257

namespace L3

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.ComponentClassification

open scoped commutatorElement

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem eq_of_proj_eq_of_sq {g T : Matrix.SpecialLinearGroup (Fin 3) F} (hg : g * g = 1)
    (hT : T * T = 1) (h : proj 3 F g = proj 3 F T) : g = T := by
  have hz : g⁻¹ * T ∈ scalars 3 F := proj_eq_proj_iff.mp h
  have hcen : g⁻¹ * T ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) :=
    scalars_le_center 3 F hz
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  rw [hgi] at hz hcen
  have hcomm : g * (g * T) = (g * T) * g := Subgroup.mem_center_iff.mp hcen g
  have hgT : g * T = T * g := by
    calc g * T = g * (g * (g * T)) := by rw [← mul_assoc, hg, one_mul]
      _ = g * ((g * T) * g) := by rw [hcomm]
      _ = (g * g) * T * g := by group
      _ = T * g := by rw [hg, one_mul]
  have hsq : (g * T) * (g * T) = 1 := by
    calc (g * T) * (g * T) = g * (T * g) * T := by group
      _ = g * (g * T) * T := by rw [hgT]
      _ = (g * g) * (T * T) := by group
      _ = 1 := by rw [hg, hT, one_mul]
  obtain ⟨c, hc3, hmat⟩ := mem_scalars.mp hz
  have h00 := congrFun (congrFun (congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) F =>
    (x : Matrix (Fin 3) (Fin 3) F)) hsq) 0) 0
  simp only [Matrix.SpecialLinearGroup.coe_mul, hmat, Matrix.SpecialLinearGroup.coe_one] at h00
  simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply] at h00
  have hcc : c * c = 1 := Units.ext (by simpa using h00)
  have hc1 : c = 1 := by
    calc c = c * (c * c) := by rw [hcc, mul_one]
      _ = c ^ 3 := (pow_three c).symm
      _ = 1 := hc3
  have hgT1 : g * T = 1 := Subtype.ext (by rw [hmat, hc1]; simp)
  have : T = g⁻¹ := eq_inv_of_mul_eq_one_right hgT1
  rw [this, hgi]


@[expose] def G1 (a c : F) : Matrix.SpecialLinearGroup (Fin 3) F := xMat a * wMat c

omit [CharP F 2] in
theorem coe_G1 (a c : F) :
    (G1 a c : Matrix (Fin 3) (Fin 3) F) = !![1, a, c; 0, 1, 0; 0, 0, 1] := by
  rw [G1, Matrix.SpecialLinearGroup.coe_mul]
  change xM a * wM c = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xM, wM, Matrix.mul_apply, Fin.sum_univ_three]

theorem G1_mul_self (a c : F) : G1 a c * G1 a c = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_G1, Matrix.SpecialLinearGroup.coe_one]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination a * h2
  · linear_combination c * h2

omit [CharP F 2] in
theorem proj_G1 (a c : F) : proj 3 F (G1 a c) = xP a * wP c := by
  rw [G1, map_mul]
  rfl

@[expose] noncomputable def Phi (A : GL (Fin 3) F) (σ : F ≃+* F) (ε : ℕ) :
    MulAut (Matrix.SpecialLinearGroup (Fin 3) F) :=
  CatalogueBHigherLinearAction.slConjugation 3 F A *
    CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ * CatalogueBGraphForm.slGraphAut 3 F ^ ε

omit [CharP F 2] in
theorem standard_eq_descendAut (A : GL (Fin 3) F) (σ : F ≃+* F) (ε : ℕ) :
    conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F ^ ε = descendAut 3 F (Phi A σ ε) := by
  rw [Phi, map_mul, map_mul, map_pow]
  rfl

omit [CharP F 2] in
theorem standard_apply_proj (A : GL (Fin 3) F) (σ : F ≃+* F) (ε : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin 3) F) :
    (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F ^ ε) (proj 3 F g) =
      proj 3 F (Phi A σ ε g) := by
  rw [standard_eq_descendAut, descendAut_proj]

omit [CharP F 2] in
theorem coe_Phi_zero (A : GL (Fin 3) F) (σ : F ≃+* F) (g : Matrix.SpecialLinearGroup (Fin 3) F) :
    ((Phi A σ 0 g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F).map σ *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  rw [Phi, pow_zero, mul_one, MulAut.mul_apply, coe_slConjugation]
  rfl

omit [CharP F 2] in
theorem coe_Phi_one (A : GL (Fin 3) F) (σ : F ≃+* F) (g : Matrix.SpecialLinearGroup (Fin 3) F) :
    ((Phi A σ 1 g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) *
        (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).transpose.map σ) *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  rw [Phi, pow_one, MulAut.mul_apply, MulAut.mul_apply, coe_slConjugation]
  rfl


@[expose] def Fixes (θ : MulAut (projectiveSL 3 F)) : Set (F × F) :=
  {v | θ (xP v.1 * wP v.2) = xP v.1 * wP v.2}

theorem phi_fix {A : GL (Fin 3) F} {σ : F ≃+* F} {ε : ℕ} {v : F × F}
    (hv : v ∈ Fixes (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F ^ ε)) :
    Phi A σ ε (G1 v.1 v.2) = G1 v.1 v.2 := by
  have h1 := standard_apply_proj A σ ε (G1 v.1 v.2)
  rw [proj_G1] at h1
  have h2 : proj 3 F (Phi A σ ε (G1 v.1 v.2)) = proj 3 F (G1 v.1 v.2) := by
    rw [← h1, proj_G1]
    exact hv
  refine eq_of_proj_eq_of_sq ?_ (G1_mul_self _ _) h2
  rw [← map_mul, G1_mul_self, map_one]

omit [CharP F 2] in
theorem mul_eq_of_phi {A : GL (Fin 3) F} {M : Matrix (Fin 3) (Fin 3) F} {G : Matrix (Fin 3) (Fin 3) F}
    (h : (A : Matrix (Fin 3) (Fin 3) F) * M * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = G) :
    (A : Matrix (Fin 3) (Fin 3) F) * M = G * (A : Matrix (Fin 3) (Fin 3) F) := by
  rw [← h]
  calc (A : Matrix (Fin 3) (Fin 3) F) * M =
      (A : Matrix (Fin 3) (Fin 3) F) * M * (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (A : Matrix (Fin 3) (Fin 3) F)) := by rw [Units.inv_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem fix0_eqs {A : GL (Fin 3) F} {σ : F ≃+* F} {v : F × F}
    (hv : v ∈ Fixes (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F ^ 0)) :
    (A : Matrix (Fin 3) (Fin 3) F) 0 0 * σ v.1 =
        v.1 * (A : Matrix (Fin 3) (Fin 3) F) 1 1 + v.2 * (A : Matrix (Fin 3) (Fin 3) F) 2 1 ∧
      (A : Matrix (Fin 3) (Fin 3) F) 0 0 * σ v.2 =
        v.1 * (A : Matrix (Fin 3) (Fin 3) F) 1 2 + v.2 * (A : Matrix (Fin 3) (Fin 3) F) 2 2 ∧
      (A : Matrix (Fin 3) (Fin 3) F) 1 0 * σ v.1 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) F) 1 0 * σ v.2 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) F) 2 0 * σ v.1 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) F) 2 0 * σ v.2 = 0 := by
  have h := phi_fix hv
  have h1 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) F =>
    (x : Matrix (Fin 3) (Fin 3) F)) h
  simp only [coe_Phi_zero, coe_G1] at h1
  have h2 := mul_eq_of_phi h1
  have e01 := congrFun (congrFun h2 0) 1
  have e02 := congrFun (congrFun h2 0) 2
  have e11 := congrFun (congrFun h2 1) 1
  have e12 := congrFun (congrFun h2 1) 2
  have e21 := congrFun (congrFun h2 2) 1
  have e22 := congrFun (congrFun h2 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply] at e01 e02 e11 e12 e21 e22
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination e01
  · linear_combination e02
  · rcases e11 with h | h <;> simp [h]
  · rcases e12 with h | h <;> simp [h]
  · rcases e21 with h | h <;> simp [h]
  · rcases e22 with h | h <;> simp [h]


theorem fix1_eqs {A : GL (Fin 3) F} {σ : F ≃+* F} {v : F × F}
    (hv : v ∈ Fixes (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F ^ 1)) :
    v.1 * (A : Matrix (Fin 3) (Fin 3) F) 1 1 + v.2 * (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧
      v.1 * (A : Matrix (Fin 3) (Fin 3) F) 1 2 + v.2 * (A : Matrix (Fin 3) (Fin 3) F) 2 2 = 0 := by
  have h := phi_fix hv
  have hinv : ((G1 v.1 v.2)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) = G1 v.1 v.2 :=
    inv_eq_of_mul_eq_one_right (G1_mul_self _ _)
  have h1 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) F =>
    (x : Matrix (Fin 3) (Fin 3) F)) h
  simp only [coe_Phi_one, hinv, coe_G1] at h1
  have h2 := mul_eq_of_phi h1
  have e01 := congrFun (congrFun h2 0) 1
  have e02 := congrFun (congrFun h2 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply] at e01 e02
  exact ⟨by linear_combination -e01, by linear_combination -e02⟩


omit [CharP F 2] in
theorem det_ne_zero (A : GL (Fin 3) F) : (A : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero

omit [CharP F 2] in
theorem block_ne_zero (A : GL (Fin 3) F) :
    ((A : Matrix (Fin 3) (Fin 3) F) 1 1 ≠ 0 ∨ (A : Matrix (Fin 3) (Fin 3) F) 2 1 ≠ 0) ∨
      ((A : Matrix (Fin 3) (Fin 3) F) 1 2 ≠ 0 ∨ (A : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0) := by
  by_contra h
  push Not at h
  obtain ⟨⟨h11, h21⟩, h12, h22⟩ := h
  apply det_ne_zero A
  rw [Matrix.det_fin_three, h11, h21, h12, h22]
  ring

omit [CharP F 2] in
theorem entry00_ne_zero (A : GL (Fin 3) F) (h10 : (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0)
    (h20 : (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) : (A : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := by
  intro h00
  apply det_ne_zero A
  rw [Matrix.det_fin_three, h00, h10, h20]
  ring

theorem fixes_type0 [Finite F] {θ : MulAut (projectiveSL 3 F)}
    (hθ : θ ∈ semilinearAutGroup 3 F) (hθD : θ ∉ linearAutGroup 3 F) :
    ∃ (σ : F ≃+* F) (m₁₁ m₁₂ m₂₁ m₂₂ : F), σ ≠ 1 ∧
      Fixes θ ⊆ {v | Semilin.InS σ m₁₁ m₁₂ m₂₁ m₂₂ v} := by
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp hθ
  have hσ : σ ≠ 1 := by
    rintro rfl
    exact hθD (by rw [map_one, mul_one]; exact conjAut_mem_linearAutGroup A)
  refine ⟨σ, ?_⟩
  by_cases hz : ∀ v ∈ Fixes (conjAut 3 F A * fieldAut 3 F σ), v = 0
  · refine ⟨0, 0, 0, 0, hσ, fun v hv => ?_⟩
    rw [hz v hv]
    exact Semilin.inS_zero σ 0 0 0 0
  · push Not at hz
    obtain ⟨v₀, hv₀, hv₀0⟩ := hz
    have hv₀' : v₀ ∈ Fixes (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F ^ 0) := by
      rw [pow_zero, mul_one]
      exact hv₀
    obtain ⟨-, -, e1, e2, e3, e4⟩ := fix0_eqs hv₀'
    have hσv : σ v₀.1 ≠ 0 ∨ σ v₀.2 ≠ 0 := by
      rcases Semilin.ne_zero_coord hv₀0 with h | h
      · exact Or.inl (by simpa using h)
      · exact Or.inr (by simpa using h)
    have h10 : (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 := by
      rcases hσv with h | h
      · exact (mul_eq_zero.mp e1).resolve_right h
      · exact (mul_eq_zero.mp e2).resolve_right h
    have h20 : (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
      rcases hσv with h | h
      · exact (mul_eq_zero.mp e3).resolve_right h
      · exact (mul_eq_zero.mp e4).resolve_right h
    have h00 := entry00_ne_zero A h10 h20
    refine ⟨(A : Matrix (Fin 3) (Fin 3) F) 1 1 / (A : Matrix (Fin 3) (Fin 3) F) 0 0,
      (A : Matrix (Fin 3) (Fin 3) F) 2 1 / (A : Matrix (Fin 3) (Fin 3) F) 0 0,
      (A : Matrix (Fin 3) (Fin 3) F) 1 2 / (A : Matrix (Fin 3) (Fin 3) F) 0 0,
      (A : Matrix (Fin 3) (Fin 3) F) 2 2 / (A : Matrix (Fin 3) (Fin 3) F) 0 0, hσ, fun v hv => ?_⟩
    have hv' : v ∈ Fixes (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F ^ 0) := by
      rw [pow_zero, mul_one]
      exact hv
    obtain ⟨f1, f2, -, -, -, -⟩ := fix0_eqs hv'
    refine ⟨?_, ?_⟩
    · field_simp
      linear_combination f1
    · field_simp
      linear_combination f2

theorem fixes_type1 [Finite F] {θ : MulAut (projectiveSL 3 F)}
    (hθ : θ ∉ semilinearAutGroup 3 F) :
    ∃ α β : F, (α ≠ 0 ∨ β ≠ 0) ∧ ∀ v ∈ Fixes θ, v.1 * α + v.2 * β = 0 := by
  have hR : standardAutGroup 3 F = ⊤ := (automorphism_generation (K := F) le_rfl).1
  have hmem : θ ∈ standardAutGroup 3 F := by rw [hR]; exact Subgroup.mem_top _
  have hδδ : dualAut 3 F * dualAut 3 F = 1 := (standard_automorphism_transport (K := F) (n := 3)).2.2.2.1
  obtain ⟨A, σ, hAσ⟩ := mem_semilinearAutGroup_iff.mp
    ((mem_or_mul_dualAut_mem hmem).resolve_left hθ)
  have hθeq : θ = conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F ^ 1 := by
    rw [pow_one, ← hAσ, mul_assoc, hδδ, mul_one]
  have hfix : ∀ v ∈ Fixes θ, v.1 * (A : Matrix (Fin 3) (Fin 3) F) 1 1 +
      v.2 * (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧
      v.1 * (A : Matrix (Fin 3) (Fin 3) F) 1 2 + v.2 * (A : Matrix (Fin 3) (Fin 3) F) 2 2 = 0 :=
    fun v hv => fix1_eqs (by rw [hθeq] at hv; exact hv)
  rcases block_ne_zero A with h | h
  · exact ⟨_, _, h, fun v hv => (hfix v hv).1⟩
  · exact ⟨_, _, h, fun v hv => (hfix v hv).2⟩


theorem card_le_of_pairs {B : Subgroup (projectiveSL 3 F)} (hB : B ≤ V1) (Q : Set (F × F))
    (hQ : ∀ a c : F, xP a * wP c ∈ B → (a, c) ∈ Q) [Finite F] : Nat.card B ≤ Nat.card Q := by
  classical
  have hex : ∀ g : B, ∃ p : F × F, (g : projectiveSL 3 F) = xP p.1 * wP p.2 := fun g => by
    obtain ⟨a, c, h⟩ := mem_V1.mp (hB g.2)
    exact ⟨(a, c), h⟩
  choose p hp using hex
  have hmem : ∀ g : B, p g ∈ Q := fun g => by
    apply hQ
    rw [← hp g]
    exact g.2
  have hinj : Function.Injective (fun g : B => (⟨p g, hmem g⟩ : Q)) := by
    intro g g' h
    have : p g = p g' := congrArg Subtype.val h
    apply Subtype.ext
    rw [hp g, hp g', this]
  exact Nat.card_le_card_of_injective _ hinj

theorem card_le_type0 [Finite F] {B : Subgroup (projectiveSL 3 F)} (hB : B ≤ V1)
    {θ : MulAut (projectiveSL 3 F)} (hθ : θ ∈ semilinearAutGroup 3 F)
    (hθD : θ ∉ linearAutGroup 3 F) (hfix : ∀ g ∈ B, θ g = g) : Nat.card B ≤ Nat.card F := by
  obtain ⟨σ, m₁₁, m₁₂, m₂₁, m₂₂, hσ, hsub⟩ := fixes_type0 hθ hθD
  have h1 : Nat.card B ≤ Nat.card {v : F × F | Semilin.InS σ m₁₁ m₁₂ m₂₁ m₂₂ v} :=
    card_le_of_pairs hB _ fun a c h => hsub (hfix _ h)
  exact h1.trans ((Semilin.card_inS_le σ m₁₁ m₁₂ m₂₁ m₂₂).trans (Semilin.card_fixSet_sq_le σ hσ))

theorem card_le_type1 [Finite F] {B : Subgroup (projectiveSL 3 F)} (hB : B ≤ V1)
    {θ : MulAut (projectiveSL 3 F)} (hθ : θ ∉ semilinearAutGroup 3 F)
    (hfix : ∀ g ∈ B, θ g = g) : Nat.card B ≤ Nat.card F := by
  obtain ⟨α, β, hαβ, hline⟩ := fixes_type1 hθ
  have h1 : Nat.card B ≤ Nat.card {v : F × F | v.1 * α + v.2 * β = 0} :=
    card_le_of_pairs hB _ fun a c h => hline _ (hfix _ h)
  exact h1.trans (Semilin.card_line_le hαβ _ fun v hv => hv)

theorem card_sq_le_pair [Finite F] {B : Subgroup (projectiveSL 3 F)} (hB : B ≤ V1)
    {θ₁ θ₂ : MulAut (projectiveSL 3 F)} (hθ₁ : θ₁ ∈ semilinearAutGroup 3 F)
    (hθ₁D : θ₁ ∉ linearAutGroup 3 F) (hθ₂ : θ₂ ∉ semilinearAutGroup 3 F)
    (hfix₁ : ∀ g ∈ B, θ₁ g = g) (hfix₂ : ∀ g ∈ B, θ₂ g = g) : Nat.card B ^ 2 ≤ Nat.card F := by
  obtain ⟨σ, m₁₁, m₁₂, m₂₁, m₂₂, hσ, hsub⟩ := fixes_type0 hθ₁ hθ₁D
  obtain ⟨α, β, hαβ, hline⟩ := fixes_type1 hθ₂
  obtain ⟨v₀, hv₀, hpar⟩ := Semilin.line_param hαβ
  have h1 : Nat.card B ≤ Nat.card {v : F × F | Semilin.InS σ m₁₁ m₁₂ m₂₁ m₂₂ v ∧
      ∃ t : F, v = (t * v₀.1, t * v₀.2)} :=
    card_le_of_pairs hB _ fun a c h => ⟨hsub (hfix₁ _ h), hpar _ (hline _ (hfix₂ _ h))⟩
  have h2 := h1.trans (Semilin.card_inS_line_le σ m₁₁ m₁₂ m₂₁ m₂₂ hv₀)
  calc Nat.card B ^ 2 ≤ Nat.card (Semilin.FixSet σ) ^ 2 := Nat.pow_le_pow_left h2 2
    _ ≤ Nat.card F := Semilin.card_fixSet_sq_le σ hσ


@[expose] def W0 : GL (Fin 3) F :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

omit [CharP F 2] in
theorem coe_W0 : ((W0 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl

omit [CharP F 2] in
theorem coe_W0_inv : (((W0 : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl

@[expose] def G2 (b c : F) : Matrix.SpecialLinearGroup (Fin 3) F := yMat b * wMat c

omit [CharP F 2] in
theorem coe_G2 (b c : F) :
    (G2 b c : Matrix (Fin 3) (Fin 3) F) = !![1, 0, c; 0, 1, b; 0, 0, 1] := by
  rw [G2, Matrix.SpecialLinearGroup.coe_mul]
  change yM b * wM c = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [yM, wM, Matrix.mul_apply, Fin.sum_univ_three]

theorem G2_mul_self (b c : F) : G2 b c * G2 b c = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_G2, Matrix.SpecialLinearGroup.coe_one]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination c * h2
  · linear_combination b * h2

omit [CharP F 2] in
theorem proj_G2 (b c : F) : proj 3 F (G2 b c) = yP b * wP c := by
  rw [G2, map_mul]
  rfl

@[expose] noncomputable def iota : MulAut (projectiveSL 3 F) := conjAut 3 F W0 * dualAut 3 F

theorem iota_yP_wP (b c : F) : iota (yP b * wP c) = xP b * wP c := by
  rw [← proj_G2, ← proj_G1, iota, MulAut.mul_apply, dualAut_proj, conjAut_proj]
  congr 1
  apply Subtype.ext
  have hinv : ((G2 b c)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) = G2 b c :=
    inv_eq_of_mul_eq_one_right (G2_mul_self _ _)
  rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose, hinv, coe_G2, coe_G1, coe_W0,
    coe_W0_inv]
  have e0 : (!![1, 0, c; 0, 1, b; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F).transpose =
      !![1, 0, 0; 0, 1, 0; c, b, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have e1 : (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) F) * !![1, 0, 0; 0, 1, 0; c, b, 1] =
      !![c, b, 1; 0, 1, 0; 1, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have e2 : (!![c, b, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) F) * !![0, 0, 1; 0, 1, 0; 1, 0, 0] =
      !![1, b, c; 0, 1, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  rw [e0, e1, e2]


theorem iota_mem_V1 {g : projectiveSL 3 F} (hg : g ∈ (V2 : Subgroup (projectiveSL 3 F))) :
    iota g ∈ (V1 : Subgroup (projectiveSL 3 F)) := by
  obtain ⟨b, c, rfl⟩ := mem_V2.mp hg
  rw [iota_yP_wP]
  exact mem_V1.mpr ⟨b, c, rfl⟩

section Normal

variable [Finite F]

omit [CharP F 2] in
theorem linearAut_conj_mem (φ : MulAut (projectiveSL 3 F)) {θ : MulAut (projectiveSL 3 F)}
    (hθ : θ ∈ linearAutGroup 3 F) : φ * θ * φ⁻¹ ∈ linearAutGroup 3 F := by
  obtain ⟨-, -, hDn, -⟩ := standard_outer_quotients (K := F) (n := 3)
  have hR : standardAutGroup 3 F = ⊤ := (automorphism_generation (K := F) le_rfl).1
  rw [hR] at hDn
  exact ((Subgroup.normal_subgroupOf_iff le_top).mp hDn) θ φ hθ (Subgroup.mem_top φ)

omit [CharP F 2] in
theorem semilinearAut_conj_mem (φ : MulAut (projectiveSL 3 F)) {θ : MulAut (projectiveSL 3 F)}
    (hθ : θ ∈ semilinearAutGroup 3 F) : φ * θ * φ⁻¹ ∈ semilinearAutGroup 3 F := by
  obtain ⟨-, -, -, hEn, -⟩ := standard_outer_quotients (K := F) (n := 3)
  have hR : standardAutGroup 3 F = ⊤ := (automorphism_generation (K := F) le_rfl).1
  rw [hR] at hEn
  exact ((Subgroup.normal_subgroupOf_iff le_top).mp hEn) θ φ hθ (Subgroup.mem_top φ)

omit [CharP F 2] in
theorem conj_mem_iff_linear (φ : MulAut (projectiveSL 3 F)) (θ : MulAut (projectiveSL 3 F)) :
    φ * θ * φ⁻¹ ∈ linearAutGroup 3 F ↔ θ ∈ linearAutGroup 3 F := by
  refine ⟨fun h => ?_, linearAut_conj_mem φ⟩
  have := linearAut_conj_mem φ⁻¹ h
  simpa [mul_assoc] using this

omit [CharP F 2] in
theorem conj_mem_iff_semilinear (φ : MulAut (projectiveSL 3 F)) (θ : MulAut (projectiveSL 3 F)) :
    φ * θ * φ⁻¹ ∈ semilinearAutGroup 3 F ↔ θ ∈ semilinearAutGroup 3 F := by
  refine ⟨fun h => ?_, semilinearAut_conj_mem φ⟩
  have := semilinearAut_conj_mem φ⁻¹ h
  simpa [mul_assoc] using this

omit [Finite F] in
theorem transport_V2 {B : Subgroup (projectiveSL 3 F)} (hB : B ≤ V2)
    {θ : MulAut (projectiveSL 3 F)} (hfix : ∀ g ∈ B, θ g = g) :
    B.map (iota (F := F)).toMonoidHom ≤ V1 ∧
      Nat.card (B.map (iota (F := F)).toMonoidHom) = Nat.card B ∧
      ∀ g ∈ B.map (iota (F := F)).toMonoidHom,
        ((iota (F := F)) * θ * (iota (F := F))⁻¹) g = g := by
  refine ⟨?_, Subgroup.card_map_of_injective iota.injective, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact iota_mem_V1 (hB hg)
  · rintro _ ⟨g, hg, rfl⟩
    show iota (θ (iota⁻¹ (iota g))) = iota g
    rw [MulAut.inv_apply, iota.symm_apply_apply, hfix g hg]

theorem card_le_of_not_linear {B : Subgroup (projectiveSL 3 F)} (hB : B ≤ V1 ∨ B ≤ V2)
    {θ : MulAut (projectiveSL 3 F)} (hθD : θ ∉ linearAutGroup 3 F) (hfix : ∀ g ∈ B, θ g = g) :
    Nat.card B ≤ Nat.card F := by
  have key : ∀ (B : Subgroup (projectiveSL 3 F)) (θ : MulAut (projectiveSL 3 F)), B ≤ V1 →
      θ ∉ linearAutGroup 3 F → (∀ g ∈ B, θ g = g) → Nat.card B ≤ Nat.card F := by
    intro B θ hB hθD hfix
    by_cases hθ : θ ∈ semilinearAutGroup 3 F
    · exact card_le_type0 hB hθ hθD hfix
    · exact card_le_type1 hB hθ hfix
  rcases hB with h | h
  · exact key B θ h hθD hfix
  · obtain ⟨h1, h2, h3⟩ := transport_V2 h hfix
    rw [← h2]
    exact key _ _ h1 (fun hm => hθD ((conj_mem_iff_linear iota θ).mp hm)) h3

theorem card_sq_le_of_pair {B : Subgroup (projectiveSL 3 F)} (hB : B ≤ V1 ∨ B ≤ V2)
    {θ₁ θ₂ : MulAut (projectiveSL 3 F)} (hθ₁ : θ₁ ∈ semilinearAutGroup 3 F)
    (hθ₁D : θ₁ ∉ linearAutGroup 3 F) (hθ₂ : θ₂ ∉ semilinearAutGroup 3 F)
    (hfix₁ : ∀ g ∈ B, θ₁ g = g) (hfix₂ : ∀ g ∈ B, θ₂ g = g) : Nat.card B ^ 2 ≤ Nat.card F := by
  rcases hB with h | h
  · exact card_sq_le_pair h hθ₁ hθ₁D hθ₂ hfix₁ hfix₂
  · obtain ⟨h1, h2, h3⟩ := transport_V2 h hfix₁
    obtain ⟨-, -, h4⟩ := transport_V2 h hfix₂
    rw [← h2]
    exact card_sq_le_pair h1 ((conj_mem_iff_semilinear iota θ₁).mpr hθ₁)
      (fun hm => hθ₁D ((conj_mem_iff_linear iota θ₁).mp hm))
      (fun hm => hθ₂ ((conj_mem_iff_semilinear iota θ₂).mp hm)) h3 h4

end Normal

end L3

end CFSG.QuasithinUnique.Fin257
