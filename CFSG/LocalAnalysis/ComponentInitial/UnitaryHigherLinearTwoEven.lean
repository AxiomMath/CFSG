module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.Basic
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoCoordinateQuotients

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GorensteinWalter
open CFSG.Wreathed.CentralSL2 (fieldPerm fieldPerm_apply fieldExtension_conj_coordinateGLAction)

variable {K : Type} [Field K]

theorem coordinateGLAction_toGL (A : SpecialLinearGroup (Fin 2) K) :
    coordinateGLAction K (SpecialLinearGroup.toGL A) = coordinatePSLAction K (A : PSL2 K) := by
  change coordinatePGLAction K (Matrix.ProjGenLinGroup.mk (SpecialLinearGroup.toGL A)) = _
  rw [← Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, coordinatePGLAction_toPGL]

theorem mem_coordinateG_iff {g : Equiv.Perm (Omega K)} :
    g ∈ coordinateG K ↔
      ∃ A : SpecialLinearGroup (Fin 2) K, coordinateGLAction K (SpecialLinearGroup.toGL A) = g := by
  rw [← coordinatePSLAction_range_eq_G]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨A, coordinateGLAction_toGL A⟩
  · rintro ⟨A, rfl⟩
    exact ⟨A, (coordinateGLAction_toGL A).symm⟩

theorem coordinateGLAction_mem_G {X : GL (Fin 2) K} (hX : GeneralLinearGroup.det X = 1) :
    coordinateGLAction K X ∈ coordinateG K := by
  have hmem : X ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K).range :=
    by rw [SpecialLinearGroup.range_toGL_eq_ker_det]; exact hX
  obtain ⟨A, rfl⟩ := hmem
  exact mem_coordinateG_iff.mpr ⟨A, rfl⟩

theorem coordinateGLAction_eq_one_iff [Finite K] (A : GL (Fin 2) K) :
    coordinateGLAction K A = 1 ↔ ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin 2) c = A := by
  have e : (∃ c : Kˣ, GeneralLinearGroup.scalar (Fin 2) c = A) ↔
      Matrix.ProjGenLinGroup.mk A = 1 := by
    rw [Matrix.ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar,
      MonoidHom.mem_range]
  rw [e]
  constructor
  · intro h
    apply coordinatePGLAction_injective K
    rw [map_one]
    exact h
  · intro h
    change coordinatePGLAction K (Matrix.ProjGenLinGroup.mk A) = 1
    rw [h, map_one]

theorem det_scalar_two (c : Kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) c) = c ^ 2 := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal,
    Fin.prod_univ_two, Units.val_pow_eq_pow_val, sq]

variable [CharP K 2]

theorem eq_one_of_sq_eq_one {c : K} (hc : c ^ 2 = 1) : c = 1 := by
  rcases (mul_self_eq_one_iff (a := c)).mp (by rw [← sq]; exact hc) with h | h
  · exact h
  · rw [h, CharTwo.neg_eq]

theorem sl_eq_of_coordinateGLAction_eq [Finite K] {A B : SpecialLinearGroup (Fin 2) K}
    (h : coordinateGLAction K (SpecialLinearGroup.toGL A) =
      coordinateGLAction K (SpecialLinearGroup.toGL B)) : A = B := by
  have h1 : coordinateGLAction K (SpecialLinearGroup.toGL (A⁻¹ * B)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨c, hc⟩ := (coordinateGLAction_eq_one_iff _).mp h1
  have hc2 : (c : K) ^ 2 = 1 := by
    have h2 := congrArg (fun X => ((GeneralLinearGroup.det X : Kˣ) : K)) hc
    simp only [det_scalar_two, Units.val_pow_eq_pow_val] at h2
    rw [h2, GeneralLinearGroup.val_det_apply]
    exact (A⁻¹ * B).2
  have hc1 : c = 1 := Units.ext (eq_one_of_sq_eq_one hc2)
  rw [hc1, map_one] at hc
  have h3 : A⁻¹ * B = 1 := SpecialLinearGroup.toGL_injective (by rw [← hc, map_one])
  rw [← mul_inv_cancel_left A B, h3, mul_one]

theorem existsUnique_sl_rep [Finite K] {g : Equiv.Perm (Omega K)} (hg : g ∈ coordinateG K) :
    ∃! A : SpecialLinearGroup (Fin 2) K, coordinateGLAction K (SpecialLinearGroup.toGL A) = g := by
  obtain ⟨A, hA⟩ := mem_coordinateG_iff.mp hg
  exact ⟨A, hA, fun B hB => sl_eq_of_coordinateGLAction_eq (hB.trans hA.symm)⟩

theorem coordinateD_eq_G [Finite K] : coordinateD K = coordinateG K := by
  refine le_antisymm ?_ (coordinateG_le_D K)
  rw [← coordinateGLAction_range]
  rintro _ ⟨A, rfl⟩
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2)
    (((GeneralLinearGroup.det A)⁻¹ : Kˣ) : K)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact Units.ne_zero _ hc
  have hdet : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc0) * A) =
      1 := by
    rw [map_mul, det_scalar_two]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, sq, ← hc, Units.val_inv_eq_inv_val,
      inv_mul_cancel₀ (Units.ne_zero _), Units.val_one]
  have h1 : coordinateGLAction K A = coordinateGLAction K
      (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc0) * A) := by
    rw [map_mul, (coordinateGLAction_eq_one_iff _).mpr ⟨_, rfl⟩, one_mul]
  rw [h1]
  exact coordinateGLAction_mem_G hdet

omit [CharP K 2] in
theorem fieldExtension_mem_E (σ : K ≃+* K) : fieldExtension K σ ∈ coordinateE K :=
  Subgroup.subset_closure (Or.inr ⟨σ, rfl⟩)

omit [CharP K 2] in
theorem fieldExtension_one : fieldExtension K (1 : K ≃+* K) = 1 := by
  rw [← fieldPerm_apply, map_one]

omit [CharP K 2] in
theorem fieldExtension_mul (σ τ : K ≃+* K) :
    fieldExtension K σ * fieldExtension K τ = fieldExtension K (σ * τ) := by
  rw [← fieldPerm_apply, ← fieldPerm_apply, ← fieldPerm_apply, map_mul]

omit [CharP K 2] in
theorem fieldExtension_inv (σ : K ≃+* K) :
    (fieldExtension K σ)⁻¹ = fieldExtension K σ⁻¹ := by
  rw [← fieldPerm_apply, ← fieldPerm_apply, map_inv]

omit [CharP K 2] in
theorem fieldExtension_conj_mem_G (σ : K ≃+* K) {g : Equiv.Perm (Omega K)}
    (hg : g ∈ coordinateG K) : fieldExtension K σ * g * (fieldExtension K σ)⁻¹ ∈ coordinateG K := by
  obtain ⟨A, rfl⟩ := mem_coordinateG_iff.mp hg
  rw [fieldExtension_conj_coordinateGLAction K]
  apply coordinateGLAction_mem_G
  have hdet : GeneralLinearGroup.det (SpecialLinearGroup.toGL A) = 1 :=
    Units.ext (by rw [GeneralLinearGroup.val_det_apply]; exact A.2)
  rw [GeneralLinearGroup.map_det, hdet, map_one]

omit [CharP K 2] in
theorem eq_one_of_fieldExtension_mem_D {σ : K ≃+* K} (hσ : fieldExtension K σ ∈ coordinateD K) :
    σ = 1 := by
  rw [← coordinateGLAction_range] at hσ
  obtain ⟨B, hB⟩ := hσ
  have h10 : B.val 1 0 = 0 := by
    by_contra hc
    have h1 := congrArg (fun π : Equiv.Perm (Omega K) => π none) hB
    simp only [coordinateGLAction_infinity K B hc, fieldExtension_none] at h1
    exact Option.some_ne_none _ h1
  have hdet : B.val 0 0 * B.val 1 1 ≠ 0 := by
    have h1 := (GeneralLinearGroup.det B).ne_zero
    rwa [GeneralLinearGroup.val_det_apply, det_fin_two, h10, mul_zero, sub_zero] at h1
  have h11 : B.val 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  have hx : ∀ x : K, coordinateGLAction K B (some x) =
      some ((B.val 0 0 * x + B.val 0 1) / B.val 1 1) := by
    intro x
    rw [coordinateGLAction_finite K B x (by rw [h10, zero_mul, zero_add]; exact h11), h10,
      zero_mul, zero_add]
  have hpt : ∀ x : K, (B.val 0 0 * x + B.val 0 1) / B.val 1 1 = σ x := by
    intro x
    have h1 := congrArg (fun π : Equiv.Perm (Omega K) => π (some x)) hB
    simp only [hx, fieldExtension_some, Option.some.injEq] at h1
    exact h1
  have h0 := hpt 0
  rw [mul_zero, zero_add, map_zero, div_eq_zero_iff] at h0
  have hb : B.val 0 1 = 0 := h0.resolve_right h11
  have h1 := hpt 1
  rw [mul_one, hb, add_zero, map_one, div_eq_one_iff_eq h11] at h1
  refine RingEquiv.ext fun x => ?_
  rw [← hpt x, hb, add_zero, h1, mul_div_cancel_left₀ x h11]
  rfl

omit [CharP K 2] in
theorem fieldExtension_mem_G_iff (σ : K ≃+* K) : fieldExtension K σ ∈ coordinateG K ↔ σ = 1 := by
  refine ⟨fun h => eq_one_of_fieldExtension_mem_D (coordinateG_le_D K h), ?_⟩
  rintro rfl
  rw [fieldExtension_one]
  exact one_mem _

theorem exists_coordinateE_factor [Finite K] {a : Equiv.Perm (Omega K)} (ha : a ∈ coordinateE K) :
    ∃ g ∈ coordinateG K, ∃ σ : K ≃+* K, a = g * fieldExtension K σ := by
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨σ, rfl⟩
    · rw [SetLike.mem_coe, coordinateD_eq_G] at hx
      exact ⟨x, hx, 1, by rw [fieldExtension_one, mul_one]⟩
    · exact ⟨1, one_mem _, σ, (one_mul _).symm⟩
  | one => exact ⟨1, one_mem _, 1, by rw [fieldExtension_one, mul_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨g, hg, σ, rfl⟩ := hx
    obtain ⟨g', hg', τ, rfl⟩ := hy
    refine ⟨g * (fieldExtension K σ * g' * (fieldExtension K σ)⁻¹),
      mul_mem hg (fieldExtension_conj_mem_G σ hg'), σ * τ, ?_⟩
    rw [← fieldExtension_mul]
    group
  | inv x _ hx =>
    obtain ⟨g, hg, σ, rfl⟩ := hx
    refine ⟨fieldExtension K σ⁻¹ * g⁻¹ * (fieldExtension K σ⁻¹)⁻¹,
      fieldExtension_conj_mem_G σ⁻¹ (inv_mem hg), σ⁻¹, ?_⟩
    rw [← fieldExtension_inv]
    group

omit [CharP K 2] in
theorem coordinateE_factor_unique {g g' : Equiv.Perm (Omega K)} (hg : g ∈ coordinateG K)
    (hg' : g' ∈ coordinateG K) {σ τ : K ≃+* K}
    (h : g * fieldExtension K σ = g' * fieldExtension K τ) : g = g' ∧ σ = τ := by
  have h1 : g'⁻¹ * g = fieldExtension K (τ * σ⁻¹) := by
    rw [← fieldExtension_mul, ← fieldExtension_inv]
    calc g'⁻¹ * g = g'⁻¹ * (g * fieldExtension K σ) * (fieldExtension K σ)⁻¹ := by group
      _ = g'⁻¹ * (g' * fieldExtension K τ) * (fieldExtension K σ)⁻¹ := by rw [h]
      _ = fieldExtension K τ * (fieldExtension K σ)⁻¹ := by group
  have h2 : τ * σ⁻¹ = 1 := (fieldExtension_mem_G_iff _).mp (h1 ▸ mul_mem (inv_mem hg') hg)
  obtain rfl : σ = τ := (mul_inv_eq_one.mp h2).symm
  exact ⟨mul_right_cancel h, rfl⟩

theorem existsUnique_coordinateE_factor [Finite K] {a : Equiv.Perm (Omega K)}
    (ha : a ∈ coordinateE K) :
    ∃! x : coordinateG K × (K ≃+* K), a = (x.1 : Equiv.Perm (Omega K)) * fieldExtension K x.2 := by
  obtain ⟨g, hg, σ, rfl⟩ := exists_coordinateE_factor ha
  refine ⟨(⟨g, hg⟩, σ), rfl, fun y hy => ?_⟩
  obtain ⟨h1, h2⟩ := coordinateE_factor_unique y.1.2 hg hy.symm
  exact Prod.ext (Subtype.ext h1) h2

theorem exists_fieldQuotient_bijective [Finite K] :
    ∃ ψ : (K ≃+* K) →* coordinateE K ⧸ (coordinateG K).subgroupOf (coordinateE K),
      Function.Bijective ψ := by
  refine ⟨(QuotientGroup.mk' _).comp ((fieldPerm K).codRestrict (coordinateE K)
    fieldExtension_mem_E), (injective_iff_map_eq_one _).mpr fun σ hσ => ?_, fun q => ?_⟩
  · rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hσ
    exact (fieldExtension_mem_G_iff σ).mp hσ
  · obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨g, hg, σ, rfl⟩ := exists_coordinateE_factor ha
    refine ⟨σ, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    change (fieldExtension K σ)⁻¹ * (g * fieldExtension K σ) ∈ coordinateG K
    have h1 := fieldExtension_conj_mem_G σ⁻¹ hg
    rwa [← fieldExtension_inv, inv_inv, mul_assoc] at h1

theorem exists_conj_upper_of_sq_eq_one {A : SpecialLinearGroup (Fin 2) K} (hA : A * A = 1)
    (hA1 : A ≠ 1) : ∃ P : GL (Fin 2) K,
      SpecialLinearGroup.toGL A * P = P * SpecialLinearGroup.toGL (sl2UpperUnipotent 1) := by
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 2) (Fin 2) K, M = (A : Matrix (Fin 2) (Fin 2) K) := ⟨_, rfl⟩
  have hMM : M * M = 1 := by
    have h1 := congrArg (fun X : SpecialLinearGroup (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K)) hA
    rw [hM]
    exact h1
  have entry : ∀ i j, (M * M) i j = (1 : Matrix (Fin 2) (Fin 2) K) i j := fun i j => by rw [hMM]
  have e00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using entry 0 0
  have e10 : M 1 0 * M 0 0 + M 1 1 * M 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using entry 1 0
  have e11 : M 1 0 * M 0 1 + M 1 1 * M 1 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using entry 1 1
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  by_cases hc : M 1 0 = 0
  ·
    have ha : M 0 0 = 1 := eq_one_of_sq_eq_one (by rw [sq]; simpa [hc] using e00)
    have hd : M 1 1 = 1 := eq_one_of_sq_eq_one (by rw [sq]; simpa [hc] using e11)
    have hb : M 0 1 ≠ 0 := by
      intro hb
      apply hA1
      refine Subtype.ext ?_
      rw [← hM]
      change M = 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
    refine ⟨GeneralLinearGroup.mkOfDetNeZero !![M 0 1, 0; 0, 1] (by simp [det_fin_two, hb]), ?_⟩
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul]
    change (A : Matrix (Fin 2) (Fin 2) K) * !![M 0 1, 0; 0, 1] = !![M 0 1, 0; 0, 1] * !![1, 1; 0, 1]
    rw [← hM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hc, hd]
  ·
    have had : M 1 1 = M 0 0 := by
      have h1 : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination e10
      have h3 := (mul_eq_zero.mp h1).resolve_left hc
      rw [eq_neg_of_add_eq_zero_right h3, CharTwo.neg_eq]
    refine ⟨GeneralLinearGroup.mkOfDetNeZero !![M 0 0 + 1, 1; M 1 0, 0]
      (by simp [det_fin_two, hc]), ?_⟩
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul]
    change (A : Matrix (Fin 2) (Fin 2) K) * !![M 0 0 + 1, 1; M 1 0, 0] =
      !![M 0 0 + 1, 1; M 1 0, 0] * !![1, 1; 0, 1]
    rw [← hM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, had]
    · linear_combination e00
    · linear_combination (-1 : K) * h2
    · linear_combination e10 - M 1 0 * had

omit [CharP K 2] in
theorem even_linear_two_involution_normal_forms [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) :
    coordinateD K = coordinateG K ∧
    (∀ g ∈ coordinateG K, ∃! A : SpecialLinearGroup (Fin 2) K,
      coordinateGLAction K (SpecialLinearGroup.toGL A) = g) ∧
    ((coordinateG K).subgroupOf (coordinateE K)).Normal ∧
    (fieldPerm K).range ≤ coordinateE K ∧
    coordinateG K ⊓ (fieldPerm K).range = ⊥ ∧
    Function.Injective (fieldPerm K) ∧
    (∀ a ∈ coordinateE K, ∃! x : coordinateG K × (K ≃+* K),
      a = (x.1 : Equiv.Perm (Omega K)) * fieldExtension K x.2) ∧
    IsCyclic (coordinateE K ⧸ (coordinateG K).subgroupOf (coordinateE K)) ∧
    Nat.card (coordinateE K ⧸ (coordinateG K).subgroupOf (coordinateE K)) = f ∧
    ∀ a ∈ coordinateE K, orderOf a = 2 →
      (a ∈ coordinateG K ∧ ∃ h ∈ coordinateG K, a = h * translation K 1 * h⁻¹) ∨
      (a ∉ coordinateG K ∧ Even f ∧ ∃ σ : K ≃+* K, σ ≠ 1 ∧ σ * σ = 1 ∧
        (∀ x, σ x = x ^ 2 ^ (f / 2)) ∧ (∀ τ : K ≃+* K, τ ≠ 1 → τ * τ = 1 → τ = σ) ∧
        (∃ d ∈ coordinateG K, a = d * fieldExtension K σ) ∧
        (∃ h ∈ coordinateG K, a = h * fieldExtension K σ * h⁻¹) ∧
        ∃ k : Subfield K, (k : Set K) = {x | σ x = x} ∧ Nat.card k = 2 ^ (f / 2)) := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hDG := coordinateD_eq_G (K := K)
  have hρG : ∀ P : GL (Fin 2) K, coordinateGLAction K P ∈ coordinateG K := fun P => by
    rw [← hDG, ← coordinateGLAction_range]
    exact ⟨P, rfl⟩
  obtain ⟨ψ, hψ⟩ := exists_fieldQuotient_bijective (K := K)
  obtain ⟨φ, -, -, hzp, hcard, hfix⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hK
  have hcyc : IsCyclic (K ≃+* K) := ⟨⟨φ, fun x =>
    Subgroup.mem_zpowers_iff.mp (by rw [hzp]; exact Subgroup.mem_top x)⟩⟩
  refine ⟨hDG, fun g hg => existsUnique_sl_rep hg, coordinateG_normal_in_E K, ?_, ?_, ?_,
    fun a ha => existsUnique_coordinateE_factor ha, isCyclic_of_surjective ψ hψ.2, ?_, ?_⟩
  · rintro _ ⟨σ, rfl⟩
    exact fieldExtension_mem_E σ
  · rw [eq_bot_iff]
    rintro x ⟨hxG, σ, rfl⟩
    rw [fieldPerm_apply] at hxG ⊢
    rw [Subgroup.mem_bot, (fieldExtension_mem_G_iff σ).mp hxG, fieldExtension_one]
  · refine (injective_iff_map_eq_one _).mpr fun σ hσ => ?_
    rw [fieldPerm_apply] at hσ
    exact (fieldExtension_mem_G_iff σ).mp (hσ ▸ one_mem _)
  · rw [← Nat.card_congr (Equiv.ofBijective ψ hψ), hcard]
  intro a ha hord2
  have ha2 : a ^ 2 = 1 := by
    rw [← hord2]
    exact pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hord2
    omega
  obtain ⟨g, hg, σ, rfl⟩ := exists_coordinateE_factor ha
  by_cases hσ : σ = 1
  ·
    subst hσ
    rw [fieldExtension_one, mul_one] at ha1 ha2 ⊢
    refine Or.inl ⟨hg, ?_⟩
    obtain ⟨A, hA⟩ := mem_coordinateG_iff.mp hg
    have hAA : A * A = 1 := by
      apply sl_eq_of_coordinateGLAction_eq
      rw [map_mul, map_mul, hA, map_one, map_one, ← sq, ha2]
    have hA1 : A ≠ 1 := by
      rintro rfl
      apply ha1
      rw [← hA, map_one, map_one]
    obtain ⟨P, hP⟩ := exists_conj_upper_of_sq_eq_one hAA hA1
    have hU : coordinateGLAction K (SpecialLinearGroup.toGL (sl2UpperUnipotent (1 : K))) =
        translation K 1 := by
      rw [coordinateGLAction_toGL]
      exact coordinatePSLAction_upper K 1
    refine ⟨coordinateGLAction K P, hρG P, ?_⟩
    rw [← hA, ← hU, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact eq_mul_inv_iff_mul_eq.mpr hP
  ·
    have h1 : g * fieldExtension K σ * (g * fieldExtension K σ) =
        (g * (fieldExtension K σ * g * (fieldExtension K σ)⁻¹)) * fieldExtension K (σ * σ) := by
      rw [← fieldExtension_mul]
      group
    have h2 : (g * (fieldExtension K σ * g * (fieldExtension K σ)⁻¹)) *
        fieldExtension K (σ * σ) = 1 * fieldExtension K 1 := by
      rw [← h1, ← sq, ha2, fieldExtension_one, one_mul]
    obtain ⟨hgg, hσσ⟩ :=
      coordinateE_factor_unique (mul_mem hg (fieldExtension_conj_mem_G σ hg)) (one_mem _) h2
    obtain ⟨hfe, hσpow⟩ := LinearFlag.even_and_eq_pow_of_involution hf hK hσ hσσ
    refine Or.inr ⟨fun hmem => hσ ((fieldExtension_mem_G_iff σ).mp (by
      have h3 := mul_mem (inv_mem hg) hmem
      rwa [inv_mul_cancel_left] at h3)), hfe, σ, hσ, hσσ, hσpow, fun τ hτ hττ => ?_,
      ⟨g, hg, rfl⟩, ?_, ?_⟩
    · obtain ⟨-, hτpow⟩ := LinearFlag.even_and_eq_pow_of_involution hf hK hτ hττ
      exact RingEquiv.ext fun x => by rw [hτpow, hσpow]
    ·
      obtain ⟨A, hA⟩ := mem_coordinateG_iff.mp hg
      have hdetA : GeneralLinearGroup.det (SpecialLinearGroup.toGL A) = 1 :=
        Units.ext (by rw [GeneralLinearGroup.val_det_apply]; exact A.2)
      have hAσ : SpecialLinearGroup.toGL A *
          GeneralLinearGroup.map σ.toRingHom (SpecialLinearGroup.toGL A) = 1 := by
        have h3 : coordinateGLAction K (SpecialLinearGroup.toGL A *
            GeneralLinearGroup.map σ.toRingHom (SpecialLinearGroup.toGL A)) = 1 := by
          rw [map_mul, ← fieldExtension_conj_coordinateGLAction K, hA]
          exact hgg
        obtain ⟨c, hc⟩ := (coordinateGLAction_eq_one_iff _).mp h3
        have hc2 : c ^ 2 = 1 := by
          have h4 := congrArg GeneralLinearGroup.det hc
          rwa [det_scalar_two, map_mul, GeneralLinearGroup.map_det, hdetA, map_one,
            mul_one] at h4
        have hc1 : c = 1 := Units.ext (eq_one_of_sq_eq_one (by
          rw [← Units.val_pow_eq_pow_val, hc2, Units.val_one]))
        rw [← hc, hc1, map_one]
      have hσσx : ∀ x, σ (σ x) = x := fun x => by
        rw [← RingAut.mul_apply, hσσ]
        rfl
      have hAAm : (A : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K).map σ = 1 := by
        have h3 := congrArg Units.val hAσ
        simpa using h3
      set T : (Fin 2 → K) → (Fin 2 → K) := fun v =>
        (A : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => σ (v i) with hT
      have hTT : ∀ v, T (T v) = v := by
        intro v
        have hσAv : (fun i => σ (((A : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => σ (v i)) i)) =
            (A : Matrix (Fin 2) (Fin 2) K).map σ *ᵥ v := by
          funext i
          simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hσσx]
        simp only [hT]
        rw [hσAv, mulVec_mulVec, hAAm, one_mulVec]
      have hadd : ∀ v w, T (v + w) = T v + T w := fun v w => by
        simp only [hT, Pi.add_apply, map_add]
        rw [← mulVec_add]
        rfl
      have hsmul : ∀ (c : K) v, T (c • v) = σ c • T v := fun c v => by
        simp only [hT, Pi.smul_apply, smul_eq_mul, map_mul]
        rw [← mulVec_smul]
        rfl
      obtain ⟨x₀, hx₀⟩ : ∃ x₀, σ x₀ ≠ x₀ := by
        by_contra hall
        exact hσ (RingEquiv.ext fun x => by
          by_contra hx
          exact hall ⟨x, hx⟩)
      obtain ⟨H, hH⟩ := LinearFlag.exists_fixed_basis hσσx hx₀ T hadd hsmul hTT
      have hAH : SpecialLinearGroup.toGL A * GeneralLinearGroup.map σ.toRingHom H = H := by
        ext r c
        have h3 := congrFun (hH c) r
        simp only [hT, mulVec, dotProduct] at h3
        rw [← h3]
        simp [Matrix.mul_apply]
      refine ⟨coordinateGLAction K H, hρG H, ?_⟩
      rw [← hA, eq_mul_inv_of_mul_eq hAH, map_mul, map_inv,
        ← fieldExtension_conj_coordinateGLAction K]
      group
    ·
      obtain ⟨-, k, hk, hkcard⟩ := hfix (Subgroup.zpowers σ)
      have hord2σ : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ
      refine ⟨k, ?_, by rw [hkcard, Nat.card_zpowers, hord2σ]⟩
      rw [hk]
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro hx
        exact hx σ (Subgroup.mem_zpowers σ)
      · intro hx τ hτ
        have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (K ≃+* K) x :=
          Subgroup.zpowers_le.mpr hx
        exact hle hτ

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
