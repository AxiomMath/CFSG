module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityPureGraph

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FourGroupEvenCanonical
open UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace UnitaryFieldTransfer

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem fixedField_charP : CharP h.fixedField 2 :=
  finite_field_prime_power_characteristic Nat.prime_two h.one_le h.card_fixedField

theorem fixedField_finite : Finite h.fixedField :=
  Nat.finite_of_card_ne_zero (by rw [h.card_fixedField]; positivity)

theorem map_subtype_map_bar (M : Matrix (Fin n) (Fin n) h.fixedField) :
    (M.map h.fixedField.subtype).map h.bar = M.map h.fixedField.subtype :=
  Matrix.ext fun i j => (M i j).2

theorem map_subtype_injective :
    Function.Injective fun M : Matrix (Fin n) (Fin n) h.fixedField =>
      M.map h.fixedField.subtype :=
  Matrix.map_injective Subtype.val_injective

@[expose] def descendMatrix (M : Matrix (Fin n) (Fin n) K) (hM : M.map h.bar = M) :
    Matrix (Fin n) (Fin n) h.fixedField :=
  Matrix.of fun i j => ⟨M i j, congrFun (congrFun hM i) j⟩

theorem descendMatrix_map (M : Matrix (Fin n) (Fin n) K) (hM : M.map h.bar = M) :
    (descendMatrix h M hM).map h.fixedField.subtype = M :=
  Matrix.ext fun _ _ => rfl

theorem inv_map_bar {A : GL (Fin n) K} (hA : (A : Matrix (Fin n) (Fin n) K).map h.bar = A) :
    ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar = (A⁻¹ : GL (Fin n) K) := by
  have h1 : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar *
      (A : Matrix (Fin n) (Fin n) K) = 1 := by
    conv_lhs => rw [← hA]
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  calc ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar
      = ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar *
          (A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    _ = (A⁻¹ : GL (Fin n) K) := by rw [h1, Matrix.one_mul]

@[expose] def descendGL (A : GL (Fin n) K) (hA : (A : Matrix (Fin n) (Fin n) K).map h.bar = A) :
    GL (Fin n) h.fixedField where
  val := descendMatrix h A hA
  inv := descendMatrix h (A⁻¹ : GL (Fin n) K) (inv_map_bar h hA)
  val_inv := map_subtype_injective h (by
    simp only [Matrix.map_mul, descendMatrix_map, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _)])
  inv_val := map_subtype_injective h (by
    simp only [Matrix.map_mul, descendMatrix_map, Units.inv_mul,
      Matrix.map_one _ (map_zero _) (map_one _)])

theorem map_descendGL (A : GL (Fin n) K) (hA : (A : Matrix (Fin n) (Fin n) K).map h.bar = A) :
    GeneralLinearGroup.map h.fixedField.subtype (descendGL h A hA) = A :=
  Units.ext (descendMatrix_map h (A : Matrix (Fin n) (Fin n) K) hA)

theorem ringEquiv_mem_fixedField (φ : K ≃+* K) {x : K} (hx : x ∈ h.fixedField) :
    φ x ∈ h.fixedField := by
  rw [UnitaryFieldData.mem_fixedField] at hx ⊢
  rw [← map_bar_comm h φ, hx]

@[expose] def fixedRestrict : (K ≃+* K) →* (h.fixedField ≃+* h.fixedField) where
  toFun φ :=
    { toFun := fun x => ⟨φ x.1, ringEquiv_mem_fixedField h φ x.2⟩
      invFun := fun x => ⟨φ.symm x.1, ringEquiv_mem_fixedField h φ.symm x.2⟩
      left_inv := fun x => Subtype.ext (φ.symm_apply_apply x.1)
      right_inv := fun x => Subtype.ext (φ.apply_symm_apply x.1)
      map_mul' := fun x y => Subtype.ext (map_mul φ x.1 y.1)
      map_add' := fun x y => Subtype.ext (map_add φ x.1 y.1) }
  map_one' := RingEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := RingEquiv.ext fun _ => Subtype.ext rfl

theorem fixedRestrict_apply (φ : K ≃+* K) (x : h.fixedField) :
    ((fixedRestrict h φ x : h.fixedField) : K) = φ x.1 :=
  rfl

theorem fixedRestrict_bar {σ : K ≃+* K} (hσ : ∀ x, σ x = h.bar x) : fixedRestrict h σ = 1 :=
  RingEquiv.ext fun x => Subtype.ext (by rw [fixedRestrict_apply, hσ]; exact x.2)

theorem mem_zpowers_of_fixedRestrict_eq_one {σ : K ≃+* K} (hσ : ∀ x, σ x = h.bar x)
    {φ : K ≃+* K} (hφ : fixedRestrict h φ = 1) : φ ∈ zpowers σ := by
  have := h.finite
  refine mem_zpowers_of_fixed fun x hx => ?_
  have hxk : x ∈ h.fixedField := by
    rw [UnitaryFieldData.mem_fixedField, ← hσ]
    exact hx
  have h1 := congrArg Subtype.val (RingEquiv.congr_fun hφ ⟨x, hxk⟩)
  exact h1

theorem canonical_case_of_map {C : GL (Fin n) K} {Cl : GL (Fin n) h.fixedField}
    (hCl : (Cl : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = C)
    (hcase : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r) :
    (Cl : Matrix (Fin n) (Fin n) h.fixedField) = 1 ∨
      ∃ r, n = 2 * r ∧ (Cl : Matrix (Fin n) (Fin n) h.fixedField) = blockSwapJ n r := by
  rcases hcase with h1 | ⟨r, hr, hJ⟩
  · left
    apply map_subtype_injective h
    dsimp only
    rw [hCl, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  · right
    refine ⟨r, hr, map_subtype_injective h ?_⟩
    dsimp only
    rw [hCl, hJ]
    ext i j
    simp only [Matrix.map_apply, blockSwapJ, Matrix.of_apply]
    split_ifs <;> simp

section Isometry

variable {C : GL (Fin n) K} {Cl : GL (Fin n) h.fixedField}
  (hCl : (Cl : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = C)

include hCl in
theorem map_mem_primeFormUnitary {g : GL (Fin n) h.fixedField}
    (hg : g ∈ matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField)) :
    GeneralLinearGroup.map h.fixedField.subtype g ∈
      primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) := by
  rw [mem_primeFormUnitary]
  change (((g : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype).map h.bar)ᵀ *
    (C : Matrix (Fin n) (Fin n) K) *
      (g : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = C
  rw [map_subtype_map_bar, ← hCl, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
    mem_matrixIsometryGroup.mp hg]

@[expose] def fixedIsometryHom :
    matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField) →*
      primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) where
  toFun g := ⟨GeneralLinearGroup.map h.fixedField.subtype g, map_mem_primeFormUnitary h hCl g.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ (a : GL (Fin n) h.fixedField) b)

theorem coe_fixedIsometryHom
    (g : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField)) :
    ((fixedIsometryHom h hCl g : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) :
      GL (Fin n) K) = GeneralLinearGroup.map h.fixedField.subtype (g : GL (Fin n) h.fixedField) :=
  rfl

variable (hcan : IsCanonicalGram (Cl : Matrix (Fin n) (Fin n) h.fixedField))

include hcan in
theorem glAut_mem_isometry (ψ : h.fixedField ≃+* h.fixedField) {g : GL (Fin n) h.fixedField}
    (hg : g ∈ matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField)) :
    glAut ψ g ∈ matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField) := by
  have e : glAut ψ g = GeneralLinearGroup.map (ψ : h.fixedField →+* h.fixedField) g :=
    Units.ext rfl
  rw [e]
  rw [mem_matrixIsometryGroup_iff_inverseTranspose] at hg ⊢
  rw [← GeneralLinearGroup.map_inverseTranspose, hg, map_mul, map_mul, map_inv, hcan.map_eq]

@[expose] def isometryFieldAct : (h.fixedField ≃+* h.fixedField) →*
    MulAut (matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField)) where
  toFun ψ :=
    { toFun := fun g => ⟨glAut ψ g, glAut_mem_isometry h hcan ψ g.2⟩
      invFun := fun g => ⟨glAut ψ⁻¹ g, glAut_mem_isometry h hcan ψ⁻¹ g.2⟩
      left_inv := fun g => Subtype.ext (by
        change glAut ψ⁻¹ (glAut ψ (g : GL (Fin n) h.fixedField)) = g
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
      right_inv := fun g => Subtype.ext (by
        change glAut ψ (glAut ψ⁻¹ (g : GL (Fin n) h.fixedField)) = g
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply])
      map_mul' := fun g g' => Subtype.ext (map_mul (glAut ψ) (g : GL (Fin n) h.fixedField) g') }
  map_one' := MulEquiv.ext fun g => Subtype.ext (by
    change glAut 1 (g : GL (Fin n) h.fixedField) = g
    rw [map_one]
    rfl)
  map_mul' ψ τ := MulEquiv.ext fun g => Subtype.ext (by
    change glAut (ψ * τ) (g : GL (Fin n) h.fixedField) =
      glAut ψ (glAut τ (g : GL (Fin n) h.fixedField))
    rw [map_mul]
    rfl)

@[expose] def fixedAct :
    (K ≃+* K) →* MulAut (matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField)) :=
  (isometryFieldAct h hcan).comp (fixedRestrict h)

variable (hC : IsPrimeFormGram C)

@[expose] def transferPsi :
    matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField) ⋊[fixedAct h hcan] (K ≃+* K) →*
      MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)) :=
  (primeFormPsi h hC).comp (SemidirectProduct.map (fixedIsometryHom h hCl) (MonoidHom.id _)
    fun _ => MonoidHom.ext fun _ => Subtype.ext (Units.ext (Matrix.ext fun _ _ => rfl)))

theorem transferPsi_apply (x : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField) ⋊[
    fixedAct h hcan] (K ≃+* K)) :
    transferPsi h hCl hcan hC x = primeFormPsi h hC ⟨fixedIsometryHom h hCl x.left, x.right⟩ :=
  rfl

@[expose] def transferTheta :
    matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField) ⋊[fixedAct h hcan] (K ≃+* K) →*
      MulAut (projectiveSL n h.fixedField) :=
  SemidirectProduct.lift ((conjAut n h.fixedField).comp (matrixIsometryGroup _).subtype)
    ((fieldAut n h.fixedField).comp (fixedRestrict h)) fun φ => MonoidHom.ext fun g => by
      obtain ⟨-, -, hfc, -⟩ := standard_automorphism_transport (n := n) (K := h.fixedField)
      change conjAut n h.fixedField (glAut (fixedRestrict h φ) (g : GL (Fin n) h.fixedField)) =
        fieldAut n h.fixedField (fixedRestrict h φ) * conjAut n h.fixedField g *
          (fieldAut n h.fixedField (fixedRestrict h φ))⁻¹
      rw [hfc]
      rfl

theorem transferTheta_apply (x : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField) ⋊[
    fixedAct h hcan] (K ≃+* K)) :
    transferTheta h hcan x = conjAut n h.fixedField (x.left : GL (Fin n) h.fixedField) *
      fieldAut n h.fixedField (fixedRestrict h x.right) :=
  rfl

theorem eq_one_of_map_eq_scalar (hn : 3 ≤ n)
    {g : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField)} {c : Kˣ}
    (hc : GeneralLinearGroup.map h.fixedField.subtype (g : GL (Fin n) h.fixedField) =
      GeneralLinearGroup.scalar (Fin n) c) : g = 1 := by
  have := fixedField_charP h
  have : NeZero n := ⟨by omega⟩
  obtain ⟨i₀, -⟩ : ∃ i : Fin n, (i : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  have hgm : ((g : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField).map
      h.fixedField.subtype = Matrix.scalar (Fin n) (c : K) := by
    have h1 := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K)) hc
    rw [GeneralLinearGroup.coe_scalar] at h1
    exact h1
  have h00 : ((((g : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField) i₀ i₀ :
      h.fixedField) : K) = c := by
    have := congrFun (congrFun hgm i₀) i₀
    simpa [Matrix.scalar_apply] using this
  have hne : ((g : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField) i₀ i₀ ≠ 0 := by
    intro h0
    rw [h0] at h00
    exact c.ne_zero (by rw [← h00]; rfl)
  have hgs : (g : GL (Fin n) h.fixedField) =
      GeneralLinearGroup.scalar (Fin n) (Units.mk0 _ hne) := by
    apply Units.ext
    apply map_subtype_injective h
    rw [GeneralLinearGroup.coe_scalar]
    change _ = (Matrix.scalar (Fin n) (_ : h.fixedField)).map h.fixedField.subtype
    dsimp only
    rw [hgm, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext j
    exact h00.symm
  have hc1 := eq_one_of_scalar_mem_matrixIsometryGroup (C := Cl) (hgs ▸ g.2)
  apply Subtype.ext
  rw [hgs, hc1, map_one]
  rfl

theorem transferPsi_injective (hn : 3 ≤ n) : Function.Injective (transferPsi h hCl hcan hC) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨g, φ⟩ hx
  rw [transferPsi_apply, primeFormPsi_eq_one_iff h hC hn] at hx
  obtain ⟨hφ, c, -, hc⟩ := hx
  have hg1 : g = 1 := eq_one_of_map_eq_scalar h hn hc
  change φ = RingEquiv.refl K at hφ
  rw [hg1, hφ]
  rfl

variable {σ : K ≃+* K} (hσ : ∀ x, σ x = h.bar x)

include hσ in
theorem glAut_map_subtype (g : GL (Fin n) h.fixedField) :
    glAut σ (GeneralLinearGroup.map h.fixedField.subtype g) =
      GeneralLinearGroup.map h.fixedField.subtype g := by
  apply Units.ext
  rw [coe_glAut]
  exact Matrix.ext fun i j => (hσ _).trans ((g : Matrix (Fin n) (Fin n) h.fixedField) i j).2

include hσ in
theorem transferPsi_mem_centralizer
    (x : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField) ⋊[fixedAct h hcan]
      (K ≃+* K)) :
    transferPsi h hCl hcan hC x ∈ centralizer {primeFormFieldHom h hC σ} := by
  have := h.finite
  rw [mem_centralizer_singleton_iff, transferPsi_apply, primeFormPsi_apply]
  have hA : primeFormFieldU h hC σ (fixedIsometryHom h hCl x.left) =
      fixedIsometryHom h hCl x.left := Subtype.ext (glAut_map_subtype h hσ _)
  have h1 := primeFormField_conj_eq h hC σ (fixedIsometryHom h hCl x.left)
  rw [hA] at h1
  have h2 : primeFormConjHom h _ (fixedIsometryHom h hCl x.left) * primeFormFieldHom h hC σ =
      primeFormFieldHom h hC σ * primeFormConjHom h _ (fixedIsometryHom h hCl x.left) := by
    conv_lhs => rw [← h1]
    group
  have hcomm : primeFormFieldHom h hC x.right * primeFormFieldHom h hC σ =
      primeFormFieldHom h hC σ * primeFormFieldHom h hC x.right := by
    rw [← map_mul, ← map_mul, ringAut_commute]
  rw [mul_assoc, hcomm, ← mul_assoc, h2, mul_assoc]

include hσ in
theorem exists_transferPsi_eq (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    {α : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))}
    (hα : α ∈ centralizer {primeFormFieldHom h hC σ}) :
    ∃ x, transferPsi h hCl hcan hC x = α := by
  have : CharP K 2 := h.charP
  have := h.finite
  have := fixedField_charP h
  have := fixedField_finite h
  obtain ⟨⟨A, φ⟩, rfl⟩ := primeFormPsi_surjective h hC hn hq α
  rw [mem_centralizer_singleton_iff, primeFormPsi_apply] at hα
  have hφσ : primeFormFieldHom h hC φ * primeFormFieldHom h hC σ =
      primeFormFieldHom h hC σ * primeFormFieldHom h hC φ := by
    rw [← map_mul, ← map_mul, ringAut_commute]
  have h2 : primeFormConjHom h _ A * primeFormFieldHom h hC σ =
      primeFormFieldHom h hC σ * primeFormConjHom h _ A := by
    have e := hα
    rw [mul_assoc, hφσ, ← mul_assoc, ← mul_assoc] at e
    exact mul_right_cancel e
  have h1 : primeFormConjHom h _ (primeFormFieldU h hC σ A) = primeFormConjHom h _ A := by
    rw [← primeFormField_conj_eq h hC σ A, ← h2, mul_inv_cancel_right]
  have h3 : primeFormPsi h hC ⟨A⁻¹ * primeFormFieldU h hC σ A, RingEquiv.refl K⟩ = 1 := by
    rw [primeFormPsi_apply, map_mul, h1, map_inv, inv_mul_cancel, one_mul]
    exact map_one (primeFormFieldHom h hC)
  obtain ⟨-, μ, hμN, hμ⟩ := (primeFormPsi_eq_one_iff h hC hn _).mp h3
  have hAbar : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar =
      (μ : K) • ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have e2 : (A : GL (Fin n) K)⁻¹ * glAut σ (A : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) μ := hμ
    have e1 : glAut σ (A : GL (Fin n) K) =
        (A : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) μ := by
      rw [← e2, mul_inv_cancel_left]
    have e3 := congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K)) e1
    simp only [coe_glAut, Units.val_mul, GeneralLinearGroup.coe_scalar] at e3
    have hmap : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ =
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar :=
      Matrix.ext fun i j => hσ _
    rw [← hmap, e3, Matrix.scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  obtain ⟨b, hb0, hbμ⟩ := h.exists_div_bar_eq hμN
  have hbb0 : h.bar b ≠ 0 := (h.bar_eq_zero_iff).not.mpr hb0
  have hNb0 : h.norm b ≠ 0 := mul_ne_zero hb0 hbb0
  obtain ⟨c', hc'⟩ := FiniteField.isSquare_of_char_two (ringChar.eq h.fixedField 2)
    (⟨(h.norm b)⁻¹, inv_mem (h.norm_mem_fixedField b)⟩ : h.fixedField)
  have hcc : (c' : K) * c' = (h.norm b)⁻¹ := (congrArg Subtype.val hc').symm
  have hcbar : h.bar (c' : K) = c' := c'.2
  have hc0 : (c' : K) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcc
    exact inv_ne_zero hNb0 hcc.symm
  have ht0 : (c' : K) * b ≠ 0 := mul_ne_zero hc0 hb0
  have htN : h.norm ((c' : K) * b) = 1 := by
    rw [UnitaryFieldData.norm, map_mul, hcbar]
    calc (c' : K) * b * (c' * h.bar b) = c' * c' * (b * h.bar b) := by ring
      _ = 1 := by rw [hcc]; exact inv_mul_cancel₀ hNb0
  have htbar : h.bar ((c' : K) * b) * (μ : K) = c' * b := by
    rw [← hbμ, map_mul, hcbar]
    field_simp
  have huU : GeneralLinearGroup.scalar (Fin n) (Units.mk0 _ ht0) ∈
      primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) := by
    rw [mem_primeFormUnitary, GeneralLinearGroup.coe_scalar, scalar_barTranspose_mul_mul,
      Units.val_mk0, htN, one_smul]
  obtain ⟨g', hg'⟩ : ∃ g' : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K),
      g' = ⟨_, huU⟩ * A := ⟨_, rfl⟩
  have hg'm : ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((c' : K) * b) • ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [hg', Subgroup.coe_mul, Units.val_mul]
    change ((GeneralLinearGroup.scalar (Fin n) (Units.mk0 _ ht0) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * _ = _
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← smul_one_eq_diagonal,
      Matrix.smul_mul, Matrix.one_mul, Units.val_mk0]
  have hg'bar : ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar =
      (g' : GL (Fin n) K) := by
    rw [hg'm]
    ext i j
    have := congrFun (congrFun hAbar i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul] at this ⊢
    rw [this, ← mul_assoc, ← map_mul, htbar]
  have hgO : descendGL h (g' : GL (Fin n) K) hg'bar ∈
      matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField) := by
    rw [mem_matrixIsometryGroup]
    apply map_subtype_injective h
    simp only [Matrix.map_mul, Matrix.transpose_map]
    rw [hCl]
    have e : ((descendGL h (g' : GL (Fin n) K) hg'bar : GL (Fin n) h.fixedField) :
        Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype =
          ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := descendMatrix_map h _ hg'bar
    rw [e]
    have := mem_primeFormUnitary.mp g'.2
    rw [hg'bar] at this
    exact this
  refine ⟨⟨⟨_, hgO⟩, φ⟩, ?_⟩
  rw [transferPsi_apply]
  have hfix : fixedIsometryHom h hCl ⟨_, hgO⟩ = g' :=
    Subtype.ext (map_descendGL h (g' : GL (Fin n) K) hg'bar)
  have hu1 : primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) ⟨_, huU⟩ = 1 := by
    have h5 := (primeFormPsi_eq_one_iff h hC hn ⟨⟨_, huU⟩, RingEquiv.refl K⟩).mpr
      ⟨rfl, Units.mk0 _ ht0, htN, rfl⟩
    rwa [primeFormPsi_apply, show RingEquiv.refl K = (1 : K ≃+* K) from rfl, map_one,
      mul_one] at h5
  change primeFormPsi h hC ⟨fixedIsometryHom h hCl ⟨_, hgO⟩, φ⟩ = primeFormPsi h hC ⟨A, φ⟩
  rw [hfix, primeFormPsi_apply, primeFormPsi_apply, hg', map_mul, hu1, one_mul]

include hσ in
theorem range_transferPsi (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2)) :
    (transferPsi h hCl hcan hC).range = centralizer {primeFormFieldHom h hC σ} := by
  ext α
  constructor
  · rintro ⟨x, rfl⟩
    exact transferPsi_mem_centralizer h hCl hcan hC hσ x
  · intro hα
    exact exists_transferPsi_eq h hCl hcan hC hσ hn hq hα

@[expose] def transferEquiv (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2)) :
    (matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField) ⋊[fixedAct h hcan]
      (K ≃+* K)) ≃* centralizer {primeFormFieldHom h hC σ} :=
  (MonoidHom.ofInjective (transferPsi_injective h hCl hcan hC hn)).trans
    (MulEquiv.subgroupCongr (range_transferPsi h hCl hcan hC hσ hn hq))

theorem coe_transferEquiv (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    (x : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField) ⋊[fixedAct h hcan]
      (K ≃+* K)) :
    (transferEquiv h hCl hcan hC hσ hn hq x : MulAut (primeFormP h _)) =
      transferPsi h hCl hcan hC x :=
  rfl

@[expose] def transferHom (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2)) :
    centralizer {primeFormFieldHom h hC σ} →* MulAut (projectiveSL n h.fixedField) :=
  (transferTheta h hcan).comp (transferEquiv h hCl hcan hC hσ hn hq).symm.toMonoidHom

theorem transferHom_transferEquiv (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    (x : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField) ⋊[fixedAct h hcan]
      (K ≃+* K)) :
    transferHom h hCl hcan hC hσ hn hq (transferEquiv h hCl hcan hC hσ hn hq x) =
      transferTheta h hcan x := by
  change transferTheta h hcan ((transferEquiv h hCl hcan hC hσ hn hq).symm
    (transferEquiv h hCl hcan hC hσ hn hq x)) = _
  rw [MulEquiv.symm_apply_apply]

theorem transferTheta_eq_one_iff (hn : 3 ≤ n)
    (x : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField) ⋊[fixedAct h hcan]
      (K ≃+* K)) :
    transferTheta h hcan x = 1 ↔ x.left = 1 ∧ fixedRestrict h x.right = 1 := by
  have := fixedField_charP h
  have := fixedField_finite h
  have : NeZero n := ⟨by omega⟩
  rw [transferTheta_apply]
  constructor
  · intro h1
    obtain ⟨hφ, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ h1
    refine ⟨?_, hφ⟩
    have hc1 := eq_one_of_scalar_mem_matrixIsometryGroup (C := Cl) (hc ▸ x.left.2)
    apply Subtype.ext
    rw [← hc, hc1, map_one]
    rfl
  · rintro ⟨h1, h2⟩
    rw [h1, h2, map_one, OneMemClass.coe_one, map_one, one_mul]

end Isometry

end UnitaryFieldTransfer

open UnitaryFieldTransfer

theorem even_unitary_canonical_field_centralizer_transfer {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (hcase : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r)
    (Cl : GL (Fin n) h.fixedField)
    (hCl : (Cl : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = C)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) :
    (∀ α : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)),
      α ∈ centralizer {primeFormFieldHom h hC σ} ↔
        ∃ (g : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField)) (φ : K ≃+* K),
          α = primeFormPsi h hC ⟨fixedIsometryHom h hCl g, φ⟩) ∧
    (∀ (g g' : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField))
      (φ φ' : K ≃+* K), primeFormPsi h hC ⟨fixedIsometryHom h hCl g, φ⟩ =
        primeFormPsi h hC ⟨fixedIsometryHom h hCl g', φ'⟩ → g = g' ∧ φ = φ') ∧
    Function.Injective ((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp
      (fixedIsometryHom h hCl)) ∧
    ((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp (fixedIsometryHom h hCl)).range ≤
      inner (primeFormP h (C : Matrix (Fin n) (Fin n) K)) ∧
    ((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp (fixedIsometryHom h hCl)).range ≤
      centralizer {primeFormFieldHom h hC σ} ∧
    (((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp
      (fixedIsometryHom h hCl)).range.subgroupOf (centralizer {primeFormFieldHom h hC σ})).Normal ∧
    ∃ Θ : centralizer {primeFormFieldHom h hC σ} →* MulAut (projectiveSL n h.fixedField),
      (∀ (g : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField)) (φ : K ≃+* K)
        (hα : primeFormPsi h hC ⟨fixedIsometryHom h hCl g, φ⟩ ∈
          centralizer {primeFormFieldHom h hC σ}),
        Θ ⟨_, hα⟩ = conjAut n h.fixedField g * fieldAut n h.fixedField (fixedRestrict h φ)) ∧
      Θ.range ≤ centralizer {conjAut n h.fixedField Cl * dualAut n h.fixedField} ∧
      Θ.ker = (zpowers (primeFormFieldHom h hC σ)).subgroupOf
        (centralizer {primeFormFieldHom h hC σ}) ∧
      orderOf (primeFormFieldHom h hC σ) = 2 ∧
      (((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp
        (fixedIsometryHom h hCl)).range.subgroupOf (centralizer {primeFormFieldHom h hC σ})).map Θ =
          (matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField)).map
            (conjAut n h.fixedField) ∧
      ∃ e : ((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp
          (fixedIsometryHom h hCl)).range ≃*
          (matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField)).map
            (conjAut n h.fixedField),
        ∀ (x : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)))
          (hx : x ∈ ((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp
            (fixedIsometryHom h hCl)).range)
          (hxM : x ∈ centralizer {primeFormFieldHom h hC σ}),
          (e ⟨x, hx⟩ : MulAut (projectiveSL n h.fixedField)) = Θ ⟨x, hxM⟩ := by
  have := fixedField_charP h
  have := fixedField_finite h
  have := h.finite
  have hcaseL := canonical_case_of_map h hCl hcase
  have hcan : IsCanonicalGram (Cl : Matrix (Fin n) (Fin n) h.fixedField) := by
    rcases hcaseL with h1 | ⟨r, hr, hJ⟩
    · rw [h1]
      exact isCanonicalGram_one
    · rw [hJ]
      exact isCanonicalGram_blockSwapJ (by omega)
  have hinj := transferPsi_injective h hCl hcan hC hn
  have hrange := range_transferPsi h hCl hcan hC hσ hn hq
  have hconj : ∀ g, primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) (fixedIsometryHom h hCl g) =
      transferPsi h hCl hcan hC (SemidirectProduct.inl g) := by
    intro g
    rw [transferPsi_apply, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      primeFormPsi_apply, map_one, mul_one]
  have hgamma : transferPsi h hCl hcan hC (SemidirectProduct.inr σ) = primeFormFieldHom h hC σ := by
    rw [transferPsi_apply, SemidirectProduct.left_inr, SemidirectProduct.right_inr,
      primeFormPsi_apply, map_one, map_one, one_mul]
  have hinjU : Function.Injective ((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp
      (fixedIsometryHom h hCl)) := by
    intro a b hab
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hconj, hconj] at hab
    exact SemidirectProduct.inl_injective (hinj hab)
  refine ⟨fun α => ?_, fun g g' φ φ' he => ?_, hinjU, ?_, ?_, ?_, ?_⟩
  · rw [← hrange]
    constructor
    · rintro ⟨⟨g, φ⟩, rfl⟩
      exact ⟨g, φ, rfl⟩
    · rintro ⟨g, φ, rfl⟩
      exact ⟨⟨g, φ⟩, rfl⟩
  · have := hinj (a₁ := ⟨g, φ⟩) (a₂ := ⟨g', φ'⟩) he
    exact ⟨congrArg SemidirectProduct.left this, congrArg SemidirectProduct.right this⟩
  · rintro _ ⟨g, rfl⟩
    have hdet : ((GeneralLinearGroup.map h.fixedField.subtype (g : GL (Fin n) h.fixedField) :
        GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
      change (((g : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField).map
        h.fixedField.subtype).det = 1
      rw [show ((g : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField).map
          h.fixedField.subtype = h.fixedField.subtype.mapMatrix
            ((g : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField) from rfl,
        ← RingHom.map_det, det_eq_one_of_mem_matrixIsometryGroup (C := Cl) g.2, map_one]
    exact (mem_inner_primeFormP h _ _).mpr
      ⟨⟨_, (mem_gramSU_iff_unitary h).mpr ⟨(fixedIsometryHom h hCl g).2, hdet⟩⟩, rfl⟩
  · rintro _ ⟨g, rfl⟩
    rw [MonoidHom.comp_apply, hconj, ← hrange]
    exact ⟨_, rfl⟩
  · refine ⟨fun x hx y => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨g, hg⟩ := hx
    rw [MonoidHom.comp_apply] at hg
    obtain ⟨z, hz⟩ : ∃ z, transferPsi h hCl hcan hC z = (y : MulAut _) := by
      rw [← MonoidHom.mem_range, hrange]
      exact y.2
    have hw : (z * SemidirectProduct.inl g * z⁻¹).right = 1 := by simp
    refine ⟨(z * SemidirectProduct.inl g * z⁻¹).left, ?_⟩
    have e1 : SemidirectProduct.inl (z * SemidirectProduct.inl g * z⁻¹).left =
        z * SemidirectProduct.inl g * z⁻¹ := by
      conv_rhs =>
        rw [← SemidirectProduct.inl_left_mul_inr_right (z * SemidirectProduct.inl g * z⁻¹)]
      rw [hw, map_one, mul_one]
    rw [MonoidHom.comp_apply, hconj, e1, map_mul, map_mul, map_inv, hz, ← hconj, hg]
    rfl
  refine ⟨transferHom h hCl hcan hC hσ hn hq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g φ hα
    have e1 : (⟨_, hα⟩ : centralizer {primeFormFieldHom h hC σ}) =
        transferEquiv h hCl hcan hC hσ hn hq ⟨g, φ⟩ := Subtype.ext rfl
    rw [e1, transferHom_transferEquiv, transferTheta_apply]
  · rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := (transferEquiv h hCl hcan hC hσ hn hq).surjective y
    rw [transferHom_transferEquiv, transferTheta_apply, mem_centralizer_singleton_iff]
    have hc1 := (commute_pureGraph_conjAut_iff hcan hn (x.left : GL (Fin n) h.fixedField)).mpr
      ⟨_, x.left.2, rfl⟩
    have hc2 := commute_pureGraph_fieldAut hcan (fixedRestrict h x.right)
    exact (hc1.mul_right hc2).eq.symm
  · ext y
    obtain ⟨x, rfl⟩ := (transferEquiv h hCl hcan hC hσ hn hq).surjective y
    rw [MonoidHom.mem_ker, transferHom_transferEquiv, transferTheta_eq_one_iff h hcan hn,
      mem_subgroupOf, coe_transferEquiv]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (mem_zpowers_of_fixedRestrict_eq_one h hσ h2)
      have hx : x = SemidirectProduct.inr σ ^ m := by
        rw [← SemidirectProduct.inl_left_mul_inr_right x, h1, map_one, one_mul, ← hm, map_zpow]
      rw [hx, map_zpow, hgamma]
      exact zpow_mem (mem_zpowers _) m
    · intro hy
      obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hy
      rw [← hgamma, ← map_zpow] at hm
      have hx := hinj hm
      rw [← hx, ← map_zpow]
      refine ⟨SemidirectProduct.left_inr _, ?_⟩
      rw [SemidirectProduct.right_inr, map_zpow, fixedRestrict_bar h hσ, _root_.one_zpow]
  · rw [← hgamma, orderOf_injective _ hinj, orderOf_injective _ SemidirectProduct.inr_injective]
    apply orderOf_eq_prime
    · refine RingEquiv.ext fun x => ?_
      rw [pow_two]
      change σ (σ x) = x
      rw [hσ, hσ, h.bar_bar]
    · intro h1
      obtain ⟨c, hc⟩ := h.exists_bar_ne
      exact hc (by rw [← hσ, h1]; rfl)
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, mem_subgroupOf] at hx
      obtain ⟨g, hg⟩ := hx
      rw [MonoidHom.comp_apply, hconj] at hg
      have e1 : x = transferEquiv h hCl hcan hC hσ hn hq (SemidirectProduct.inl g) :=
        Subtype.ext (by rw [coe_transferEquiv, ← hg])
      rw [e1, transferHom_transferEquiv, transferTheta_apply, SemidirectProduct.left_inl,
        SemidirectProduct.right_inl, map_one, map_one, mul_one]
      exact mem_map_of_mem _ g.2
    · rintro ⟨g, hg, rfl⟩
      refine ⟨transferEquiv h hCl hcan hC hσ hn hq (SemidirectProduct.inl ⟨g, hg⟩), ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_subgroupOf, coe_transferEquiv]
        exact ⟨⟨g, hg⟩, by rw [MonoidHom.comp_apply, hconj]⟩
      · rw [transferHom_transferEquiv, transferTheta_apply, SemidirectProduct.left_inl,
          SemidirectProduct.right_inl, map_one, map_one, mul_one]
  · have hinjL := (even_linear_canonical_graph_symplectic_centralizers h.one_le
      h.card_fixedField hn Cl hcaseL).1
    have hrangeL : ((conjAut n h.fixedField).comp (matrixIsometryGroup
        (Cl : Matrix (Fin n) (Fin n) h.fixedField)).subtype).range =
          (matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField)).map
            (conjAut n h.fixedField) := by
      rw [MonoidHom.range_comp, range_subtype]
    refine ⟨(MonoidHom.ofInjective hinjU).symm.trans
      ((MonoidHom.ofInjective hinjL).trans (MulEquiv.subgroupCongr hrangeL)), ?_⟩
    intro x hx hxM
    obtain ⟨g, rfl⟩ := hx
    have h1 : (MonoidHom.ofInjective hinjU).symm ⟨_, ⟨g, rfl⟩⟩ = g := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    have h2 : (⟨_, hxM⟩ : centralizer {primeFormFieldHom h hC σ}) =
        transferEquiv h hCl hcan hC hσ hn hq (SemidirectProduct.inl g) :=
      Subtype.ext (by rw [coe_transferEquiv, ← hconj]; rfl)
    rw [MulEquiv.trans_apply, h1, h2, transferHom_transferEquiv, transferTheta_apply,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, map_one, mul_one]
    rfl

end CFSG.ComponentClassification.UnbalancedCatalog
