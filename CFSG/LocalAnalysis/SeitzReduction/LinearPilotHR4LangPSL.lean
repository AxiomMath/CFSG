module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR4Lang
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLinearOuter

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

section Generic

variable {X : Type*} [Group X]

theorem sq_conj_mul_eq_one {α : MulAut X} (hα : α ^ 2 = 1) {z : X} (hz : α z = z⁻¹) :
    (MulAut.conj z * α) ^ 2 = 1 := by
  have h1 : α * MulAut.conj z = MulAut.conj (α z) * α := by
    rw [← mulAut_mul_conj_mul_inv_eq_conj α z, inv_mul_cancel_right]
  calc (MulAut.conj z * α) ^ 2 = MulAut.conj z * (α * MulAut.conj z) * α := by
        rw [sq]; group
    _ = MulAut.conj z * MulAut.conj (α z) * (α * α) := by rw [h1]; group
    _ = 1 := by rw [hz, ← map_mul, mul_inv_cancel, map_one, one_mul, ← sq, hα]

theorem exists_inv_apply_mul_eq_of_conj_eq
    (hinj : Function.Injective (MulAut.conj : X →* MulAut X)) {α : MulAut X} (hα : α ^ 2 = 1)
    {z x : X} (h : MulAut.conj x * α * (MulAut.conj x)⁻¹ = MulAut.conj z * α) :
    ∃ w, (α w)⁻¹ * w = z := by
  have h1 : α * (MulAut.conj x)⁻¹ = MulAut.conj ((α x)⁻¹) * α := by
    calc α * (MulAut.conj x)⁻¹ = α * MulAut.conj x⁻¹ * α⁻¹ * α := by
          rw [map_inv, inv_mul_cancel_right]
      _ = MulAut.conj ((α x)⁻¹) * α := by
          rw [mulAut_mul_conj_mul_inv_eq_conj α x⁻¹, map_inv]
  have h2 : MulAut.conj (x * (α x)⁻¹) * α = MulAut.conj z * α := by
    rw [← h, map_mul, mul_assoc, ← h1, mul_assoc]
  have h3 : x * (α x)⁻¹ = z := hinj (mul_right_cancel h2)
  refine ⟨(α x)⁻¹, ?_⟩
  have hαα : α (α x) = x := by rw [← MulAut.mul_apply, ← sq, hα, MulAut.one_apply]
  rw [map_inv, hαα, inv_inv, h3]

end Generic

section Cyclic

variable {M : Type*} [CommGroup M]

theorem exists_fixed_mul_pow_field {u n : ℕ} (hu : 1 ≤ u) {a c : M} (ha : a ^ (4 * u ^ 2) = a)
    (hac : a ^ (2 * u) = a * c ^ n) :
    ∃ a₁ l : M, a₁ ^ (2 * u) = a₁ ∧ a = a₁ * l ^ n := by
  have hcn : c ^ n * a = a ^ (2 * u) := by rw [hac, mul_comm]
  have hpm : c ^ (n * (2 * u + 1)) = 1 := by
    have e1 : c ^ (n * (2 * u + 1)) * a ^ (2 * u + 1) = a ^ (2 * u * (2 * u + 1)) := by
      rw [pow_mul, ← mul_pow, hcn, ← pow_mul]
    have e2 : a ^ (2 * u * (2 * u + 1)) = a ^ (2 * u + 1) := by
      have : 2 * u * (2 * u + 1) = 4 * u ^ 2 + 2 * u := by ring
      rw [this, pow_add, ha, ← pow_succ']
    rw [e2] at e1
    exact mul_eq_right.1 e1
  refine ⟨a * ((c ^ u) ^ n)⁻¹, c ^ u, ?_, by rw [inv_mul_cancel_right]⟩
  rw [mul_pow, hac, inv_pow, ← pow_mul, ← pow_mul, ← pow_mul]
  have e3 : u * (n * (2 * u)) = n * (1 + u) + n * (2 * u + 1) * (u - 1) := by
    obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  rw [e3, pow_add, pow_mul c (n * (2 * u + 1)), hpm, one_pow, mul_one,
    show n * (1 + u) = n + u * n by ring, pow_add, _root_.mul_inv_rev,
    mul_comm (c ^ (u * n))⁻¹ (c ^ n)⁻¹, mul_assoc, mul_inv_cancel_left]

theorem exists_fixed_mul_pow_graphField {u n : ℕ} (hu : 1 ≤ u) {a c : M}
    (ha : a ^ (4 * u ^ 2) = a) (hac : a ^ (2 * u + 1) * c ^ n = 1) :
    ∃ a₁ l : M, a₁ ^ (2 * u + 1) = 1 ∧ a = a₁ * l ^ n := by
  have hcn : c ^ n = (a ^ (2 * u + 1))⁻¹ := eq_inv_of_mul_eq_one_right hac
  have hpm : c ^ (n * (2 * u - 1)) = 1 := by
    rw [pow_mul, hcn, inv_pow, ← pow_mul]
    have : (2 * u + 1) * (2 * u - 1) + 1 = 4 * u ^ 2 := by
      obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
      simp only [show 2 * (v + 1) - 1 = 2 * v + 1 by omega]
      ring
    have h1 : a ^ ((2 * u + 1) * (2 * u - 1)) * a = a := by rw [← pow_succ, this, ha]
    rw [mul_eq_right.1 h1, inv_one]
  refine ⟨a * ((c ^ (u - 1)) ^ n)⁻¹, c ^ (u - 1), ?_, by rw [inv_mul_cancel_right]⟩
  rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, ← inv_inv (a ^ (2 * u + 1)), ← hcn, ← mul_inv,
    inv_eq_one, ← pow_add]
  have e : n + (u - 1) * (n * (2 * u + 1)) = n * (2 * u - 1) * u := by
    obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
    simp only [Nat.add_sub_cancel, show 2 * (v + 1) - 1 = 2 * v + 1 by omega]
    ring
  rw [e, pow_mul, hpm, one_pow]

end Cyclic

section Matrices

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def langDiag (i₀ : Fin n) (d : Kˣ) : GL (Fin n) K where
  val := diagonal (Function.update (1 : Fin n → K) i₀ (d : K))
  inv := diagonal (Function.update (1 : Fin n → K) i₀ ((d⁻¹ : Kˣ) : K))
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    by_cases h : i = i₀
    · subst h
      simp
    · simp [Function.update_of_ne h]
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    by_cases h : i = i₀
    · subst h
      simp
    · simp [Function.update_of_ne h]

theorem coe_langDiag (i₀ : Fin n) (d : Kˣ) :
    ((langDiag i₀ d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal (Function.update (1 : Fin n → K) i₀ (d : K)) :=
  rfl

theorem det_langDiag (i₀ : Fin n) (d : Kˣ) :
    GeneralLinearGroup.det (langDiag i₀ d : GL (Fin n) K) = d := by
  ext
  rw [GeneralLinearGroup.val_det_apply, coe_langDiag, det_diagonal,
    Finset.prod_update_of_mem (Finset.mem_univ i₀)]
  simp

theorem inverseTranspose_langDiag (i₀ : Fin n) (d : Kˣ) :
    GeneralLinearGroup.inverseTranspose (langDiag i₀ d : GL (Fin n) K) = langDiag i₀ d⁻¹ := by
  ext i j
  rw [GeneralLinearGroup.coe_inverseTranspose]
  change (diagonal (Function.update (1 : Fin n → K) i₀ ((d⁻¹ : Kˣ) : K)))ᵀ i j = _
  rw [diagonal_transpose]
  rfl

theorem map_langDiag (σ : K ≃+* K) (i₀ : Fin n) {d d' : Kˣ} (hd : σ (d : K) = d') :
    GeneralLinearGroup.map (σ : K →+* K) (langDiag i₀ d) = langDiag i₀ d' := by
  ext i j
  rw [GeneralLinearGroup.map_apply, coe_langDiag, coe_langDiag]
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq, diagonal_apply_eq]
    by_cases h : i = i₀
    · subst h
      rw [Function.update_self, Function.update_self]
      exact hd
    · rw [Function.update_of_ne h, Function.update_of_ne h]
      simp
  · rw [diagonal_apply_ne _ hij, diagonal_apply_ne _ hij, RingHom.coe_coe, map_zero]

theorem val_det_map (σ : K ≃+* K) (A : GL (Fin n) K) :
    (GeneralLinearGroup.det (GeneralLinearGroup.map (σ : K →+* K) A) : K) =
      σ (GeneralLinearGroup.det A : K) := by
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply,
    GeneralLinearGroup.val_map_apply]
  exact (RingHom.map_det (σ : K →+* K) (A : Matrix (Fin n) (Fin n) K)).symm

theorem det_inverseTranspose (A : GL (Fin n) K) :
    GeneralLinearGroup.det (GeneralLinearGroup.inverseTranspose A) =
      (GeneralLinearGroup.det A)⁻¹ := by
  ext
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_inverseTranspose, det_transpose,
    ← GeneralLinearGroup.val_det_apply, map_inv]

theorem det_scalar_GL (c : Kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) = c ^ n := by
  ext
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar]
  simp [Matrix.scalar_apply, det_diagonal]

theorem det_toGL (B : SpecialLinearGroup (Fin n) K) :
    GeneralLinearGroup.det (SpecialLinearGroup.toGL B) = 1 := by
  ext
  rw [GeneralLinearGroup.val_det_apply, SpecialLinearGroup.coe_GL_coe_matrix, Units.val_one]
  exact B.2

theorem exists_toGL_eq {M : GL (Fin n) K} (hM : GeneralLinearGroup.det M = 1) :
    ∃ B : SpecialLinearGroup (Fin n) K, SpecialLinearGroup.toGL B = M := by
  refine ⟨⟨(M : Matrix (Fin n) (Fin n) K), ?_⟩, Units.ext rfl⟩
  rw [← GeneralLinearGroup.val_det_apply, hM, Units.val_one]

end Matrices

section Conj

variable {K : Type} [Field K] {n : ℕ}

theorem exists_half_of_even {f : ℕ} (hf : 1 ≤ f) (hfe : Even f) :
    ∃ u : ℕ, 1 ≤ u ∧ 2 ^ (f / 2) = 2 * u ∧ 2 ^ f = 4 * u ^ 2 := by
  obtain ⟨e, rfl⟩ := hfe
  refine ⟨2 ^ (e - 1), Nat.one_le_two_pow, ?_, ?_⟩
  · rw [show (e + e) / 2 = e by omega, ← pow_succ']
    congr 1
    omega
  · have h : 2 * 2 ^ (e - 1) = 2 ^ e := by
      rw [← pow_succ']
      congr 1
      omega
    calc 2 ^ (e + e) = (2 * 2 ^ (e - 1)) ^ 2 := by rw [h, ← pow_mul, mul_two]
      _ = 4 * (2 ^ (e - 1)) ^ 2 := by ring

theorem pow_card_units [Finite K] {u : ℕ} (hK : Nat.card K = 4 * u ^ 2) (a : Kˣ) :
    a ^ (4 * u ^ 2) = a := by
  have := Fintype.ofFinite K
  ext
  rw [Units.val_pow_eq_pow_val, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem exists_sl_conj_eq_field [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 3 ≤ n) (σ : K ≃+* K) (hσ : σ ≠ 1) (B : SpecialLinearGroup (Fin n) K)
    (h2 : (conjAut n K (SpecialLinearGroup.toGL B) * fieldAut n K σ) ^ 2 = 1) :
    ∃ B' : SpecialLinearGroup (Fin n) K,
      conjAut n K (SpecialLinearGroup.toGL B') * fieldAut n K σ *
          (conjAut n K (SpecialLinearGroup.toGL B'))⁻¹ =
        conjAut n K (SpecialLinearGroup.toGL B) * fieldAut n K σ := by
  obtain ⟨hfe, hσx, H, hH⟩ := even_linear_field_involution_descent hf hK hn _ σ hσ h2
  obtain ⟨u, hu1, hq₀, hq⟩ := exists_half_of_even hf hfe
  have key : ∀ M : GL (Fin n) K,
      (conjAut n K (GeneralLinearGroup.map (σ : K →+* K) M))⁻¹ * fieldAut n K σ =
        fieldAut n K σ * (conjAut n K M)⁻¹ := fun M => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← fieldAut_mul_conjAut, mul_inv_cancel_right]
  have hHH : conjAut n K (H * (GeneralLinearGroup.map (σ : K →+* K) H)⁻¹) * fieldAut n K σ =
      conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹ := by
    rw [map_mul, map_inv, mul_assoc, key, ← mul_assoc]
  have hBc : conjAut n K (SpecialLinearGroup.toGL B) =
      conjAut n K (H * (GeneralLinearGroup.map (σ : K →+* K) H)⁻¹) :=
    mul_right_cancel (hH.trans hHH.symm)
  obtain ⟨c, hc⟩ :=
    (CFSG.ComponentClassification.UnbalancedCatalog.conjAut_eq_conjAut_iff hn _ _).1 hBc
  set a := GeneralLinearGroup.det H with ha
  have hσa : GeneralLinearGroup.det (GeneralLinearGroup.map (σ : K →+* K) H) = a ^ (2 * u) := by
    ext
    rw [val_det_map, hσx, hq₀, Units.val_pow_eq_pow_val]
  have hrel := congrArg GeneralLinearGroup.det hc
  rw [det_toGL, map_mul, map_mul, map_inv, hσa, det_scalar_GL] at hrel
  have hac : a ^ (2 * u) = a * c ^ n := by
    rw [eq_comm, mul_right_comm, mul_inv_eq_one] at hrel
    exact hrel.symm
  obtain ⟨a₁, l, ha₁, hal⟩ :=
    exists_fixed_mul_pow_field hu1 (pow_card_units (hK.trans hq) a) hac
  set D : GL (Fin n) K := langDiag ⟨0, by omega⟩ a₁⁻¹ with hD
  have hσD : GeneralLinearGroup.map (σ : K →+* K) D = D := by
    refine map_langDiag σ _ ?_
    rw [hσx, hq₀, ← Units.val_pow_eq_pow_val, inv_pow, ha₁]
  have hDf : conjAut n K D * fieldAut n K σ * (conjAut n K D)⁻¹ = fieldAut n K σ := by
    rw [mul_inv_eq_iff_eq_mul, fieldAut_mul_conjAut, hσD]
  have hMdet : GeneralLinearGroup.det (H * D * GeneralLinearGroup.scalar (Fin n) l⁻¹) = 1 := by
    rw [map_mul, map_mul, hD, det_langDiag, det_scalar_GL, ← ha, hal, inv_pow,
      mul_right_comm a₁, mul_inv_cancel, one_mul, mul_inv_cancel]
  obtain ⟨B', hB'⟩ := exists_toGL_eq hMdet
  refine ⟨B', ?_⟩
  rw [hB', map_mul, map_mul, conjAut_scalar, mul_one, hH]
  calc conjAut n K H * conjAut n K D * fieldAut n K σ * (conjAut n K H * conjAut n K D)⁻¹ =
      conjAut n K H * (conjAut n K D * fieldAut n K σ * (conjAut n K D)⁻¹) *
        (conjAut n K H)⁻¹ := by group
    _ = conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹ := by rw [hDf]

theorem exists_sl_conj_eq_graphField [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 3 ≤ n) (σ : K ≃+* K) (hσ : σ ≠ 1) (B : SpecialLinearGroup (Fin n) K)
    (h2 : (conjAut n K (SpecialLinearGroup.toGL B) * fieldAut n K σ * dualAut n K) ^ 2 = 1) :
    ∃ B' : SpecialLinearGroup (Fin n) K,
      conjAut n K (SpecialLinearGroup.toGL B') * (fieldAut n K σ * dualAut n K) *
          (conjAut n K (SpecialLinearGroup.toGL B'))⁻¹ =
        conjAut n K (SpecialLinearGroup.toGL B) * (fieldAut n K σ * dualAut n K) := by
  obtain ⟨hfe, hσx, H, hH⟩ :=
    UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two hf hK hn _ σ hσ h2
  rw [mul_assoc] at hH
  obtain ⟨u, hu1, hq₀, hq⟩ := exists_half_of_even hf hfe
  set α₀ := fieldAut n K σ * dualAut n K with hα₀
  have hcomm : ∀ M : GL (Fin n) K, α₀ * conjAut n K M =
      conjAut n K (GeneralLinearGroup.map (σ : K →+* K)
        (GeneralLinearGroup.inverseTranspose M)) * α₀ := fun M => by
    rw [hα₀, mul_assoc, dualAut_mul_conjAut, ← mul_assoc, fieldAut_mul_conjAut, mul_assoc]
  have key : ∀ M : GL (Fin n) K,
      (conjAut n K (GeneralLinearGroup.map (σ : K →+* K)
        (GeneralLinearGroup.inverseTranspose M)))⁻¹ * α₀ = α₀ * (conjAut n K M)⁻¹ := fun M => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hcomm, mul_inv_cancel_right]
  have hHH : conjAut n K (H * (GeneralLinearGroup.map (σ : K →+* K)
        (GeneralLinearGroup.inverseTranspose H))⁻¹) * α₀ =
      conjAut n K H * α₀ * (conjAut n K H)⁻¹ := by
    rw [map_mul, map_inv, mul_assoc, key, ← mul_assoc]
  have hBc : conjAut n K (SpecialLinearGroup.toGL B) =
      conjAut n K (H * (GeneralLinearGroup.map (σ : K →+* K)
        (GeneralLinearGroup.inverseTranspose H))⁻¹) :=
    mul_right_cancel (hH.trans hHH.symm)
  obtain ⟨c, hc⟩ :=
    (CFSG.ComponentClassification.UnbalancedCatalog.conjAut_eq_conjAut_iff hn _ _).1 hBc
  set a := GeneralLinearGroup.det H with ha
  have hτa : GeneralLinearGroup.det (GeneralLinearGroup.map (σ : K →+* K)
      (GeneralLinearGroup.inverseTranspose H)) = (a ^ (2 * u))⁻¹ := by
    ext
    rw [val_det_map, det_inverseTranspose, Units.val_inv_eq_inv_val, map_inv₀, hσx, hq₀,
      Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  have hrel := congrArg GeneralLinearGroup.det hc
  rw [det_toGL, map_mul, map_mul, map_inv, hτa, inv_inv, det_scalar_GL, ← pow_succ'] at hrel
  obtain ⟨a₁, l, ha₁, hal⟩ :=
    exists_fixed_mul_pow_graphField hu1 (pow_card_units (hK.trans hq) a) hrel.symm
  set D : GL (Fin n) K := langDiag ⟨0, by omega⟩ a₁⁻¹ with hD
  have hτD : GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.inverseTranspose D) = D := by
    rw [hD, inverseTranspose_langDiag, inv_inv]
    refine map_langDiag σ _ ?_
    rw [hσx, hq₀, ← Units.val_pow_eq_pow_val]
    congr 1
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, ha₁])
  have hDf : conjAut n K D * α₀ * (conjAut n K D)⁻¹ = α₀ := by
    rw [mul_inv_eq_iff_eq_mul, hcomm, hτD]
  have hMdet : GeneralLinearGroup.det (H * D * GeneralLinearGroup.scalar (Fin n) l⁻¹) = 1 := by
    rw [map_mul, map_mul, hD, det_langDiag, det_scalar_GL, ← ha, hal, inv_pow,
      mul_right_comm a₁, mul_inv_cancel, one_mul, mul_inv_cancel]
  obtain ⟨B', hB'⟩ := exists_toGL_eq hMdet
  refine ⟨B', ?_⟩
  rw [hB', map_mul, map_mul, conjAut_scalar, mul_one, hH]
  calc conjAut n K H * conjAut n K D * α₀ * (conjAut n K H * conjAut n K D)⁻¹ =
      conjAut n K H * (conjAut n K D * α₀ * (conjAut n K D)⁻¹) * (conjAut n K H)⁻¹ := by group
    _ = conjAut n K H * α₀ * (conjAut n K H)⁻¹ := by rw [hDf]

end Conj

section Lang

variable {K : Type} [Field K] {n : ℕ}

theorem isLangSurjective_fieldAut [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 3 ≤ n) (σ : K ≃+* K) (hσ : σ ≠ 1) (hσ2 : fieldAut n K σ ^ 2 = 1) :
    IsLangSurjective (fieldAut n K σ) := by
  intro z hz
  obtain ⟨B, rfl⟩ := proj_surjective n K z
  have h2 : (conjAut n K (SpecialLinearGroup.toGL B) * fieldAut n K σ) ^ 2 = 1 := by
    rw [conjAut_toGL]
    exact sq_conj_mul_eq_one hσ2 hz
  obtain ⟨B', hB'⟩ := exists_sl_conj_eq_field hf hK hn σ hσ B h2
  rw [conjAut_toGL, conjAut_toGL] at hB'
  exact exists_inv_apply_mul_eq_of_conj_eq (LinearOuter.conj_injective hn) hσ2 hB'

theorem isLangSurjective_fieldAut_mul_dualAut [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hσ2 : (fieldAut n K σ * dualAut n K) ^ 2 = 1) :
    IsLangSurjective (fieldAut n K σ * dualAut n K) := by
  intro z hz
  obtain ⟨B, rfl⟩ := proj_surjective n K z
  have h2 : (conjAut n K (SpecialLinearGroup.toGL B) * fieldAut n K σ * dualAut n K) ^ 2 = 1 := by
    rw [mul_assoc, conjAut_toGL]
    exact sq_conj_mul_eq_one hσ2 hz
  obtain ⟨B', hB'⟩ := exists_sl_conj_eq_graphField hf hK hn σ hσ B h2
  rw [conjAut_toGL, conjAut_toGL] at hB'
  exact exists_inv_apply_mul_eq_of_conj_eq (LinearOuter.conj_injective hn) hσ2 hB'

theorem isLangSurjective_of_sigma_ne_one [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) (A : GL (Fin n) K) (σ : K ≃+* K) (ε : ℕ)
    (hσ : σ ≠ 1) (hε : ε ≤ 1) (h2 : (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε) ^ 2 = 1) :
    IsLangSurjective (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε) := by
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · rw [pow_zero, mul_one] at h2 ⊢
    obtain ⟨-, -, H, hH⟩ := even_linear_field_involution_descent hf hK hn A σ hσ h2
    have hσ2 : fieldAut n K σ ^ 2 = 1 := by
      have h : MulAut.conj (conjAut n K H) (fieldAut n K σ ^ 2) = 1 := by
        rw [map_pow, MulAut.conj_apply, ← hH, h2]
      exact (MulEquiv.map_eq_one_iff _).1 h
    refine IsLangSurjective.of_conj (ψ := (conjAut n K H)⁻¹) ?_
      (isLangSurjective_fieldAut hf hK hn σ hσ hσ2)
    rw [hH]
    group
  · rw [pow_one] at h2 ⊢
    obtain ⟨-, -, H, hH⟩ :=
      UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two hf hK hn A σ hσ h2
    have hσ2 : (fieldAut n K σ * dualAut n K) ^ 2 = 1 := by
      have h : MulAut.conj (conjAut n K H) ((fieldAut n K σ * dualAut n K) ^ 2) = 1 := by
        rw [map_pow, MulAut.conj_apply, ← hH, h2]
      exact (MulEquiv.map_eq_one_iff _).1 h
    refine IsLangSurjective.of_conj (ψ := (conjAut n K H)⁻¹) ?_
      (isLangSurjective_fieldAut_mul_dualAut hf hK hn σ hσ hσ2)
    rw [hH]
    group

theorem eq_one_of_sq_eq_one_charTwoField [CharP K 2] {x : K} (h : x ^ 2 = 1) : x = 1 := by
  have h1 : (x + 1) ^ 2 = 0 := by
    rw [add_sq, h, mul_one, one_pow, show (2 : K) = 0 from CharTwo.two_eq_zero, zero_mul,
      add_zero, CharTwo.add_self_eq_zero]
  have h2 : x + 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h1
  rwa [CharTwo.add_eq_zero] at h2

theorem isLangSurjective_dualAut_of_odd [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) (hodd : Odd n) : IsLangSurjective (dualAut n K) := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  intro z hz
  obtain ⟨Z, rfl⟩ := proj_surjective n K z
  have hδ2 : dualAut n K ^ 2 = 1 := by
    rw [sq]
    exact (standard_automorphism_transport (n := n) (K := K)).2.2.2.1
  have h2 : (conjAut n K (SpecialLinearGroup.toGL Z) * dualAut n K) ^ 2 = 1 := by
    rw [conjAut_toGL]
    exact sq_conj_mul_eq_one hδ2 hz
  obtain ⟨-, ⟨H, C, hA, -, hC⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms hf hK hn _ h2
  rcases hC with ⟨hC1, -⟩ | ⟨r, hr, -⟩
  · rw [hC1, Matrix.mul_one, SpecialLinearGroup.coe_GL_coe_matrix] at hA
    have hdet : (H : Matrix (Fin n) (Fin n) K).det = 1 := by
      refine eq_one_of_sq_eq_one_charTwoField ?_
      have h := congrArg Matrix.det hA
      rw [Z.2, det_mul, det_transpose] at h
      rw [sq, ← h]
    set W : SpecialLinearGroup (Fin n) K := ⟨(H : Matrix (Fin n) (Fin n) K)ᵀ, by
      rw [det_transpose, hdet]⟩ with hW
    refine ⟨proj n K W, ?_⟩
    rw [dualAut_proj, ← map_inv, ← map_mul]
    congr 1
    have h1m : ((W.transpose * W⁻¹.transpose : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = ((1 : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose,
        Matrix.SpecialLinearGroup.coe_transpose, ← Matrix.transpose_mul,
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
        Matrix.transpose_one]
    have h1 : W.transpose * W⁻¹.transpose = 1 :=
      Matrix.SpecialLinearGroup.ext _ _ fun i j => congrFun (congrFun h1m i) j
    rw [inv_eq_of_mul_eq_one_left h1]
    have h3m : ((W.transpose * W : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (Z : Matrix (Fin n) (Fin n) K) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose, hW]
      change ((H : Matrix (Fin n) (Fin n) K)ᵀ)ᵀ * (H : Matrix (Fin n) (Fin n) K)ᵀ = _
      rw [Matrix.transpose_transpose, ← hA]
    exact Matrix.SpecialLinearGroup.ext _ _ fun i j => congrFun (congrFun h3m i) j
  · exact absurd hodd (by rw [hr]; exact Nat.not_odd_iff_even.2 (even_two_mul r))

theorem isLangSurjective_conjAut_mul_dualAut_of_odd [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) (hodd : Odd n) (A : GL (Fin n) K)
    (h2 : (conjAut n K A * dualAut n K) ^ 2 = 1) :
    IsLangSurjective (conjAut n K A * dualAut n K) := by
  obtain ⟨-, ⟨H, C, -, hHC, hC⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms hf hK hn A h2
  rcases hC with ⟨hC1, -⟩ | ⟨r, hr, -⟩
  · have hC1' : C = 1 := Units.ext hC1
    rw [hC1', map_one, one_mul] at hHC
    refine IsLangSurjective.of_conj (ψ := (conjAut n K H)⁻¹) ?_
      (isLangSurjective_dualAut_of_odd hf hK hn hodd)
    rw [hHC]
    group
  · exact absurd hodd (by rw [hr]; exact Nat.not_odd_iff_even.2 (even_two_mul r))

theorem isLangSurjective_of_not_inner_of_not_even_graph [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) (A : GL (Fin n) K) (σ : K ≃+* K) (ε : ℕ)
    (hε : ε ≤ 1) (h2 : (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε) ^ 2 = 1)
    (hinn : ¬(σ = 1 ∧ ε = 0)) (hgr : ¬(σ = 1 ∧ ε = 1 ∧ Even n)) :
    IsLangSurjective (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε) := by
  by_cases hσ : σ = 1
  · subst hσ
    have hε0 : ε ≠ 0 := fun h => hinn ⟨rfl, h⟩
    have hε1 : ε = 1 := by omega
    subst hε1
    have hodd : Odd n := Nat.not_even_iff_odd.1 fun h => hgr ⟨rfl, rfl, h⟩
    rw [map_one, mul_one, pow_one] at h2 ⊢
    exact isLangSurjective_conjAut_mul_dualAut_of_odd hf hK hn hodd A h2
  · exact isLangSurjective_of_sigma_ne_one hf hK hn A σ ε hσ hε h2

end Lang

end CFSG.SeitzReduction.LinearPilot
