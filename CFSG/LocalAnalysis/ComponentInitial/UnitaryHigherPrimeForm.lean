module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem ringHom_apply_of_mem_bot (σ : K →+* K) {x : K} (hx : x ∈ (⊥ : Subfield K)) :
    σ x = x := by
  rw [← Subfield.closure_empty] at hx
  induction hx using Subfield.closure_induction with
  | mem x hx => exact absurd hx (Set.notMem_empty x)
  | one => exact map_one σ
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | neg x _ hx => rw [map_neg, hx]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

structure IsPrimeFormGram (C : GL (Fin n) K) : Prop where
  symm : (C : Matrix (Fin n) (Fin n) K)ᵀ = C
  prime : ∀ i j, (C : Matrix (Fin n) (Fin n) K) i j ∈ (⊥ : Subfield K)

theorem IsPrimeFormGram.map_eq {C : GL (Fin n) K} (hC : IsPrimeFormGram C) (σ : K →+* K) :
    (C : Matrix (Fin n) (Fin n) K).map σ = C :=
  Matrix.ext fun i j => ringHom_apply_of_mem_bot σ (hC.prime i j)

theorem IsPrimeFormGram.map_eq_ringEquiv {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (φ : K ≃+* K) : (C : Matrix (Fin n) (Fin n) K).map φ = C :=
  Matrix.ext fun i j => ringHom_apply_of_mem_bot (φ : K →+* K) (hC.prime i j)

section Groups

variable (h : UnitaryFieldData p f K)

@[expose] def primeFormUnitary (C : Matrix (Fin n) (Fin n) K) : Subgroup (GL (Fin n) K) where
  carrier := {g | ((g : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * C *
    (g : Matrix (Fin n) (Fin n) K) = C}
  mul_mem' {g g'} hg hg' := by
    change (((g * g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * C *
      ((g * g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = C
    rw [Units.val_mul, conjTranspose_mul_mul, hg, hg']
  one_mem' := by
    change (((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * C *
      ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = C
    rw [Units.val_one, Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one,
      Matrix.one_mul, Matrix.mul_one]
  inv_mem' {g} hg := by
    have hgg : (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h1 := conjTranspose_mul_mul h C (g : Matrix (Fin n) (Fin n) K)
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [hg, hgg] at h1
    simp only [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one,
      Matrix.one_mul, Matrix.mul_one] at h1
    exact h1.symm

variable {h} in
theorem mem_primeFormUnitary {C : Matrix (Fin n) (Fin n) K} {g : GL (Fin n) K} :
    g ∈ primeFormUnitary h C ↔
      ((g : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * C * (g : Matrix (Fin n) (Fin n) K) = C :=
  Iff.rfl

theorem mem_gramSU_iff_unitary {C : Matrix (Fin n) (Fin n) K} {g : GL (Fin n) K} :
    g ∈ gramSU h C ↔ g ∈ primeFormUnitary h C ∧ (g : Matrix (Fin n) (Fin n) K).det = 1 :=
  Iff.rfl

abbrev primeFormP (C : Matrix (Fin n) (Fin n) K) : Type :=
  gramSU h C ⧸ normOneScalars h (gramSU h C) n

end Groups

section Conj

variable (h : UnitaryFieldData p f K) (C : Matrix (Fin n) (Fin n) K)

theorem conj_mem_gramSU {A g : GL (Fin n) K} (hA : A ∈ primeFormUnitary h C)
    (hg : g ∈ gramSU h C) : A * g * A⁻¹ ∈ gramSU h C := by
  refine ⟨mul_mem (mul_mem hA hg.1) (inv_mem hA), ?_⟩
  rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hg.2, mul_one, ← det_mul, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, det_one]

@[expose] noncomputable def primeFormConjSU (A : primeFormUnitary h C) :
    gramSU h C ≃* gramSU h C where
  toFun g := ⟨A * g * A⁻¹, conj_mem_gramSU h C A.2 g.2⟩
  invFun g := ⟨A⁻¹ * g * A⁻¹⁻¹, conj_mem_gramSU h C (inv_mem A.2) g.2⟩
  left_inv g := Subtype.ext (by
    change ((A : GL (Fin n) K))⁻¹ * ((A : GL (Fin n) K) * g * (A : GL (Fin n) K)⁻¹) *
      (A : GL (Fin n) K)⁻¹⁻¹ = g
    group)
  right_inv g := Subtype.ext (by
    change (A : GL (Fin n) K) * ((A : GL (Fin n) K)⁻¹ * g * (A : GL (Fin n) K)⁻¹⁻¹) *
      (A : GL (Fin n) K)⁻¹ = g
    group)
  map_mul' g g' := Subtype.ext (by
    change (A : GL (Fin n) K) * ((g : GL (Fin n) K) * g') * (A : GL (Fin n) K)⁻¹ =
      ((A : GL (Fin n) K) * g * (A : GL (Fin n) K)⁻¹) *
        ((A : GL (Fin n) K) * g' * (A : GL (Fin n) K)⁻¹)
    group)

theorem map_normOneScalars_conj (A : primeFormUnitary h C) :
    (normOneScalars h (gramSU h C) n).map (primeFormConjSU h C A).toMonoidHom =
      normOneScalars h (gramSU h C) n := by
  have hfix : ∀ z ∈ normOneScalars h (gramSU h C) n, primeFormConjSU h C A z = z := by
    rintro z ⟨c, -, -, hz⟩
    apply Subtype.ext
    change (A : GL (Fin n) K) * z * (A : GL (Fin n) K)⁻¹ = z
    rw [hz, (commute_scalar c (A : GL (Fin n) K)).eq, mul_inv_cancel_right]
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    change primeFormConjSU h C A y ∈ _
    rw [hfix y hy]
    exact hy
  · intro hz
    exact ⟨z, hz, hfix z hz⟩

@[expose] noncomputable def primeFormConjAut (A : primeFormUnitary h C) :
    MulAut (primeFormP h C) :=
  QuotientGroup.congr _ _ (primeFormConjSU h C A) (map_normOneScalars_conj h C A)

theorem primeFormConjAut_mk (A : primeFormUnitary h C) (g : gramSU h C) :
    primeFormConjAut h C A (g : primeFormP h C) = ((primeFormConjSU h C A g : gramSU h C) :
      primeFormP h C) :=
  QuotientGroup.congr_mk _ _ _ _ g

@[expose] noncomputable def primeFormConjHom : primeFormUnitary h C →* MulAut (primeFormP h C) where
  toFun := primeFormConjAut h C
  map_one' := MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => by
    rw [primeFormConjAut_mk]
    congr 1
    apply Subtype.ext
    change ((1 : primeFormUnitary h C) : GL (Fin n) K) * g *
      ((1 : primeFormUnitary h C) : GL (Fin n) K)⁻¹ = g
    rw [Subgroup.coe_one, one_mul, inv_one, mul_one]
  map_mul' A B := MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => by
    change primeFormConjAut h C (A * B) (g : primeFormP h C) =
      primeFormConjAut h C A (primeFormConjAut h C B (g : primeFormP h C))
    rw [primeFormConjAut_mk, primeFormConjAut_mk, primeFormConjAut_mk]
    congr 1
    apply Subtype.ext
    change ((A * B : primeFormUnitary h C) : GL (Fin n) K) * g *
      ((A * B : primeFormUnitary h C) : GL (Fin n) K)⁻¹ = (A : GL (Fin n) K) *
        ((B : GL (Fin n) K) * g * (B : GL (Fin n) K)⁻¹) * (A : GL (Fin n) K)⁻¹
    rw [Subgroup.coe_mul]
    group

theorem primeFormConjHom_mk (A : primeFormUnitary h C) (g : gramSU h C) :
    primeFormConjHom h C A (g : primeFormP h C) =
      ((⟨A * g * (A : GL (Fin n) K)⁻¹, conj_mem_gramSU h C A.2 g.2⟩ : gramSU h C) :
        primeFormP h C) :=
  primeFormConjAut_mk h C A g

end Conj

section Field

variable (h : UnitaryFieldData p f K) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)

include hC

theorem map_gram_eq (φ : K ≃+* K) (g : Matrix (Fin n) (Fin n) K) :
    ((g.map φ).map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) * g.map φ =
      ((g.map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) * g).map φ := by
  rw [Matrix.map_mul, Matrix.map_mul, transpose_map, hC.map_eq_ringEquiv φ]
  congr 3
  ext i j
  simp [map_bar_comm]

theorem glAut_mem_primeFormUnitary (φ : K ≃+* K) {g : GL (Fin n) K}
    (hg : g ∈ primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) :
    glAut φ g ∈ primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) := by
  change (((glAut φ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
    (C : Matrix (Fin n) (Fin n) K) * ((glAut φ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (C : Matrix (Fin n) (Fin n) K)
  rw [coe_glAut, map_gram_eq h hC, hg, hC.map_eq_ringEquiv φ]

theorem glAut_mem_gramSU (φ : K ≃+* K) {g : GL (Fin n) K}
    (hg : g ∈ gramSU h (C : Matrix (Fin n) (Fin n) K)) :
    glAut φ g ∈ gramSU h (C : Matrix (Fin n) (Fin n) K) := by
  refine ⟨glAut_mem_primeFormUnitary h hC φ hg.1, ?_⟩
  rw [coe_glAut, show (g : Matrix (Fin n) (Fin n) K).map φ =
    (φ : K →+* K).mapMatrix (g : Matrix (Fin n) (Fin n) K) from rfl, ← RingHom.map_det, hg.2,
    map_one]

@[expose] noncomputable def primeFormFieldSU (φ : K ≃+* K) :
    gramSU h (C : Matrix (Fin n) (Fin n) K) ≃* gramSU h (C : Matrix (Fin n) (Fin n) K) where
  toFun g := ⟨glAut φ g, glAut_mem_gramSU h hC φ g.2⟩
  invFun g := ⟨glAut φ⁻¹ g, glAut_mem_gramSU h hC φ⁻¹ g.2⟩
  left_inv g := Subtype.ext (by
    change glAut φ⁻¹ (glAut φ (g : GL (Fin n) K)) = g
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
  right_inv g := Subtype.ext (by
    change glAut φ (glAut φ⁻¹ (g : GL (Fin n) K)) = g
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply])
  map_mul' g g' := Subtype.ext (map_mul (glAut φ) (g : GL (Fin n) K) g')

theorem map_normOneScalars_field (φ : K ≃+* K) :
    (normOneScalars h (gramSU h (C : Matrix (Fin n) (Fin n) K)) n).map
      (primeFormFieldSU h hC φ).toMonoidHom =
      normOneScalars h (gramSU h (C : Matrix (Fin n) (Fin n) K)) n := by
  have himage : ∀ (ψ : K ≃+* K) z, z ∈ normOneScalars h (gramSU h (C : Matrix (Fin n)
      (Fin n) K)) n → primeFormFieldSU h hC ψ z ∈ normOneScalars h (gramSU h (C : Matrix
        (Fin n) (Fin n) K)) n := by
    rintro ψ z ⟨c, hcN, hcn, hz⟩
    refine ⟨Units.map (ψ : K →* K) c, ?_, ?_, ?_⟩
    · rw [Units.coe_map]
      change h.norm (ψ (c : K)) = 1
      rw [UnitaryFieldData.norm, ← map_bar_comm, ← map_mul]
      change ψ (h.norm (c : K)) = 1
      rw [hcN, map_one]
    · rw [← map_pow, hcn, map_one]
    · change glAut ψ (z : GL (Fin n) K) = _
      rw [hz]
      apply Units.ext
      rw [coe_glAut, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar, scalar_apply,
        scalar_apply, diagonal_map (map_zero ψ), Units.coe_map]
      rfl
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact himage φ y hy
  · intro hz
    refine ⟨primeFormFieldSU h hC φ⁻¹ z, himage φ⁻¹ z hz, ?_⟩
    exact (primeFormFieldSU h hC φ).apply_symm_apply z

@[expose] noncomputable def primeFormFieldAut (φ : K ≃+* K) :
    MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)) :=
  QuotientGroup.congr _ _ (primeFormFieldSU h hC φ) (map_normOneScalars_field h hC φ)

theorem primeFormFieldAut_mk (φ : K ≃+* K) (g : gramSU h (C : Matrix (Fin n) (Fin n) K)) :
    primeFormFieldAut h hC φ (g : primeFormP h (C : Matrix (Fin n) (Fin n) K)) =
      ((primeFormFieldSU h hC φ g : gramSU h (C : Matrix (Fin n) (Fin n) K)) :
        primeFormP h (C : Matrix (Fin n) (Fin n) K)) :=
  QuotientGroup.congr_mk _ _ _ _ g

@[expose] noncomputable def primeFormFieldHom :
    (K ≃+* K) →* MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)) where
  toFun := primeFormFieldAut h hC
  map_one' := MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => by
    rw [primeFormFieldAut_mk]
    congr 1
  map_mul' φ ψ := MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => by
    change primeFormFieldAut h hC (φ * ψ) (g : primeFormP h _) =
      primeFormFieldAut h hC φ (primeFormFieldAut h hC ψ (g : primeFormP h _))
    rw [primeFormFieldAut_mk, primeFormFieldAut_mk, primeFormFieldAut_mk]
    congr 1

end Field

section Psi

variable (h : UnitaryFieldData p f K) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)

include hC

@[expose] noncomputable def primeFormFieldU :
    (K ≃+* K) →* MulAut (primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) where
  toFun φ :=
    { toFun := fun g => ⟨glAut φ g, glAut_mem_primeFormUnitary h hC φ g.2⟩
      invFun := fun g => ⟨glAut φ⁻¹ g, glAut_mem_primeFormUnitary h hC φ⁻¹ g.2⟩
      left_inv := fun g => Subtype.ext (by
        change glAut φ⁻¹ (glAut φ (g : GL (Fin n) K)) = g
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
      right_inv := fun g => Subtype.ext (by
        change glAut φ (glAut φ⁻¹ (g : GL (Fin n) K)) = g
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply])
      map_mul' := fun g g' => Subtype.ext (map_mul (glAut φ) (g : GL (Fin n) K) g') }
  map_one' := MulEquiv.ext fun g => Subtype.ext (by
    change glAut 1 (g : GL (Fin n) K) = g
    rw [map_one]
    rfl)
  map_mul' φ ψ := MulEquiv.ext fun g => Subtype.ext (by
    change glAut (φ * ψ) (g : GL (Fin n) K) = glAut φ (glAut ψ (g : GL (Fin n) K))
    rw [map_mul]
    rfl)

theorem coe_primeFormFieldU (φ : K ≃+* K)
    (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) :
    ((primeFormFieldU h hC φ A : primeFormUnitary h _) : GL (Fin n) K) = glAut φ A :=
  rfl

theorem primeFormField_conj_eq (φ : K ≃+* K)
    (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) :
    primeFormFieldHom h hC φ * primeFormConjHom h _ A * (primeFormFieldHom h hC φ)⁻¹ =
      primeFormConjHom h _ (primeFormFieldU h hC φ A) := by
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  rw [← map_inv, MulAut.mul_apply, MulAut.mul_apply]
  change primeFormFieldAut h hC φ (primeFormConjAut h _ A
    (primeFormFieldAut h hC φ⁻¹ (g : primeFormP h _))) =
      primeFormConjAut h _ (primeFormFieldU h hC φ A) (g : primeFormP h _)
  rw [primeFormFieldAut_mk, primeFormConjAut_mk, primeFormFieldAut_mk, primeFormConjAut_mk]
  congr 1
  apply Subtype.ext
  change glAut φ ((A : GL (Fin n) K) * glAut φ⁻¹ (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹) =
    glAut φ (A : GL (Fin n) K) * g * (glAut φ (A : GL (Fin n) K))⁻¹
  simp only [map_mul, map_inv, MulAut.inv_apply, MulEquiv.apply_symm_apply]

@[expose] noncomputable def primeFormPsi :
    primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) ⋊[primeFormFieldU h hC] (K ≃+* K) →*
      MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)) :=
  SemidirectProduct.lift (primeFormConjHom h _) (primeFormFieldHom h hC) fun φ =>
    MonoidHom.ext fun A => by
      change primeFormConjHom h _ (primeFormFieldU h hC φ A) =
        primeFormFieldHom h hC φ * primeFormConjHom h _ A * (primeFormFieldHom h hC φ)⁻¹
      rw [primeFormField_conj_eq]

theorem primeFormPsi_apply (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K))
    (φ : K ≃+* K) :
    primeFormPsi h hC ⟨A, φ⟩ = primeFormConjHom h _ A * primeFormFieldHom h hC φ := by
  rw [SemidirectProduct.mk_eq_inl_mul_inr, map_mul, primeFormPsi, SemidirectProduct.lift_inl,
    SemidirectProduct.lift_inr]

end Psi

section Node

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def primeFormD (C : Matrix (Fin n) (Fin n) K) :
    Subgroup (MulAut (primeFormP h C)) :=
  (primeFormConjHom h C).range

@[expose] noncomputable def primeFormE {C : GL (Fin n) K} (hC : IsPrimeFormGram C) :
    Subgroup (MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) :=
  primeFormD h _ ⊔ (primeFormFieldHom h hC).range

theorem range_primeFormPsi {C : GL (Fin n) K} (hC : IsPrimeFormGram C) :
    (primeFormPsi h hC).range = primeFormE h hC := by
  apply le_antisymm
  · rintro _ ⟨⟨A, φ⟩, rfl⟩
    rw [primeFormPsi_apply]
    exact mul_mem (Subgroup.mem_sup_left ⟨A, rfl⟩) (Subgroup.mem_sup_right ⟨φ, rfl⟩)
  · refine sup_le ?_ ?_
    · rintro _ ⟨A, rfl⟩
      exact ⟨SemidirectProduct.inl A, SemidirectProduct.lift_inl _ _ _ A⟩
    · rintro _ ⟨φ, rfl⟩
      exact ⟨SemidirectProduct.inr φ, SemidirectProduct.lift_inr _ _ _ φ⟩

theorem unitary_prime_form_automorphism_data {C : GL (Fin n) K} (hC : IsPrimeFormGram C) :
    (gramForm h (C : Matrix (Fin n) (Fin n) K)).IsSymm ∧
    (gramForm h (C : Matrix (Fin n) (Fin n) K)).SeparatingLeft ∧
    (∀ g : GL (Fin n) K, g ∈ primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) ↔
      ((g : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * C * (g : Matrix (Fin n) (Fin n) K) = C) ∧
    (∀ g : GL (Fin n) K, g ∈ gramSU h (C : Matrix (Fin n) (Fin n) K) ↔
      g ∈ primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) ∧
        (g : Matrix (Fin n) (Fin n) K).det = 1) ∧
    (∀ z : gramSU h (C : Matrix (Fin n) (Fin n) K),
      z ∈ normOneScalars h (gramSU h (C : Matrix (Fin n) (Fin n) K)) n ↔
        ∃ c : Kˣ, h.norm (c : K) = 1 ∧ c ^ n = 1 ∧
          (z : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) c) ∧
    normOneScalars h (gramSU h (C : Matrix (Fin n) (Fin n) K)) n ≤
      Subgroup.center (gramSU h (C : Matrix (Fin n) (Fin n) K)) ∧
    Function.Surjective
      (QuotientGroup.mk' (normOneScalars h (gramSU h (C : Matrix (Fin n) (Fin n) K)) n)) ∧
    (∀ (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K))
      (g : gramSU h (C : Matrix (Fin n) (Fin n) K)),
      primeFormConjHom h _ A (g : primeFormP h _) =
        ((⟨A * g * (A : GL (Fin n) K)⁻¹, conj_mem_gramSU h _ A.2 g.2⟩ :
          gramSU h (C : Matrix (Fin n) (Fin n) K)) : primeFormP h _)) ∧
    (∀ (φ : K ≃+* K) (g : gramSU h (C : Matrix (Fin n) (Fin n) K)),
      primeFormFieldHom h hC φ (g : primeFormP h _) =
        ((⟨glAut φ g, glAut_mem_gramSU h hC φ g.2⟩ :
          gramSU h (C : Matrix (Fin n) (Fin n) K)) : primeFormP h _)) ∧
    (∀ (φ : K ≃+* K) (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)),
      ((primeFormFieldU h hC φ A : primeFormUnitary h _) : GL (Fin n) K) = glAut φ A ∧
      primeFormFieldHom h hC φ * primeFormConjHom h _ A * (primeFormFieldHom h hC φ)⁻¹ =
        primeFormConjHom h _ (primeFormFieldU h hC φ A)) ∧
    primeFormD h (C : Matrix (Fin n) (Fin n) K) = (primeFormConjHom h _).range ∧
    primeFormE h hC = primeFormD h _ ⊔ (primeFormFieldHom h hC).range ∧
    (∀ (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) (φ : K ≃+* K),
      primeFormPsi h hC ⟨A, φ⟩ = primeFormConjHom h _ A * primeFormFieldHom h hC φ) ∧
    (primeFormPsi h hC).range = primeFormE h hC := by
  have hCbar : ((C : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ = C := by
    rw [hC.map_eq h.bar, hC.symm]
  refine ⟨gramForm_isSymm h hCbar,
    gramForm_separatingLeft h ((Matrix.isUnit_iff_isUnit_det _).mp C.isUnit).ne_zero,
    fun g => Iff.rfl, fun g => Iff.rfl, fun z => Iff.rfl,
    normOneScalars_le_center h _ n, QuotientGroup.mk'_surjective _,
    fun A g => primeFormConjHom_mk h _ A g, fun φ g => primeFormFieldAut_mk h hC φ g,
    fun φ A => ⟨rfl, primeFormField_conj_eq h hC φ A⟩, rfl, rfl,
    fun A φ => primeFormPsi_apply h hC A φ, range_primeFormPsi h hC⟩

end Node

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
