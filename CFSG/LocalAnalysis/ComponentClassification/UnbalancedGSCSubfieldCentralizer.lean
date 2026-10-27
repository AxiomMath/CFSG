module

public import CFSG.CharacterTheory.Semidihedral.ProjectiveNonsquareInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.LinearAlgebra.LinearGroups.QuadraticFrobenius
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedGS

namespace SubfieldCentralizer

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GorensteinWalter Matrix

universe u

variable {K : Type u} [Field K]


theorem pgl_map_injective {k : Type u} {F : Type*} [Field k] [Field F]
    (i : k →+* F) : Function.Injective (Matrix.ProjGenLinGroup.map (n := Fin 2) i) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk U =>
    rw [MonoidHom.mem_ker, Matrix.ProjGenLinGroup.map_mk,
      Matrix.ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at hg
    obtain ⟨c, hc⟩ := hg
    apply Matrix.ProjGenLinGroup.mk_eq_one.mpr
    apply Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    refine ⟨U.val 0 0, Matrix.ext fun a b => i.injective ?_⟩
    have h00 : c = i (U.val 0 0) := by
      have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hc
      simpa only [Matrix.scalar_apply, Matrix.diagonal_apply, ite_true,
        Matrix.GeneralLinearGroup.map_apply] using hh
    have hab : (if a = b then c else 0) = i (U.val a b) := by
      have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M a b) hc
      simpa only [Matrix.scalar_apply, Matrix.diagonal_apply,
        Matrix.GeneralLinearGroup.map_apply] using hh
    by_cases h : a = b
    · simpa only [Matrix.scalar_apply, Matrix.diagonal_apply, ite_eq_left h] using
        h00.symm.trans (by simpa only [ite_eq_left h] using hab)
    · simpa only [Matrix.scalar_apply, Matrix.diagonal_apply, ite_eq_right h, map_zero] using
        (by simpa only [ite_eq_right h] using hab : 0 = i (U.val a b))

@[expose] noncomputable def upperGL (t : K) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![1, t; 0, 1] (by simp [det_fin_two])

@[expose] noncomputable def invGL : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![0, -1; 1, 0] (by simp [det_fin_two])

theorem coordinateGLAction_upperGL (t : K) :
    coordinateGLAction K (upperGL t) = translation K t := by
  apply Equiv.ext
  intro x
  cases x with
  | none =>
    rw [coordinateGLAction_infinity_lower_left_zero K _ (by simp [upperGL]), translation_none]
  | some x =>
    rw [coordinateGLAction_finite K _ x (by simp [upperGL]), translation_some]
    simp [upperGL]

theorem coordinateGLAction_invGL : coordinateGLAction K invGL = inversion K := by
  apply Equiv.ext
  intro x
  cases x with
  | none =>
    rw [coordinateGLAction_infinity K _ (by simp [invGL]), inversion_none]
    simp [invGL]
  | some x =>
    by_cases hx : x = 0
    · subst hx
      rw [coordinateGLAction_finite_denominator_zero K _ 0 (by simp [invGL]), inversion_zero]
    · rw [coordinateGLAction_finite K _ x (by simp [invGL, hx]), inversion_nonzero K x hx]
      simp [invGL, neg_div]

theorem fieldExtension_mul_translation (τ : K ≃+* K) (b : K) :
    fieldExtension K τ * translation K b = translation K (τ b) * fieldExtension K τ := by
  apply Equiv.ext
  intro x
  cases x with
  | none => rfl
  | some x =>
    change fieldExtension K τ (translation K b (some x)) =
      translation K (τ b) (fieldExtension K τ (some x))
    simp

theorem fieldExtension_mul_inversion (τ : K ≃+* K) :
    fieldExtension K τ * inversion K = inversion K * fieldExtension K τ := by
  apply Equiv.ext
  intro x
  change fieldExtension K τ (inversion K x) = inversion K (fieldExtension K τ x)
  cases x with
  | none => simp
  | some x =>
    by_cases hx : x = 0
    · subst hx
      simp
    · have hx' : τ x ≠ 0 := by simpa using hx
      rw [inversion_nonzero K x hx, fieldExtension_some, fieldExtension_some,
        inversion_nonzero K _ hx']
      simp

theorem fieldExtension_mul_coordinatePGLAction [Finite K] (τ : K ≃+* K) (g : PGL2 K) :
    fieldExtension K τ * coordinatePGLAction K g =
      coordinatePGLAction K (pgl2FieldAut K τ g) * fieldExtension K τ := by
  have h := congrArg (coordinateSemilinearAction K)
    (SemidirectProduct.inl_aut (φ := pgl2FieldAut K) τ g)
  simp only [map_mul, map_inv, coordinateSemilinearAction_inl,
    coordinateSemilinearAction_inr] at h
  rw [h]
  group

theorem eq_one_of_commute_translation_inversion (d : Equiv.Perm (Omega K))
    (hd : d ∈ coordinateD K) (h1 : d * translation K 1 = translation K 1 * d)
    (h2 : d * inversion K = inversion K * d) : d = 1 := by
  rw [← coordinateGLAction_range_eq_D] at hd
  obtain ⟨A, rfl⟩ := hd
  change coordinateGLAction K A = 1
  have hp1 : ∀ x, coordinateGLAction K A (translation K 1 x) =
      translation K 1 (coordinateGLAction K A x) := fun x => congrArg (fun f => f x) h1
  have hp2 : ∀ x, coordinateGLAction K A (inversion K x) =
      inversion K (coordinateGLAction K A x) := fun x => congrArg (fun f => f x) h2
  have hinf : coordinateGLAction K A none = none := by
    have h := hp1 none
    rw [translation_none] at h
    cases hω : coordinateGLAction K A none with
    | none => rfl
    | some y =>
      rw [hω, translation_some] at h
      have := Option.some_injective _ h
      have h10 : (1 : K) = 0 := by linear_combination -this
      exact absurd h10 one_ne_zero
  have hc : A.val 1 0 = 0 := by
    by_contra hc
    rw [coordinateGLAction_infinity K A hc] at hinf
    exact Option.some_ne_none _ hinf
  have hdet : A.val 0 0 * A.val 1 1 ≠ 0 := by
    have h := (GeneralLinearGroup.det A).ne_zero
    change A.val.det ≠ 0 at h
    rw [det_fin_two, hc, mul_zero, sub_zero] at h
    exact h
  have hd0 : A.val 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  have hfin : ∀ x : K, coordinateGLAction K A (some x) =
      some ((A.val 0 0 * x + A.val 0 1) / A.val 1 1) := by
    intro x
    rw [coordinateGLAction_finite K A x (by rw [hc, zero_mul, zero_add]; exact hd0), hc, zero_mul,
      zero_add]
  have hb : A.val 0 1 = 0 := by
    have h := hp2 none
    rw [inversion_none, hfin, hinf, inversion_none] at h
    have := Option.some_injective _ h
    rw [mul_zero, zero_add, div_eq_zero_iff] at this
    exact this.resolve_right hd0
  have ha : A.val 0 0 = A.val 1 1 := by
    have h := hp1 (some 0)
    rw [translation_some, hfin, hfin, translation_some, hb] at h
    have := Option.some_injective _ h
    field_simp at this
    linear_combination this
  apply Equiv.ext
  intro x
  cases x with
  | none => exact hinf
  | some x =>
    rw [hfin, hb, ha, add_zero, mul_div_cancel_left₀ _ hd0]
    rfl

@[expose] noncomputable def subfieldD [Finite K] (k : Subfield K) :
    coordinateD k →* coordinateD K :=
  (pglEquivCoordinateD K).toMonoidHom.comp ((Matrix.ProjGenLinGroup.map k.subtype).comp
    (pglEquivCoordinateD k).symm.toMonoidHom)

theorem subfieldD_mk [Finite K] (k : Subfield K) (A : GL (Fin 2) k) :
    (subfieldD k (pglEquivCoordinateD k (Matrix.ProjGenLinGroup.mk A)) :
      Equiv.Perm (Omega K)) = coordinateGLAction K (GeneralLinearGroup.map k.subtype A) := by
  simp only [subfieldD, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
    Matrix.ProjGenLinGroup.map_mk]
  rfl

theorem subfieldD_injective [Finite K] (k : Subfield K) : Function.Injective (subfieldD k) :=
  (pglEquivCoordinateD K).injective.comp
    ((pgl_map_injective k.subtype).comp (pglEquivCoordinateD k).symm.injective)

theorem subfieldD_surj_mk [Finite K] (k : Subfield K) (x : coordinateD k) :
    ∃ V : GL (Fin 2) k, x = pglEquivCoordinateD k (Matrix.ProjGenLinGroup.mk V) := by
  obtain ⟨V, hV⟩ := Matrix.ProjGenLinGroup.mk_surjective ((pglEquivCoordinateD k).symm x)
  exact ⟨V, by rw [hV, MulEquiv.apply_symm_apply]⟩

theorem subfieldD_G [Finite K] (k : Subfield K) (x : coordinateD k)
    (hx : (x : Equiv.Perm (Omega k)) ∈ coordinateG k) :
    (subfieldD k x : Equiv.Perm (Omega K)) ∈ coordinateG K := by
  obtain ⟨V, rfl⟩ := subfieldD_surj_mk k x
  rw [subfieldD_mk]
  have hsq := (CFSG.Semidihedral.ProjectiveNonsquareInvolutions.projective_mem_G_iff k V).mp hx
  apply (CFSG.Semidihedral.ProjectiveNonsquareInvolutions.projective_mem_G_iff K
    (GeneralLinearGroup.map k.subtype V)).mpr
  obtain ⟨r, hr⟩ := hsq
  refine ⟨Units.map k.subtype.toMonoidHom r, ?_⟩
  rw [Matrix.GeneralLinearGroup.map_det, hr, map_mul]
  rfl

theorem fieldExtension_commute_subfieldD [Finite K] (k : Subfield K) (σ : K ≃+* K)
    (hσ : ∀ x ∈ k, σ x = x)
    (x : coordinateD k) :
    fieldExtension K σ * (subfieldD k x : Equiv.Perm (Omega K)) =
      (subfieldD k x : Equiv.Perm (Omega K)) * fieldExtension K σ := by
  obtain ⟨V, rfl⟩ := subfieldD_surj_mk k x
  rw [subfieldD_mk]
  change fieldExtension K σ * coordinatePGLAction K
      (Matrix.ProjGenLinGroup.mk (GeneralLinearGroup.map k.subtype V)) =
    coordinatePGLAction K (Matrix.ProjGenLinGroup.mk (GeneralLinearGroup.map k.subtype V)) *
      fieldExtension K σ
  rw [fieldExtension_mul_coordinatePGLAction]
  congr 2
  rw [pgl2FieldAut_apply]
  change pgl2RingEquiv σ (QuotientGroup.mk' _ (GeneralLinearGroup.map k.subtype V)) =
    QuotientGroup.mk' _ (GeneralLinearGroup.map k.subtype V)
  rw [pgl2RingEquiv_mk]
  congr 1
  apply GeneralLinearGroup.ext
  intro i j
  simp only [GeneralLinearGroup.map_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  exact hσ _ (V.val i j).2

@[expose] def subfieldFixingSubgroup (k : Subfield K) : Subgroup (K ≃+* K) where
  carrier := {τ | ∀ x ∈ k, τ x = x}
  mul_mem' {a b} ha hb x hx := by
    change a (b x) = x
    rw [hb x hx, ha x hx]
  one_mem' x _ := rfl
  inv_mem' {a} ha x hx := by
    change a.symm x = x
    rw [RingEquiv.symm_apply_eq, ha x hx]

theorem mem_zpowers_of_fix {ℓ g : ℕ} (hℓ : ℓ.Prime) (hg : 1 ≤ g)
    (hK : Nat.card K = ℓ ^ (2 * g))
    (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ ℓ ^ g) (k : Subfield K) (hk : ∀ x, x ∈ k ↔ σ x = x)
    (hkcard : Nat.card k = ℓ ^ g) (τ : K ≃+* K) (hτ : ∀ x ∈ k, τ x = x) :
    τ ∈ Subgroup.zpowers σ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, -, -, -, hcardAut, hA⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      hℓ (n := 2 * g) (by omega) hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  set B := subfieldFixingSubgroup k with hB
  obtain ⟨hBdvd, S, hS, hScard⟩ := hA B
  have hle : ∀ x ∈ k, x ∈ S := by
    intro x hx
    have : x ∈ (S : Set K) := by
      rw [hS]
      intro ρ hρ
      exact hρ x hx
    exact this
  have hcardle : Nat.card k ≤ Nat.card S :=
    Nat.card_le_card_of_injective (fun x : k => (⟨x.1, hle x.1 x.2⟩ : S))
      (fun a b h => Subtype.ext (Subtype.mk.inj h))
  rw [hkcard, hScard] at hcardle
  have hgle : g ≤ 2 * g / Nat.card B := (Nat.pow_le_pow_iff_right hℓ.one_lt).mp hcardle
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hB2 : Nat.card B ≤ 2 := by
    by_contra h
    push Not at h
    have : 2 * g / Nat.card B < g := by
      rw [Nat.div_lt_iff_lt_mul hBpos]
      nlinarith
    omega
  have hσk : σ ∈ B := fun x hx => (hk x).mp hx
  have hσ2 : σ ^ 2 = 1 := by
    apply RingEquiv.ext
    intro x
    change σ (σ x) = x
    rw [hσ, hσ, ← pow_mul, ← pow_two, ← pow_mul, mul_comm, ← hK, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
  have hσ1 : σ ≠ 1 := by
    intro h1
    have htop : ∀ x : K, x ∈ k := fun x => (hk x).mpr (by rw [h1]; rfl)
    have : Nat.card k = Nat.card K :=
      Nat.card_congr (Equiv.subtypeUnivEquiv htop)
    rw [hkcard, hK] at this
    have h2 := Nat.pow_right_injective hℓ.two_le this
    omega
  have hord : orderOf σ = 2 := orderOf_eq_prime hσ2 hσ1
  have hzle : Subgroup.zpowers σ ≤ B := (Subgroup.zpowers_le).mpr hσk
  have hzcard : Nat.card (Subgroup.zpowers σ) = 2 := by rw [Nat.card_zpowers, hord]
  have heq : Subgroup.zpowers σ = B :=
    Subgroup.eq_of_le_of_card_ge hzle (by rw [hzcard]; exact hB2)
  rw [heq]
  exact hτ

theorem map_upperGL {k : Subfield K} (t : k) :
    GeneralLinearGroup.map k.subtype (upperGL t) = upperGL (t : K) := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [upperGL, GeneralLinearGroup.map_apply]

theorem map_invGL {k : Subfield K} :
    GeneralLinearGroup.map k.subtype (invGL (K := k)) = invGL := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [invGL, GeneralLinearGroup.map_apply]

theorem fieldExtension_mem_zpowers {σ τ : K ≃+* K} [Finite K] (h : τ ∈ Subgroup.zpowers σ) :
    fieldExtension K τ ∈ Subgroup.zpowers (fieldExtension K σ) := by
  obtain ⟨n, rfl⟩ := h
  refine ⟨n, ?_⟩
  change fieldExtension K σ ^ n = fieldExtension K (σ ^ n)
  rw [← coordinateSemilinearAction_inr, ← coordinateSemilinearAction_inr, ← map_zpow, ← map_zpow]

end SubfieldCentralizer

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GorensteinWalter Matrix
  SubfieldCentralizer

universe u

theorem quadratic_projective_linear_two_subfield_pointwise_centralizer {ℓ g : ℕ} (hℓ : ℓ.Prime)
    (hg : 1 ≤ g) {K : Type u} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ (2 * g))
    (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ ℓ ^ g) (k : Subfield K) (hk : ∀ x, x ∈ k ↔ σ x = x) :
    (∀ A : GL (Fin 2) k, (subfieldD k (pglEquivCoordinateD k (Matrix.ProjGenLinGroup.mk A)) :
      Equiv.Perm (Omega K)) = coordinateGLAction K (GeneralLinearGroup.map k.subtype A)) ∧
    Function.Injective (subfieldD k) ∧
    (∀ x : coordinateD k, (x : Equiv.Perm (Omega k)) ∈ coordinateG k →
      (subfieldD k x : Equiv.Perm (Omega K)) ∈ coordinateG K) ∧
    Nat.card k = ℓ ^ g ∧
    Subgroup.centralizer
        ((((coordinateG k).subgroupOf (coordinateD k)).map
          ((coordinateD K).subtype.comp (subfieldD k)) : Subgroup (Equiv.Perm (Omega K))) :
          Set (Equiv.Perm (Omega K))) ⊓ coordinateE K =
      Subgroup.zpowers (fieldExtension K σ) := by
  have hkcard : Nat.card k = ℓ ^ g := by
    obtain ⟨σ', hσ', -, -, F', hF', hF'card⟩ :=
      CFSG.LinearGroups.finite_field_quadratic_frobenius hℓ hg
        (K := K) (by rw [hK, ← pow_mul, mul_comm])
    rw [← hF'card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [hk, hF', hσ])
  refine ⟨subfieldD_mk k, subfieldD_injective k, subfieldD_G k, hkcard, ?_⟩
  set S := (((coordinateG k).subgroupOf (coordinateD k)).map
    ((coordinateD K).subtype.comp (subfieldD k)) : Subgroup (Equiv.Perm (Omega K))) with hS
  have hσk : ∀ x ∈ k, σ x = x := fun x hx => (hk x).mp hx
  have hT : ∀ t : k, translation K (t : K) ∈ S := by
    intro t
    refine Subgroup.mem_map.mpr ⟨pglEquivCoordinateD k (Matrix.ProjGenLinGroup.mk (upperGL t)),
      ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      change coordinateGLAction k (upperGL t) ∈ coordinateG k
      rw [coordinateGLAction_upperGL]
      exact Subgroup.subset_closure (Or.inl ⟨t, rfl⟩)
    · change (subfieldD k (pglEquivCoordinateD k (Matrix.ProjGenLinGroup.mk (upperGL t))) :
        Equiv.Perm (Omega K)) = _
      rw [subfieldD_mk, map_upperGL, coordinateGLAction_upperGL]
  have hI : inversion K ∈ S := by
    refine Subgroup.mem_map.mpr ⟨pglEquivCoordinateD k (Matrix.ProjGenLinGroup.mk invGL), ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      change coordinateGLAction k invGL ∈ coordinateG k
      rw [coordinateGLAction_invGL]
      exact Subgroup.subset_closure (Or.inr rfl)
    · change (subfieldD k (pglEquivCoordinateD k (Matrix.ProjGenLinGroup.mk invGL)) :
        Equiv.Perm (Omega K)) = _
      rw [subfieldD_mk, map_invGL, coordinateGLAction_invGL]
  apply le_antisymm
  · rintro e ⟨hcent, hE⟩
    rw [← coordinateSemilinearAction_range_eq_E] at hE
    obtain ⟨y, rfl⟩ := hE
    rw [← SemidirectProduct.inl_left_mul_inr_right y, map_mul, coordinateSemilinearAction_inl,
      coordinateSemilinearAction_inr] at hcent ⊢
    set d := coordinatePGLAction K y.left with hd
    set τ := y.right
    have hcomm : ∀ h ∈ S, h * (d * fieldExtension K τ) = d * fieldExtension K τ * h :=
      fun h hh => Subgroup.mem_centralizer_iff.mp hcent h hh
    have hdD : d ∈ coordinateD K := by
      rw [← coordinatePGLAction_range_eq_D]
      exact ⟨_, rfl⟩
    have key : ∀ T : Equiv.Perm (Omega K), T ∈ S →
        fieldExtension K τ * T = T * fieldExtension K τ → d * T = T * d := by
      intro T hTS hfT
      have := hcomm T hTS
      have h2 : (T * d) * fieldExtension K τ = (d * T) * fieldExtension K τ := by
        rw [mul_assoc, this, mul_assoc, hfT, mul_assoc]
      exact (mul_right_cancel h2).symm
    have h1 : d * translation K 1 = translation K 1 * d := by
      have hT1 := hT 1
      rw [OneMemClass.coe_one] at hT1
      exact key _ hT1 (by rw [fieldExtension_mul_translation, map_one])
    have h2 : d * inversion K = inversion K * d := key _ hI (fieldExtension_mul_inversion τ)
    have hd1 : d = 1 := eq_one_of_commute_translation_inversion d hdD h1 h2
    rw [hd1, one_mul] at hcomm ⊢
    have hτk : ∀ x ∈ k, τ x = x := by
      intro x hx
      have := hcomm _ (hT ⟨x, hx⟩)
      rw [fieldExtension_mul_translation] at this
      have h3 := mul_right_cancel this
      have h4 := congrArg (fun φ : Equiv.Perm (Omega K) => φ (some 0)) h3
      simp only [translation_some, zero_add, Option.some.injEq] at h4
      exact h4.symm
    exact fieldExtension_mem_zpowers (mem_zpowers_of_fix hℓ hg hK σ hσ k hk hkcard τ hτk)
  · rw [Subgroup.zpowers_le]
    refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, Subgroup.subset_closure (Or.inr ⟨σ, rfl⟩)⟩
    intro h hh
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hh
    exact (fieldExtension_commute_subfieldD k σ hσk x).symm

end CFSG.ComponentClassification.UnbalancedGS
