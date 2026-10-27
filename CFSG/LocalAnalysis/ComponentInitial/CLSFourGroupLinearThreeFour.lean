module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourRoots
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.PRank

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearThreeFourOuter

open LinearFlag

open Matrix

variable {k : Type*} [Field k]

theorem card_units_eq_three (hk : Nat.card k = 4) : Nat.card kˣ = 3 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := Fintype.ofFinite k
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hk]

theorem units_pow_three (hk : Nat.card k = 4) (x : kˣ) : x ^ 3 = 1 :=
  Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact LinearFieldFour.pow_three_eq_one hk x.ne_zero)

section Sigma

variable {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2)
include hσ

theorem sigma_mul_self (hk : Nat.card k = 4) : σ * σ = 1 := by
  refine RingEquiv.ext fun a => ?_
  change σ (σ a) = a
  rw [hσ, hσ, ← pow_mul]
  exact LinearFieldFour.pow_four_eq_self hk a

theorem units_map_sigma (hk : Nat.card k = 4) (x : kˣ) :
    Units.map (σ : k →+* k).toMonoidHom x = x⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  refine Units.ext ?_
  rw [Units.val_mul, Units.coe_map, Units.val_one]
  change σ (x : k) * x = 1
  rw [hσ, ← pow_succ, ← Units.val_pow_eq_pow_val, units_pow_three hk, Units.val_one]

theorem sigma_ne_one (hk : Nat.card k = 4) : σ ≠ 1 := by
  obtain ⟨ω, hω0, hω1⟩ := LinearFieldFour.exists_ne_zero_ne_one hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  intro h
  have h1 : σ ω = ω := by rw [h]; rfl
  rw [hσ, sq, LinearFieldFour.omega_mul_omega hk hω0 hω1] at h1
  exact one_ne_zero (by linear_combination h1)

theorem ringEquiv_eq_one_or (hk : Nat.card k = 4) (τ : k ≃+* k) : τ = 1 ∨ τ = σ := by
  obtain ⟨ω, hω0, hω1⟩ := LinearFieldFour.exists_ne_zero_ne_one hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hωω := LinearFieldFour.omega_mul_omega hk hω0 hω1
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  rcases LinearFieldFour.eq_zero_or_eq_one_or hk hω0 hω1 (τ ω) with h | h | h | h
  · exact absurd ((map_eq_zero_iff τ τ.injective).1 h) hω0
  · exact absurd (τ.injective (h.trans (map_one τ).symm)) hω1
  · left
    refine RingEquiv.ext fun a => ?_
    rcases LinearFieldFour.eq_zero_or_eq_one_or hk hω0 hω1 a with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact h
    · rw [map_add, map_one, h]
      rfl
  · right
    refine RingEquiv.ext fun a => ?_
    rcases LinearFieldFour.eq_zero_or_eq_one_or hk hω0 hω1 a with rfl | rfl | rfl | rfl
    · simp
    · simp
    · rw [h, hσ, sq, hωω]
    · rw [map_add, map_one, h, hσ, sq]
      linear_combination (-1 : k) * hωω - ω * h2

end Sigma

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem val_one_two : (1 : ZMod 2).val = 1 :=
  rfl

theorem pow_val_add {G : Type*} [Monoid G] {g : G} (hg : g * g = 1) (a b : ZMod 2) :
    g ^ (a + b).val = g ^ a.val * g ^ b.val := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;>
    simp [val_one_two, hg, show (1 + 1 : ZMod 2) = 0 from rfl]

theorem not_conj_single_transpose (C : GL (Fin 3) k)
    (h : ∀ i j : Fin 3, i ≠ j → (C : Matrix (Fin 3) (Fin 3) k) * Matrix.single i j (1 : k) =
      Matrix.single j i (1 : k) * (C : Matrix (Fin 3) (Fin 3) k)) : False := by
  have h02 := h 0 2 (by decide)
  have h01 := h 0 1 (by decide)
  have h12 := h 1 2 (by decide)
  have e : Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : k) =
      Matrix.single 0 1 1 * Matrix.single 1 2 1 := by
    rw [single_mul_single_same, mul_one]
  have hz : Matrix.single (2 : Fin 3) (0 : Fin 3) (1 : k) * (C : Matrix (Fin 3) (Fin 3) k) =
      0 := by
    rw [← h02, e, ← Matrix.mul_assoc, h01, Matrix.mul_assoc, h12, ← Matrix.mul_assoc,
      single_mul_single_of_ne (1 : k) (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (by decide) (1 : k),
      Matrix.zero_mul]
  have hz' : Matrix.single (2 : Fin 3) (0 : Fin 3) (1 : k) = 0 := by
    have := congrArg (· * ((C⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) hz
    simpa [Matrix.mul_assoc] using this
  have := congrFun (congrFun hz' 2) 0
  simp at this

@[expose] def tvSL {i j : Fin 3} (hij : i ≠ j) : Matrix.SpecialLinearGroup (Fin 3) k :=
  ⟨transvection i j 1, det_transvection_of_ne i j hij 1⟩

theorem tvSL_inv [CharP k 2] {i j : Fin 3} (hij : i ≠ j) :
    ((tvSL (k := k) hij)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) = tvSL hij := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  change transvection i j (1 : k) * transvection i j 1 = 1
  rw [transvection_mul_transvection_same i j hij, CharTwo.add_self_eq_zero, transvection_zero]

theorem map_tvSL (ρ : k ≃+* k) {i j : Fin 3} (hij : i ≠ j) :
    Matrix.SpecialLinearGroup.map ρ.toRingHom (tvSL hij) = tvSL hij := by
  refine Subtype.ext ?_
  change ρ.toRingHom.mapMatrix (transvection i j 1) = transvection i j 1
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, transvection, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem transpose_transvection (i j : Fin 3) (c : k) :
    (transvection i j c)ᵀ = transvection j i c := by
  rw [transvection, transvection, transpose_add, transpose_one, transpose_single]

theorem trace_transvection {i j : Fin 3} (hij : i ≠ j) (c : k) :
    (transvection i j c).trace = 3 := by
  simp [transvection, Matrix.trace_add, Matrix.trace_single_eq_of_ne _ _ _ hij]

theorem conjAut_mul_fieldAut_ne_dualAut [CharP k 2] (C : GL (Fin 3) k) (ρ : k ≃+* k) :
    conjAut 3 k C * fieldAut 3 k ρ ≠ dualAut 3 k := by
  intro h
  refine not_conj_single_transpose C fun i j hij => ?_
  have hg := congrArg (fun φ : MulAut (projectiveSL 3 k) => φ (proj 3 k (tvSL hij))) h
  simp only [MulAut.mul_apply, fieldAut_proj, conjAut_proj, dualAut_proj] at hg
  rw [map_tvSL, tvSL_inv] at hg
  set g := tvSL (k := k) hij
  set M := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k C g
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_proj_iff.1 hg)
  have hN : ((g.transpose : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      (M : Matrix (Fin 3) (Fin 3) k) * scalar (Fin 3) (c : k) := by
    have hc' : ((M⁻¹ * g.transpose : Matrix.SpecialLinearGroup (Fin 3) k) :
        Matrix (Fin 3) (Fin 3) k) = scalar (Fin 3) (c : k) := hc
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv] at hc'
    have h1 : (M : Matrix (Fin 3) (Fin 3) k) * adjugate (M : Matrix (Fin 3) (Fin 3) k) = 1 := by
      rw [Matrix.mul_adjugate, M.prop, one_smul]
    calc ((g.transpose : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)
        = (M : Matrix (Fin 3) (Fin 3) k) * adjugate (M : Matrix (Fin 3) (Fin 3) k) *
            ((g.transpose : Matrix.SpecialLinearGroup (Fin 3) k) :
              Matrix (Fin 3) (Fin 3) k) := by
          rw [h1, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, hc']
  have hM : (M : Matrix (Fin 3) (Fin 3) k) = (C : Matrix (Fin 3) (Fin 3) k) *
      transvection i j 1 * ((C⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) :=
    coe_slConjugation C g
  have hgT : ((g.transpose : Matrix.SpecialLinearGroup (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k) = transvection j i 1 := by
    rw [Matrix.SpecialLinearGroup.coe_transpose]
    exact transpose_transvection i j 1
  have hCC : ((C⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
      (C : Matrix (Fin 3) (Fin 3) k) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hCC' : (C : Matrix (Fin 3) (Fin 3) k) *
      ((C⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hc1 : (c : k) = 1 := by
    have htr := congrArg Matrix.trace hN
    rw [hgT, trace_transvection hij.symm, hM, scalar_apply, ← smul_one_eq_diagonal,
      Matrix.mul_smul, Matrix.mul_one, trace_smul, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      hCC, Matrix.one_mul, trace_transvection hij, smul_eq_mul] at htr
    have h3 : (3 : k) = 1 := by linear_combination (CharTwo.two_eq_zero : (2 : k) = 0)
    rw [h3, mul_one] at htr
    exact htr.symm
  rw [hc1, hgT, hM, map_one, Matrix.mul_one] at hN
  have hN' : Matrix.single j i (1 : k) = (C : Matrix (Fin 3) (Fin 3) k) *
      Matrix.single i j 1 * ((C⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
    rw [transvection, transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hCC'] at hN
    exact add_left_cancel hN
  rw [hN', Matrix.mul_assoc, hCC, Matrix.mul_one]

section NormalForm

variable (σ : k ≃+* k)

@[expose] def twistF (a : ZMod 2) (B : GL (Fin 3) k) : GL (Fin 3) k :=
  if a = 0 then B else GeneralLinearGroup.map (σ : k →+* k) B

@[expose] def twistD (b : ZMod 2) (B : GL (Fin 3) k) : GL (Fin 3) k :=
  if b = 0 then B else GeneralLinearGroup.inverseTranspose B

@[expose] def nf (A : GL (Fin 3) k) (a b : ZMod 2) : MulAut (projectiveSL 3 k) :=
  conjAut 3 k A * fieldAut 3 k σ ^ a.val * dualAut 3 k ^ b.val

theorem dualAut_mul_self : dualAut 3 k * dualAut 3 k = 1 :=
  (standard_automorphism_transport (K := k) (n := 3)).2.2.2.1

theorem dualAut_pow_mul_conjAut (b : ZMod 2) (B : GL (Fin 3) k) :
    dualAut 3 k ^ b.val * conjAut 3 k B = conjAut 3 k (twistD b B) * dualAut 3 k ^ b.val := by
  rcases zmod_two_cases b with rfl | rfl
  · simp [twistD]
  · simp [twistD, val_one_two, dualAut_mul_conjAut]

theorem fieldAut_pow_mul_conjAut (a : ZMod 2) (B : GL (Fin 3) k) :
    fieldAut 3 k σ ^ a.val * conjAut 3 k B =
      conjAut 3 k (twistF σ a B) * fieldAut 3 k σ ^ a.val := by
  rcases zmod_two_cases a with rfl | rfl
  · simp [twistF]
  · simp [twistF, val_one_two, fieldAut_mul_conjAut]

theorem twistF_one (a : ZMod 2) : twistF σ a (1 : GL (Fin 3) k) = 1 := by
  unfold twistF
  split_ifs <;> simp

theorem twistD_one (b : ZMod 2) : twistD b (1 : GL (Fin 3) k) = 1 := by
  unfold twistD
  split_ifs <;> simp

theorem nf_mul (hff : fieldAut 3 k σ * fieldAut 3 k σ = 1) (A B : GL (Fin 3) k)
    (a b a' b' : ZMod 2) :
    nf σ A a b * nf σ B a' b' = nf σ (A * twistF σ a (twistD b B)) (a + a') (b + b') := by
  have hdf : Commute (dualAut 3 k ^ b.val) (fieldAut 3 k σ ^ a'.val) :=
    (show Commute (dualAut 3 k) (fieldAut 3 k σ) from dualAut_mul_fieldAut σ).pow_pow _ _
  unfold nf
  rw [pow_val_add hff, pow_val_add dualAut_mul_self, map_mul]
  calc conjAut 3 k A * fieldAut 3 k σ ^ a.val * dualAut 3 k ^ b.val *
        (conjAut 3 k B * fieldAut 3 k σ ^ a'.val * dualAut 3 k ^ b'.val)
      = conjAut 3 k A * fieldAut 3 k σ ^ a.val * (dualAut 3 k ^ b.val * conjAut 3 k B) *
          fieldAut 3 k σ ^ a'.val * dualAut 3 k ^ b'.val := by simp only [mul_assoc]
    _ = conjAut 3 k A * (fieldAut 3 k σ ^ a.val * conjAut 3 k (twistD b B)) *
          (dualAut 3 k ^ b.val * fieldAut 3 k σ ^ a'.val) * dualAut 3 k ^ b'.val := by
        rw [dualAut_pow_mul_conjAut]
        simp only [mul_assoc]
    _ = _ := by
        rw [fieldAut_pow_mul_conjAut, hdf.eq]
        simp only [mul_assoc]

theorem nf_zero_zero (A : GL (Fin 3) k) : nf σ A 0 0 = conjAut 3 k A := by
  simp [nf]

theorem nf_one_zero : nf σ (1 : GL (Fin 3) k) 1 0 = fieldAut 3 k σ := by
  simp [nf, val_one_two]

theorem nf_zero_one : nf σ (1 : GL (Fin 3) k) 0 1 = dualAut 3 k := by
  simp [nf, val_one_two]

variable {σ} (hσ : ∀ a, σ a = a ^ 2)
include hσ

theorem fieldAut_sigma_mul_self (hk : Nat.card k = 4) :
    fieldAut 3 k σ * fieldAut 3 k σ = 1 := by
  rw [← map_mul, sigma_mul_self hσ hk, map_one]

theorem det_map_sigma (hk : Nat.card k = 4) (B : GL (Fin 3) k) :
    GeneralLinearGroup.det (GeneralLinearGroup.map (σ : k →+* k) B) =
      (GeneralLinearGroup.det B)⁻¹ := by
  rw [← units_map_sigma hσ hk]
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, Units.coe_map, GeneralLinearGroup.val_det_apply]
  change Matrix.det ((σ : k →+* k).mapMatrix (B : Matrix (Fin 3) (Fin 3) k)) = _
  rw [← RingHom.map_det]
  rfl

omit hσ in
theorem det_inverseTranspose (B : GL (Fin 3) k) :
    GeneralLinearGroup.det (GeneralLinearGroup.inverseTranspose B) =
      (GeneralLinearGroup.det B)⁻¹ := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_inverseTranspose, det_transpose,
    ← GeneralLinearGroup.val_det_apply, map_inv]

theorem det_twist (hk : Nat.card k = 4) (a b : ZMod 2) (B : GL (Fin 3) k) :
    GeneralLinearGroup.det (twistF σ a (twistD b B)) =
      if a + b = 0 then GeneralLinearGroup.det B else (GeneralLinearGroup.det B)⁻¹ := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;>
    simp [twistF, twistD, det_map_sigma hσ hk, det_inverseTranspose,
      show (1 + 1 : ZMod 2) = 0 from rfl]

theorem nf_eq_one (hk : Nat.card k = 4) {C : GL (Fin 3) k} {x y : ZMod 2}
    (h : nf σ C x y = 1) : GeneralLinearGroup.det C = 1 ∧ x = 0 ∧ y = 0 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  rcases zmod_two_cases y with rfl | rfl
  · rcases zmod_two_cases x with rfl | rfl
    · rw [nf_zero_zero] at h
      obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl C 1
        (by rw [map_one, mul_one, h])
      refine ⟨?_, rfl, rfl⟩
      rw [← hc]
      refine Units.ext ?_
      rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar, scalar_apply,
        det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Units.val_one,
        ← Units.val_pow_eq_pow_val, units_pow_three hk, Units.val_one]
    · simp only [nf, val_one_two, pow_one, ZMod.val_zero, pow_zero, mul_one] at h
      exact absurd (eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl C σ h).1 (sigma_ne_one hσ hk)
  · exfalso
    simp only [nf, val_one_two, pow_one] at h
    have hd : dualAut 3 k = (conjAut 3 k C * fieldAut 3 k σ ^ x.val)⁻¹ :=
      eq_inv_of_mul_eq_one_right h
    have hfx : (fieldAut 3 k σ ^ x.val)⁻¹ = fieldAut 3 k σ ^ x.val := by
      rcases zmod_two_cases x with rfl | rfl
      · simp
      · rw [val_one_two, pow_one]
        exact inv_eq_of_mul_eq_one_right (fieldAut_sigma_mul_self hσ hk)
    rw [_root_.mul_inv_rev, hfx, ← map_inv, fieldAut_pow_mul_conjAut, ← map_pow] at hd
    exact conjAut_mul_fieldAut_ne_dualAut _ _ hd.symm

theorem nf_inj (hk : Nat.card k = 4) {A B : GL (Fin 3) k} {a b a' b' : ZMod 2}
    (h : nf σ A a b = nf σ B a' b') :
    GeneralLinearGroup.det A = GeneralLinearGroup.det B ∧ a = a' ∧ b = b' := by
  have hff := fieldAut_sigma_mul_self hσ hk
  have hinv : nf σ 1 a' b' * nf σ 1 a' b' = 1 := by
    rw [nf_mul σ hff, twistD_one, twistF_one, mul_one, CharTwo.add_self_eq_zero,
      CharTwo.add_self_eq_zero, nf_zero_zero, map_one]
  have hB : nf σ B⁻¹ 0 0 * nf σ B a' b' = nf σ 1 a' b' := by
    rw [nf_mul σ hff, zero_add, zero_add]
    simp [twistF, twistD]
  have hA : nf σ B⁻¹ 0 0 * nf σ A a b = nf σ (B⁻¹ * A) a b := by
    rw [nf_mul σ hff, zero_add, zero_add]
    simp [twistF, twistD]
  have h1 : nf σ (B⁻¹ * A) a b * nf σ 1 a' b' = 1 := by
    rw [← hA, h, hB, hinv]
  rw [nf_mul σ hff, twistD_one, twistF_one, mul_one] at h1
  obtain ⟨hdet, ha, hb⟩ := nf_eq_one hσ hk h1
  rw [map_mul, map_inv, inv_mul_eq_one] at hdet
  refine ⟨hdet.symm, ?_, ?_⟩
  · rw [← sub_eq_zero, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
    exact ha
  · rw [← sub_eq_zero, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
    exact hb

theorem exists_nf (hk : Nat.card k = 4) (α : MulAut (projectiveSL 3 k)) :
    ∃ t : GL (Fin 3) k × ZMod 2 × ZMod 2, α = nf σ t.1 t.2.1 t.2.2 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  obtain ⟨A, τ, ε, hε, rfl⟩ := (automorphism_generation (K := k) (n := 3) le_rfl).2 α
  have hδ : dualAut 3 k ^ ε = dualAut 3 k ^ ((ε : ZMod 2)).val := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  rcases ringEquiv_eq_one_or hσ hk τ with rfl | rfl
  · exact ⟨(A, 0, ε), by simp [nf, hδ]⟩
  · exact ⟨(A, 1, ε), by simp [nf, hδ, val_one_two]⟩

end NormalForm

@[expose] def inversionAction (G : Type*) [CommGroup G] :
    Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* MulAut G where
  toFun v := if Multiplicative.toAdd v.1 + Multiplicative.toAdd v.2 = 0 then 1 else MulEquiv.inv G
  map_one' := by simp
  map_mul' v w := by
    have hinv : MulEquiv.inv G * MulEquiv.inv G = 1 := MulEquiv.ext fun x => inv_inv x
    have e : Multiplicative.toAdd (v * w).1 + Multiplicative.toAdd (v * w).2 =
        (Multiplicative.toAdd v.1 + Multiplicative.toAdd v.2) +
          (Multiplicative.toAdd w.1 + Multiplicative.toAdd w.2) := by
      simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul]
      ring
    simp only [e]
    generalize Multiplicative.toAdd v.1 + Multiplicative.toAdd v.2 = s
    generalize Multiplicative.toAdd w.1 + Multiplicative.toAdd w.2 = t
    rcases zmod_two_cases s with rfl | rfl <;> rcases zmod_two_cases t with rfl | rfl <;>
      simp [hinv, show (1 + 1 : ZMod 2) = 0 from rfl]

theorem inversionAction_apply {G : Type*} [CommGroup G] (a b : ZMod 2) (x : G) :
    inversionAction G (Multiplicative.ofAdd a, Multiplicative.ofAdd b) x =
      if a + b = 0 then x else x⁻¹ := by
  simp only [inversionAction, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  split_ifs <;> rfl

@[expose] def diagGL (x : kˣ) : GL (Fin 3) k :=
  ⟨Matrix.diagonal ![(x : k), 1, 1], Matrix.diagonal ![((x⁻¹ : kˣ) : k), 1, 1],
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp,
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp⟩

theorem coe_diagGL (x : kˣ) :
    ((diagGL x : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = Matrix.diagonal ![(x : k), 1, 1] :=
  rfl

theorem det_diagGL (x : kˣ) : GeneralLinearGroup.det (diagGL x) = x := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, coe_diagGL, det_diagonal, Fin.prod_univ_three]
  simp

instance innerAut_normal (G : Type*) [Group G] : (MulAut.conj : G →* MulAut G).range.Normal where
  conj_mem := by
    rintro _ ⟨p, rfl⟩ φ
    refine ⟨φ p, ?_⟩
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]

theorem conjAut_mem_range_conj_iff (hk : Nat.card k = 4) (A : GL (Fin 3) k) :
    conjAut 3 k A ∈ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range ↔
      GeneralLinearGroup.det A = 1 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨g, rfl⟩ := proj_surjective 3 k x
    rw [← conjAut_toGL] at hx
    have h1 : conjAut 3 k ((Matrix.SpecialLinearGroup.toGL g)⁻¹ * A) = 1 := by
      rw [map_mul, map_inv, hx, inv_mul_cancel]
    obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (K := k) (n := 3) le_rfl
      ((Matrix.SpecialLinearGroup.toGL g)⁻¹ * A) 1 (by rw [map_one, mul_one]; exact h1)
    have hdet := congrArg GeneralLinearGroup.det hc
    have hg : GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL g) = 1 :=
      Units.ext (by rw [GeneralLinearGroup.val_det_apply]; exact g.prop)
    have hsc : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) c) = 1 := by
      refine Units.ext ?_
      rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar, scalar_apply,
        det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Units.val_one,
        ← Units.val_pow_eq_pow_val, units_pow_three hk, Units.val_one]
    rw [hsc, map_mul, map_inv, hg, inv_one, one_mul] at hdet
    exact hdet.symm
  · intro h
    let g : Matrix.SpecialLinearGroup (Fin 3) k :=
      ⟨(A : Matrix (Fin 3) (Fin 3) k), by
        rw [← GeneralLinearGroup.val_det_apply, h, Units.val_one]⟩
    refine ⟨proj 3 k g, ?_⟩
    rw [← conjAut_toGL]
    congr 1
    exact Units.ext rfl

section Outer

variable {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2)
include hσ

theorem exists_outerHom (hk : Nat.card k = 4) :
    ∃ Ψ : MulAut (projectiveSL 3 k) →* kˣ ⋊[inversionAction kˣ]
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)),
      ∀ (A : GL (Fin 3) k) (a b : ZMod 2), Ψ (nf σ A a b) =
        ⟨GeneralLinearGroup.det A, (Multiplicative.ofAdd a, Multiplicative.ofAdd b)⟩ := by
  classical
  choose t ht using exists_nf hσ hk
  let F : MulAut (projectiveSL 3 k) → kˣ ⋊[inversionAction kˣ]
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := fun α =>
    ⟨GeneralLinearGroup.det (t α).1,
      (Multiplicative.ofAdd (t α).2.1, Multiplicative.ofAdd (t α).2.2)⟩
  have hF : ∀ (A : GL (Fin 3) k) (a b : ZMod 2), F (nf σ A a b) =
      ⟨GeneralLinearGroup.det A, (Multiplicative.ofAdd a, Multiplicative.ofAdd b)⟩ := by
    intro A a b
    obtain ⟨h1, h2, h3⟩ := nf_inj hσ hk (ht (nf σ A a b)).symm
    change (⟨GeneralLinearGroup.det (t (nf σ A a b)).1,
      (Multiplicative.ofAdd (t (nf σ A a b)).2.1,
        Multiplicative.ofAdd (t (nf σ A a b)).2.2)⟩ :
          kˣ ⋊[inversionAction kˣ] (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) = _
    rw [h1, h2, h3]
  refine ⟨{ toFun := F, map_one' := ?_, map_mul' := ?_ }, hF⟩
  · rw [show (1 : MulAut (projectiveSL 3 k)) = nf σ 1 0 0 by rw [nf_zero_zero, map_one], hF]
    refine SemidirectProduct.ext ?_ ?_
    · simp
    · rfl
  · intro α β
    obtain ⟨⟨A, a, b⟩, rfl⟩ := exists_nf hσ hk α
    obtain ⟨⟨B, a', b'⟩, rfl⟩ := exists_nf hσ hk β
    change F (nf σ A a b * nf σ B a' b') = F (nf σ A a b) * F (nf σ B a' b')
    rw [nf_mul σ (fieldAut_sigma_mul_self hσ hk), hF, hF, hF]
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.mul_left, map_mul, det_twist hσ hk, inversionAction_apply]
    · rw [SemidirectProduct.mul_right]
      rfl

theorem ker_eq_range_conj (hk : Nat.card k = 4)
    {Ψ : MulAut (projectiveSL 3 k) →* kˣ ⋊[inversionAction kˣ]
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))}
    (hΨ : ∀ (A : GL (Fin 3) k) (a b : ZMod 2), Ψ (nf σ A a b) =
      ⟨GeneralLinearGroup.det A, (Multiplicative.ofAdd a, Multiplicative.ofAdd b)⟩) :
    Ψ.ker = (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range := by
  ext α
  obtain ⟨⟨A, a, b⟩, rfl⟩ := exists_nf hσ hk α
  dsimp only
  rw [MonoidHom.mem_ker, hΨ]
  constructor
  · intro h
    have hl := congrArg SemidirectProduct.left h
    have hr := congrArg SemidirectProduct.right h
    simp only [SemidirectProduct.one_left, SemidirectProduct.one_right, Prod.ext_iff,
      Prod.fst_one, Prod.snd_one, ofAdd_eq_one] at hl hr
    obtain ⟨rfl, rfl⟩ := hr
    rw [nf_zero_zero]
    exact (conjAut_mem_range_conj_iff hk A).2 hl
  · intro h
    obtain ⟨g, hg⟩ := h
    obtain ⟨g, rfl⟩ := proj_surjective 3 k g
    rw [← conjAut_toGL, ← nf_zero_zero σ] at hg
    obtain ⟨hdet, rfl, rfl⟩ := nf_inj hσ hk hg.symm
    refine SemidirectProduct.ext ?_ rfl
    change GeneralLinearGroup.det A = 1
    rw [hdet]
    exact Units.ext (by rw [GeneralLinearGroup.val_det_apply]; exact g.prop)

omit hσ in
theorem surjective_of_nf
    {Ψ : MulAut (projectiveSL 3 k) →* kˣ ⋊[inversionAction kˣ]
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))}
    (hΨ : ∀ (A : GL (Fin 3) k) (a b : ZMod 2), Ψ (nf σ A a b) =
      ⟨GeneralLinearGroup.det A, (Multiplicative.ofAdd a, Multiplicative.ofAdd b)⟩) :
    Function.Surjective Ψ := by
  rintro ⟨x, v₁, v₂⟩
  refine ⟨nf σ (diagGL x) (Multiplicative.toAdd v₁) (Multiplicative.toAdd v₂), ?_⟩
  rw [hΨ, det_diagGL]
  rfl

end Outer

section Matrices

variable {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2)

theorem diagGL_mul (x y : kˣ) : diagGL x * diagGL y = (diagGL (x * y) : GL (Fin 3) k) := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_diagGL, coe_diagGL, coe_diagGL, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

theorem diagGL_one : diagGL (1 : kˣ) = (1 : GL (Fin 3) k) := by
  refine Units.ext ?_
  ext i j
  rw [coe_diagGL]
  fin_cases i <;> fin_cases j <;> simp

theorem coe_diagGL_inv (x : kˣ) :
    (((diagGL x)⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      Matrix.diagonal ![((x⁻¹ : kˣ) : k), 1, 1] :=
  rfl

theorem inverseTranspose_diagGL (x : kˣ) :
    GeneralLinearGroup.inverseTranspose (diagGL x) = (diagGL x⁻¹ : GL (Fin 3) k) := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.coe_inverseTranspose, coe_diagGL_inv, diagonal_transpose, coe_diagGL]

include hσ in
theorem map_sigma_diagGL (hk : Nat.card k = 4) (x : kˣ) :
    GeneralLinearGroup.map (σ : k →+* k) (diagGL x) = (diagGL x⁻¹ : GL (Fin 3) k) := by
  refine Units.ext ?_
  have hx : σ (x : k) = ((x⁻¹ : kˣ) : k) := congrArg Units.val (units_map_sigma hσ hk x)
  ext i j
  rw [GeneralLinearGroup.map_apply, coe_diagGL, coe_diagGL]
  fin_cases i <;> fin_cases j <;> simp [hx]

variable [CharP k 2]

@[expose] def s23GL : GL (Fin 3) k :=
  Matrix.SpecialLinearGroup.toGL LinearFieldFour.s₂₃Mat

theorem coe_s23GL : ((s23GL : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = LinearFieldFour.s₂₃M :=
  rfl

theorem s23GL_mul_self : (s23GL * s23GL : GL (Fin 3) k) = 1 := by
  rw [s23GL, ← map_mul, LinearFieldFour.s₂₃Mat_mul_self, map_one]

theorem s23GL_inv : (s23GL⁻¹ : GL (Fin 3) k) = s23GL :=
  inv_eq_of_mul_eq_one_right s23GL_mul_self

theorem inverseTranspose_s23GL :
    GeneralLinearGroup.inverseTranspose (s23GL : GL (Fin 3) k) = s23GL := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.coe_inverseTranspose, s23GL_inv, coe_s23GL]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem map_s23GL (ρ : k ≃+* k) :
    GeneralLinearGroup.map (ρ : k →+* k) (s23GL : GL (Fin 3) k) = s23GL := by
  refine Units.ext ?_
  ext i j
  rw [GeneralLinearGroup.map_apply, coe_s23GL]
  fin_cases i <;> fin_cases j <;> simp [LinearFieldFour.s₂₃M]

theorem diagGL_mul_s23GL (x : kˣ) : diagGL x * s23GL = (s23GL * diagGL x : GL (Fin 3) k) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_diagGL, coe_s23GL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearFieldFour.s₂₃M, Matrix.mul_apply, Fin.sum_univ_three]

theorem s23GL_ne_scalar (c : kˣ) :
    GeneralLinearGroup.scalar (Fin 3) c ≠ (s23GL : GL (Fin 3) k) := by
  intro h
  have h00 := congrArg (fun g : GL (Fin 3) k => (g : Matrix (Fin 3) (Fin 3) k) 0 0) h
  have h11 := congrArg (fun g : GL (Fin 3) k => (g : Matrix (Fin 3) (Fin 3) k) 1 1) h
  simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq, coe_s23GL] at h00 h11
  have h0 : (c : k) = 1 := h00
  have h1 : (c : k) = 0 := h11
  exact one_ne_zero (h0.symm.trans h1)

end Matrices

theorem zmod_two_add_self (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

theorem ofAdd_one_pow_val (a : ZMod 2) :
    Multiplicative.ofAdd (1 : ZMod 2) ^ a.val = Multiplicative.ofAdd a := by
  rcases zmod_two_cases a with rfl | rfl <;> rfl

theorem exists_elementaryAbelian_eight {G : Type*} [Group G] {x y z : G}
    (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z) (hx : x * x = 1)
    (hy : y * y = 1) (hz : z * z = 1)
    (h : ∀ a b c : ZMod 2, x ^ a.val * y ^ b.val * z ^ c.val = 1 → a = 0 ∧ b = 0 ∧ c = 0) :
    ∃ E : Subgroup G, CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧
      ∀ K : Subgroup G, x ∈ K → y ∈ K → z ∈ K → E ≤ K := by
  set F : ZMod 2 × ZMod 2 × ZMod 2 → G := fun v => x ^ v.1.val * y ^ v.2.1.val * z ^ v.2.2.val
    with hFdef
  have hF : ∀ v w, F v * F w = F (v + w) := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩
    simp only [hFdef, Prod.mk_add_mk, pow_val_add hx, pow_val_add hy, pow_val_add hz]
    have h1 : Commute (z ^ c.val) (x ^ a'.val) := (hxz.pow_pow _ _).symm
    have h2 : Commute (y ^ b.val) (x ^ a'.val) := (hxy.pow_pow _ _).symm
    have h3 : Commute (z ^ c.val) (y ^ b'.val) := (hyz.pow_pow _ _).symm
    calc x ^ a.val * y ^ b.val * z ^ c.val * (x ^ a'.val * y ^ b'.val * z ^ c'.val)
        = x ^ a.val * (y ^ b.val * (z ^ c.val * x ^ a'.val)) * y ^ b'.val * z ^ c'.val := by
          simp only [mul_assoc]
      _ = x ^ a.val * (y ^ b.val * x ^ a'.val * z ^ c.val) * y ^ b'.val * z ^ c'.val := by
          rw [h1.eq]
          simp only [mul_assoc]
      _ = x ^ a.val * x ^ a'.val * (y ^ b.val * (z ^ c.val * y ^ b'.val)) * z ^ c'.val := by
          rw [h2.eq]
          simp only [mul_assoc]
      _ = x ^ a.val * x ^ a'.val * (y ^ b.val * y ^ b'.val) * (z ^ c.val * z ^ c'.val) := by
          rw [h3.eq]
          simp only [mul_assoc]
  have hF0 : F 0 = 1 := by simp [hFdef]
  have hFF : ∀ v, F v * F v = 1 := fun v => by
    rw [hF, show v + v = 0 from Prod.ext (zmod_two_add_self _)
      (Prod.ext (zmod_two_add_self _) (zmod_two_add_self _)), hF0]
  let E : Subgroup G :=
    { carrier := Set.range F
      mul_mem' := by
        rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
        exact ⟨v + w, (hF v w).symm⟩
      one_mem' := ⟨0, hF0⟩
      inv_mem' := by
        rintro _ ⟨v, rfl⟩
        exact ⟨v, (inv_eq_of_mul_eq_one_right (hFF v)).symm⟩ }
  have hinj : Function.Injective F := by
    intro v w hvw
    have h0 : F (v + w) = 1 := by rw [← hF, hvw, hFF]
    obtain ⟨ha, hb, hc⟩ := h (v + w).1 (v + w).2.1 (v + w).2.2 h0
    have e : ∀ s t : ZMod 2, s + t = 0 → s = t := fun s t hst => by
      rw [← sub_eq_zero, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
      exact hst
    exact Prod.ext (e _ _ ha) (Prod.ext (e _ _ hb) (e _ _ hc))
  refine ⟨E, ?_, ?_, ?_⟩
  · refine { is_comm := ⟨fun a b => Subtype.ext ?_⟩, exponent_dvd_p := ?_ }
    · obtain ⟨_, v, hv⟩ := a
      obtain ⟨_, w, hw⟩ := b
      subst hv hw
      change F v * F w = F w * F v
      rw [hF, hF, add_comm]
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext ?_
      obtain ⟨_, v, hv⟩ := a
      subst hv
      change F v ^ 2 = 1
      rw [sq, hFF]
  · change Nat.card (Set.range F) = 8
    rw [Nat.card_range_of_injective hinj, Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  · rintro K hxK hyK hzK _ ⟨v, rfl⟩
    exact mul_mem (mul_mem (pow_mem hxK _) (pow_mem hyK _)) (pow_mem hzK _)

theorem three_le_pRank {G : Type*} [Group G] [Finite G] {X E : Subgroup G}
    (hE : CFSG.IsElementaryAbelian 2 E) (hcard : Nat.card E = 8) (hEX : E ≤ X) :
    3 ≤ CFSG.pRank 2 X := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  obtain ⟨hc, hsq⟩ := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).mp hE
  refine CFSG.SectionRank.le_pRank one_lt_two le_top (E := E.subgroupOf X) ⟨?_, ?_⟩ ?_
  · refine ⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩
    have := hc.is_comm.comm ⟨((a : X) : G), a.2⟩ ⟨((b : X) : G), b.2⟩
    change ((a : X) : G) * ((b : X) : G) = ((b : X) : G) * ((a : X) : G)
    exact congrArg Subtype.val this
  · intro a ha
    have h2 : ((a : G)) ^ 2 = 1 := hsq (a : G) ha
    exact Subtype.ext (by rw [Subgroup.coe_pow, h2, Subgroup.coe_one])
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv, hcard]
    norm_num

theorem center_projectiveSL_three_eq_bot (hk : Nat.card k = 4) :
    Subgroup.center (projectiveSL 3 k) = ⊥ := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  refine eq_bot_iff.2 fun z hz => ?_
  obtain ⟨g, rfl⟩ := proj_surjective 3 k z
  have hconj : conjAut 3 k (Matrix.SpecialLinearGroup.toGL g) = 1 := by
    rw [conjAut_toGL]
    ext x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← Subgroup.mem_center_iff.1 hz x, mul_inv_cancel_right]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (K := k) (n := 3) le_rfl
    (Matrix.SpecialLinearGroup.toGL g) 1 (by rw [map_one, mul_one]; exact hconj)
  refine Subgroup.mem_bot.2 (proj_eq_one_iff.2 ⟨c, units_pow_three hk c, ?_⟩)
  have := congrArg (fun A : GL (Fin 3) k => (A : Matrix (Fin 3) (Fin 3) k)) hc
  simp only [GeneralLinearGroup.coe_scalar] at this
  exact this.symm

abbrev innerAutGroup (G : Type*) [Group G] : Subgroup (MulAut G) :=
  (MulAut.conj : G →* MulAut G).range

theorem inr_one_one_mem_center (G : Type*) [CommGroup G] :
    (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (1 : ZMod 2)) :
      G ⋊[inversionAction G] (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∈
        Subgroup.center _ := by
  rw [Subgroup.mem_center_iff]
  intro z
  refine SemidirectProduct.ext ?_ ?_
  · rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.left_inr,
      SemidirectProduct.right_inr, map_one, mul_one, one_mul, inversionAction_apply,
      show (1 + 1 : ZMod 2) = 0 from rfl]
    simp only [↓reduceIte]
  · rw [SemidirectProduct.mul_right, SemidirectProduct.mul_right, mul_comm]

section Rank

variable {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2)
include hσ

omit hσ in
theorem twistF_one_eq (B : GL (Fin 3) k) :
    twistF σ 1 B = GeneralLinearGroup.map (σ : k →+* k) B := by
  simp [twistF]

omit hσ in
theorem twistD_one_eq (B : GL (Fin 3) k) :
    twistD 1 B = GeneralLinearGroup.inverseTranspose B := by
  simp [twistD]

theorem two_dvd_and_not_four_dvd_index (hk : Nat.card k = 4)
    (H : Subgroup (MulAut (projectiveSL 3 k))) (hIH : innerAutGroup (projectiveSL 3 k) ≤ H)
    (hβ : fieldAut 3 k σ * dualAut 3 k ∈ H)
    (hrank : CFSG.pRank 2 ↥(H ⊓ Subgroup.centralizer {fieldAut 3 k σ * dualAut 3 k}) ≤ 2) :
    2 ∣ ((innerAutGroup (projectiveSL 3 k)).subgroupOf H).index ∧
      ¬ 4 ∣ ((innerAutGroup (projectiveSL 3 k)).subgroupOf H).index := by
  classical
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hff := fieldAut_sigma_mul_self hσ hk
  obtain ⟨Ψ, hΨ⟩ := exists_outerHom hσ hk
  have hker := ker_eq_range_conj hσ hk hΨ
  set I := innerAutGroup (projectiveSL 3 k) with hI
  have hidx : (I.subgroupOf H).index = Nat.card (H.map Ψ) := by
    have h1 : I.subgroupOf H = (Ψ.comp H.subtype).ker := by
      rw [← MonoidHom.comap_ker, hker]
      rfl
    rw [h1, Subgroup.index_ker, MonoidHom.range_comp, Subgroup.range_subtype]
  have hβnf : fieldAut 3 k σ * dualAut 3 k = nf σ 1 1 1 := by
    simp [nf, val_one_two]
  have hΨβ : Ψ (fieldAut 3 k σ * dualAut 3 k) =
      ⟨1, (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)⟩ := by
    rw [hβnf, hΨ, map_one]
  have hββ : (fieldAut 3 k σ * dualAut 3 k) * (fieldAut 3 k σ * dualAut 3 k) = 1 := by
    rw [hβnf, nf_mul σ hff, twistD_one, twistF_one, mul_one, zmod_two_add_self, nf_zero_zero,
      map_one]
  refine ⟨?_, fun h4 => ?_⟩
  ·
    rw [hidx]
    have hord : orderOf (Ψ (fieldAut 3 k σ * dualAut 3 k)) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [sq, ← map_mul, hββ, map_one]
      · rw [hΨβ]
        intro h
        have h1 : Multiplicative.ofAdd (1 : ZMod 2) = 1 :=
          congrArg (fun z => (SemidirectProduct.right z).1) h
        exact absurd (ofAdd_eq_one.1 h1) (by decide)
    have hdvd := Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_map_of_mem Ψ hβ)
    rwa [hord] at hdvd
  rw [hidx] at h4
  set Hb := H.map Ψ with hHb
  set r := (SemidirectProduct.rightHom : kˣ ⋊[inversionAction kˣ]
    (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →* _).comp Hb.subtype with hr
  have hcard : Nat.card Hb = Nat.card r.ker * Nat.card r.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hker3 : Nat.card r.ker ∣ 3 := by
    have hle : r.ker.map Hb.subtype ≤ (SemidirectProduct.rightHom : kˣ ⋊[inversionAction kˣ]
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →* _).ker := by
      rintro _ ⟨y, hy, rfl⟩
      exact hy
    have h3 : Nat.card (SemidirectProduct.rightHom : kˣ ⋊[inversionAction kˣ]
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →* _).ker = 3 := by
      rw [← SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.range_eq_map,
        Subgroup.card_map_of_injective SemidirectProduct.inl_injective, Subgroup.card_top,
        card_units_eq_three hk]
    rw [← h3, ← Subgroup.card_map_of_injective Hb.subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  have hrange4 : 4 ∣ Nat.card r.range := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hker3 with h1 | h3
    · rwa [hcard, h1, one_mul] at h4
    · rw [hcard, h3] at h4
      exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h4
  have htop : r.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have hV : Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) = 4 := by
      rw [Nat.card_prod]
      simp
    have hle := Subgroup.card_le_card_group r.range
    have hpos : 0 < Nat.card r.range := Nat.card_pos
    rw [hV] at hle ⊢
    obtain ⟨m, hm⟩ := hrange4
    rcases m with _ | _ | m
    · omega
    · omega
    · omega
  obtain ⟨⟨_, ⟨h, hh, rfl⟩⟩, hy⟩ :=
    (htop ▸ Subgroup.mem_top _ : (Multiplicative.ofAdd (1 : ZMod 2), 1) ∈ r.range)
  obtain ⟨⟨A, a, b⟩, rfl⟩ := exists_nf hσ hk h
  dsimp only at hh hy
  have hy' : (Ψ (nf σ A a b)).right = (Multiplicative.ofAdd (1 : ZMod 2), 1) := hy
  rw [hΨ, Prod.ext_iff] at hy'
  obtain ⟨ha, hb⟩ := hy'
  have ha' : a = 1 := Multiplicative.ofAdd.injective ha
  have hb' : b = 0 := ofAdd_eq_one.1 hb
  subst ha' hb'
  set x := GeneralLinearGroup.det A with hx
  set D : GL (Fin 3) k := diagGL x with hD
  set h₁ := nf σ D 1 0 with hh₁
  set t := nf σ (s23GL : GL (Fin 3) k) 0 0 with ht
  have hDmem : conjAut 3 k (D * A⁻¹) ∈ H := by
    refine hIH ((conjAut_mem_range_conj_iff hk _).2 ?_)
    rw [map_mul, map_inv, det_diagGL, ← hx, mul_inv_cancel]
  have hh₁H : h₁ ∈ H := by
    have e : h₁ = conjAut 3 k (D * A⁻¹) * nf σ A 1 0 := by
      rw [hh₁, ← nf_zero_zero σ, nf_mul σ hff]
      simp [twistF, twistD]
    rw [e]
    exact mul_mem hDmem hh
  have htI : t ∈ I := by
    rw [ht, nf_zero_zero, s23GL, conjAut_toGL]
    exact ⟨_, rfl⟩
  have htH : t ∈ H := hIH htI
  have hΨt : Ψ t = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact htI
  have ht1 : t ≠ 1 := by
    intro h1
    rw [ht, nf_zero_zero] at h1
    obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (K := k) (n := 3) le_rfl
      s23GL 1 (by rw [map_one, mul_one]; exact h1)
    exact s23GL_ne_scalar c hc
  have hDinv :
      GeneralLinearGroup.map (σ : k →+* k) (GeneralLinearGroup.inverseTranspose D) = D := by
    rw [hD, inverseTranspose_diagGL, map_sigma_diagGL hσ hk, inv_inv]
  have hβh₁ : Commute (fieldAut 3 k σ * dualAut 3 k) h₁ := by
    change _ * _ = _ * _
    rw [hβnf, hh₁, nf_mul σ hff, nf_mul σ hff, twistD_one_eq, twistF_one_eq, hDinv,
      twistD_one, twistF_one, one_mul, mul_one, add_comm (1 : ZMod 2) 0]
  have hβt : Commute (fieldAut 3 k σ * dualAut 3 k) t := by
    change _ * _ = _ * _
    rw [hβnf, ht, nf_mul σ hff, nf_mul σ hff, twistD_one_eq, twistF_one_eq,
      inverseTranspose_s23GL, map_s23GL, twistD_one, twistF_one, one_mul, mul_one,
      add_zero, zero_add]
  have hh₁t : Commute h₁ t := by
    change _ * _ = _ * _
    rw [hh₁, ht, nf_mul σ hff, nf_mul σ hff]
    simp only [twistF, twistD, one_ne_zero, ↓reduceIte, map_s23GL, add_zero, zero_add]
    rw [hD, diagGL_mul_s23GL]
  have hh₁h₁ : h₁ * h₁ = 1 := by
    rw [hh₁, nf_mul σ hff]
    simp only [twistF, twistD, one_ne_zero, ↓reduceIte]
    rw [hD, map_sigma_diagGL hσ hk, diagGL_mul, mul_inv_cancel, diagGL_one,
      zmod_two_add_self, add_zero, nf_zero_zero, map_one]
  have htt : t * t = 1 := by
    rw [ht, nf_zero_zero, ← map_mul, s23GL_mul_self, map_one]
  set ρ := (SemidirectProduct.rightHom : kˣ ⋊[inversionAction kˣ]
    (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →* _).comp Ψ with hρ
  have hρβ : ρ (fieldAut 3 k σ * dualAut 3 k) =
      (Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (1 : ZMod 2)) := by
    rw [hρ, MonoidHom.comp_apply, hΨβ]
    rfl
  have hρh₁ : ρ h₁ = (Multiplicative.ofAdd (1 : ZMod 2), 1) := by
    rw [hρ, MonoidHom.comp_apply, hh₁, hΨ]
    rfl
  have hρt : ρ t = 1 := by
    rw [hρ, MonoidHom.comp_apply, hΨt, map_one]
  have hind : ∀ a b c : ZMod 2,
      (fieldAut 3 k σ * dualAut 3 k) ^ a.val * h₁ ^ b.val * t ^ c.val = 1 →
        a = 0 ∧ b = 0 ∧ c = 0 := by
    intro a b c habc
    have hR := congrArg ρ habc
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, hρβ, hρh₁, hρt, one_pow, mul_one,
      map_one ρ] at hR
    have hab := congrArg Prod.fst hR
    have ha := congrArg Prod.snd hR
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.pow_fst, Prod.pow_snd, Prod.fst_one,
      Prod.snd_one, one_pow, mul_one] at hab ha
    rw [ofAdd_one_pow_val, ofAdd_one_pow_val, ← ofAdd_add, ofAdd_eq_one] at hab
    rw [ofAdd_one_pow_val, ofAdd_eq_one] at ha
    subst ha
    rw [zero_add] at hab
    subst hab
    refine ⟨rfl, rfl, ?_⟩
    rcases zmod_two_cases c with rfl | rfl
    · rfl
    · exfalso
      apply ht1
      simpa [val_one_two] using habc
  obtain ⟨E, hEab, hE8, hEle⟩ :=
    exists_elementaryAbelian_eight hβh₁ hβt hh₁t hββ hh₁h₁ htt hind
  have hEK : E ≤ H ⊓ Subgroup.centralizer {fieldAut 3 k σ * dualAut 3 k} := by
    refine hEle _ (Subgroup.mem_inf.2 ⟨hβ, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩)
      (Subgroup.mem_inf.2 ⟨hh₁H, Subgroup.mem_centralizer_singleton_iff.2 hβh₁.eq.symm⟩)
      (Subgroup.mem_inf.2 ⟨htH, Subgroup.mem_centralizer_singleton_iff.2 hβt.eq.symm⟩)
  have h3 := three_le_pRank hEab hE8 hEK
  omega

end Rank

theorem linear_three_four_outer_quotient_rank_two_restriction (k : Type*) [Field k]
    (hk : Nat.card k = 4) (σ : k ≃+* k) (hσ : ∀ a, σ a = a ^ 2) :
    Subgroup.center (projectiveSL 3 k) = ⊥ ∧ Nat.card kˣ = 3 ∧
    (∃ e : MulAut (projectiveSL 3 k) ⧸ innerAutGroup (projectiveSL 3 k) ≃*
        kˣ ⋊[inversionAction kˣ] (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)),
      (∀ A : GL (Fin 3) k,
        e (conjAut 3 k A) = SemidirectProduct.inl (GeneralLinearGroup.det A)) ∧
      e (fieldAut 3 k σ) = SemidirectProduct.inr (Multiplicative.ofAdd 1, 1) ∧
      e (dualAut 3 k) = SemidirectProduct.inr (1, Multiplicative.ofAdd 1)) ∧
    (∀ A : GL (Fin 3) k,
      ((fieldAut 3 k σ * conjAut 3 k A * (fieldAut 3 k σ)⁻¹ : MulAut (projectiveSL 3 k)) :
          MulAut (projectiveSL 3 k) ⧸ innerAutGroup (projectiveSL 3 k)) =
        ((conjAut 3 k A : MulAut (projectiveSL 3 k)) :
          MulAut (projectiveSL 3 k) ⧸ innerAutGroup (projectiveSL 3 k))⁻¹ ∧
      ((dualAut 3 k * conjAut 3 k A * (dualAut 3 k)⁻¹ : MulAut (projectiveSL 3 k)) :
          MulAut (projectiveSL 3 k) ⧸ innerAutGroup (projectiveSL 3 k)) =
        ((conjAut 3 k A : MulAut (projectiveSL 3 k)) :
          MulAut (projectiveSL 3 k) ⧸ innerAutGroup (projectiveSL 3 k))⁻¹) ∧
    ((fieldAut 3 k σ * dualAut 3 k : MulAut (projectiveSL 3 k)) :
        MulAut (projectiveSL 3 k) ⧸ innerAutGroup (projectiveSL 3 k)) =
      ((fieldAut 3 k σ : MulAut (projectiveSL 3 k)) :
        MulAut (projectiveSL 3 k) ⧸ innerAutGroup (projectiveSL 3 k)) *
      ((dualAut 3 k : MulAut (projectiveSL 3 k)) :
        MulAut (projectiveSL 3 k) ⧸ innerAutGroup (projectiveSL 3 k)) ∧
    ((fieldAut 3 k σ * dualAut 3 k : MulAut (projectiveSL 3 k)) :
        MulAut (projectiveSL 3 k) ⧸ innerAutGroup (projectiveSL 3 k)) ∈
      Subgroup.center (MulAut (projectiveSL 3 k) ⧸ innerAutGroup (projectiveSL 3 k)) ∧
    ∀ H : Subgroup (MulAut (projectiveSL 3 k)), innerAutGroup (projectiveSL 3 k) ≤ H →
      fieldAut 3 k σ * dualAut 3 k ∈ H →
      CFSG.pRank 2 ↥(H ⊓ Subgroup.centralizer {fieldAut 3 k σ * dualAut 3 k}) ≤ 2 →
      2 ∣ ((innerAutGroup (projectiveSL 3 k)).subgroupOf H).index ∧
        ¬ 4 ∣ ((innerAutGroup (projectiveSL 3 k)).subgroupOf H).index := by
  obtain ⟨Ψ, hΨ⟩ := exists_outerHom hσ hk
  have hker := ker_eq_range_conj hσ hk hΨ
  have hsurj := surjective_of_nf hΨ
  set I := innerAutGroup (projectiveSL 3 k) with hI
  let e : MulAut (projectiveSL 3 k) ⧸ I ≃* kˣ ⋊[inversionAction kˣ]
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective Ψ hsurj)
  have he : ∀ x : MulAut (projectiveSL 3 k), e (x : MulAut (projectiveSL 3 k) ⧸ I) = Ψ x :=
    fun _ => rfl
  have hc : ∀ A : GL (Fin 3) k, Ψ (conjAut 3 k A) =
      SemidirectProduct.inl (GeneralLinearGroup.det A) := fun A => by
    rw [← nf_zero_zero σ, hΨ]
    rfl
  have hf : Ψ (fieldAut 3 k σ) = SemidirectProduct.inr (Multiplicative.ofAdd 1, 1) := by
    rw [← nf_one_zero σ, hΨ, map_one]
    rfl
  have hd : Ψ (dualAut 3 k) = SemidirectProduct.inr (1, Multiplicative.ofAdd 1) := by
    rw [← nf_zero_one σ, hΨ, map_one]
    rfl
  have hconj : ∀ (v : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) (A : GL (Fin 3) k),
      (SemidirectProduct.inr v * SemidirectProduct.inl (GeneralLinearGroup.det A) *
        (SemidirectProduct.inr v)⁻¹ : kˣ ⋊[inversionAction kˣ]
          (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) =
        SemidirectProduct.inl (inversionAction kˣ v (GeneralLinearGroup.det A)) := by
    intro v A
    rw [SemidirectProduct.inl_aut, map_inv]
  refine ⟨center_projectiveSL_three_eq_bot hk, card_units_eq_three hk,
    ⟨e, fun A => (he _).trans (hc A), (he _).trans hf, (he _).trans hd⟩,
    fun A => ⟨e.injective ?_, e.injective ?_⟩, rfl, ?_,
    fun H hIH hβ hrank => two_dvd_and_not_four_dvd_index hσ hk H hIH hβ hrank⟩
  · rw [map_inv, he, he, map_mul, map_mul, map_inv, hf, hc, hconj,
      show Multiplicative.ofAdd (1 : ZMod 2) = Multiplicative.ofAdd 1 from rfl,
      show ((Multiplicative.ofAdd (1 : ZMod 2), 1) : Multiplicative (ZMod 2) ×
        Multiplicative (ZMod 2)) = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 0) from rfl,
      inversionAction_apply]
    simp
  · rw [map_inv, he, he, map_mul, map_mul, map_inv, hd, hc, hconj,
      show ((1, Multiplicative.ofAdd 1) : Multiplicative (ZMod 2) ×
        Multiplicative (ZMod 2)) = (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1) from rfl,
      inversionAction_apply]
    simp
  · rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    apply e.injective
    rw [map_mul, map_mul, he, he]
    have hβ : Ψ (fieldAut 3 k σ * dualAut 3 k) =
        SemidirectProduct.inr (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1) := by
      rw [map_mul, hf, hd, ← map_mul]
      rfl
    rw [hβ]
    exact (Subgroup.mem_center_iff.1 (inr_one_one_mem_center kˣ) (Ψ x))

end LinearThreeFourOuter

end CFSG.LocalAnalysis.ComponentInitial
