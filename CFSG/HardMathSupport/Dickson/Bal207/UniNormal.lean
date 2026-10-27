module

public import CFSG.HardMathSupport.Dickson.Bal207.UniFrame
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.RankThree.SteinbergR3EUnitaryFieldDescent

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Uni

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.UnitaryDescent
  CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

open CFSG.LieType.Steinberg (exists_conjTr_mul_mul_eq_one)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LieType.Universal.Unitary (conjTr)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

variable {ℓ f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem uni_three_dvd_of_cube {x : ℕ} (h : 3 ∣ x ^ 3 + 1) : 3 ∣ x + 1 := by
  have e : x ^ 3 % 3 = (x % 3) ^ 3 % 3 := Nat.pow_mod x 3 3
  have hx : x % 3 < 3 := Nat.mod_lt x (by norm_num)
  interval_cases hr : x % 3 <;> norm_num at e <;> omega

theorem uni_eq_pow_of_cube {G : Type*} [Group G] [Finite G] [IsCyclic G] {σ τ : G}
    (hσ : orderOf σ = 3) (hτ : τ ^ 3 = 1) : ∃ k : ℕ, τ = σ ^ k := by
  classical
  have := Fintype.ofFinite G
  by_contra hne
  push Not at hne
  have hinj : Set.InjOn (fun k : ℕ => σ ^ k) (Finset.range 3 : Set ℕ) := by
    rw [Finset.coe_range, ← hσ]
    exact pow_injOn_Iio_orderOf
  have hnot : τ ∉ (Finset.range 3).image (fun k : ℕ => σ ^ k) := by
    rw [Finset.mem_image]
    rintro ⟨k, -, hk⟩
    exact hne k hk.symm
  have h2 := IsCyclic.card_pow_eq_one_le (α := G) (n := 3) (by norm_num)
  have hsub : insert τ ((Finset.range 3).image (fun k : ℕ => σ ^ k)) ⊆
      Finset.univ.filter (fun a : G => a ^ 3 = 1) := by
    intro a ha
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact hτ
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 ha
      rw [← pow_mul, mul_comm, pow_mul, ← hσ, pow_orderOf_eq_one, one_pow]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn hinj,
    Finset.card_range] at h1
  have h3 : (Finset.univ.filter (fun a : G => a ^ 3 = 1)).card ≤ 3 := by
    convert h2 using 2
  omega

theorem uni_conj_mul_conj {G : Type*} [Group G] (a x y : G) :
    (a⁻¹ * x * a) * (a⁻¹ * y * a) = a⁻¹ * (x * y) * a := by
  group

theorem uni_conj_pow {G : Type*} [Group G] (a x : G) (k : ℕ) :
    (a⁻¹ * x * a) ^ k = a⁻¹ * x ^ k * a := by
  have := conj_pow (a := a⁻¹) (b := x) (i := k)
  rwa [inv_inv] at this

theorem uni_inr_mul_inl {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N} (g : G) (m : N) :
    (SemidirectProduct.inr g : N ⋊[φ] G) * SemidirectProduct.inl m =
      SemidirectProduct.inl (φ g m) * SemidirectProduct.inr g := by
  rw [SemidirectProduct.inl_aut, map_inv, inv_mul_cancel_right]

abbrev UniGamma (h : UnitaryFieldData ℓ f K) (n : ℕ) : Type :=
  primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⋊[primeFormFieldU h
    isPrimeFormGram_one] (K ≃+* K)

section Gamma

variable (h : UnitaryFieldData ℓ f K)

theorem uniGamma_pow_right (x : UniGamma h n) (k : ℕ) : (x ^ k).right = x.right ^ k :=
  map_pow SemidirectProduct.rightHom x k

theorem uniGamma_pow_left (x : UniGamma h n) (k : ℕ) :
    (((x ^ k).left : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
      GL (Fin n) K) = twistedNorm x.right (x.left : GL (Fin n) K) k := by
  induction k with
  | zero =>
    rw [pow_zero]
    rfl
  | succ k ih =>
    rw [pow_succ, SemidirectProduct.mul_left, Subgroup.coe_mul, ih, coe_primeFormFieldU,
      uniGamma_pow_right, twistedNorm_succ]

end Gamma

theorem uni_exists_fixed_unitary (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {σ : K ≃+* K} (hσ : orderOf σ = p) {A : GL (Fin n) K}
    (hA : A ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hL : twistedNorm σ A p = 1) :
    ∃ M ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      A * glAut σ M = M := by
  classical
  have : Finite K := h.finite
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  obtain ⟨-, hcard, hbar⟩ := fixed_field_facts h hp hp2 σ hσ
  set γ := semilin σ A with hγ
  have hγp : ∀ v, (⇑γ)^[p] v = v := fun v => by
    rw [hγ, iterate_semilin, hL, Units.val_one, Matrix.one_mulVec, hσp]
    rfl
  have h2f : 1 ≤ 2 * f := by have := h.one_le; omega
  obtain ⟨-, -, -, -, bb, hbb, -⟩ := CFSG.RankThree.Classical.semilinear_fixed_basis h.prime h2f
    h.card σ hσ (Module.finrank_fin_fun K) γ (semilin_smul σ _) hγp
  have hfix : ∀ i j, σ (hform h (bb i) (bb j)) = hform h (bb i) (bb j) := fun i j => by
    have := hform_semilin h σ hA (bb i) (bb j)
    rw [← hγ, hbb, hbb] at this
    exact this.symm
  set K₀ := semilinearFixedSubfield σ with hK₀
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : Finite K₀ := Subtype.finite
  have := Fintype.ofFinite K₀
  have : CharP K₀ ℓ := charP_of_card_eq_prime_pow (f := 2 * (f / p)) (by
    rw [← Nat.card_eq_fintype_card, hcard, ← pow_mul, mul_comm])
  set G₀ : Matrix (Fin n) (Fin n) K₀ :=
    Matrix.of fun i j => ⟨hform h (bb i) (bb j), RingHom.mem_eqLocusField.mpr (hfix i j)⟩ with hG₀
  have hσ₀ : ∀ x : K₀, ((unitaryInvolution K₀ ℓ (f / p) x : K₀) : K) = h.bar x := fun x => by
    rw [unitaryInvolution_apply, SubmonoidClass.coe_pow, hbar _ (RingHom.mem_eqLocusField.mp x.2)]
  have hGh : conjTr (unitaryInvolution K₀ ℓ (f / p)) G₀ = G₀ := by
    ext i j
    rw [conjTr, Matrix.transpose_apply, Matrix.map_apply, hσ₀]
    simp only [hG₀, Matrix.of_apply]
    exact bar_hform h _ _
  set Bm : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => bb j i with hBm
  have hBmT : Bm = (Pi.basisFun K (Fin n)).toMatrix bb := by
    ext i j
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rfl
  have hBm_inv : Bm * bb.toMatrix (Pi.basisFun K (Fin n)) = 1 := by
    rw [hBmT, Module.Basis.toMatrix_mul_toMatrix_flip]
  have hdetB : Bm.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hBm_inv
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hGB : G₀.map K₀.subtype = (Bm.map h.bar)ᵀ * Bm := by
    ext i j
    simp only [hG₀, hBm, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
      Matrix.transpose_apply, hform, dotProduct]
    rfl
  have hdet₀ : G₀.det ≠ 0 := by
    intro h0
    have e1 : ((G₀.det : K₀) : K) = (G₀.map K₀.subtype).det := RingHom.map_det K₀.subtype G₀
    have e2 : h.bar Bm.det = (Bm.map h.bar).det := RingHom.map_det h.bar Bm
    rw [h0, ZeroMemClass.coe_zero, hGB, Matrix.det_mul, Matrix.det_transpose, ← e2] at e1
    exact mul_ne_zero ((map_ne_zero h.bar).mpr hdetB) hdetB e1.symm
  obtain ⟨P, hP⟩ := exists_conjTr_mul_mul_eq_one (p := ℓ) (f := f / p) hcard hGh hdet₀
  set PK : Matrix (Fin n) (Fin n) K := (P : Matrix (Fin n) (Fin n) K₀).map K₀.subtype with hPK
  set Mm : Matrix (Fin n) (Fin n) K := Bm * PK with hMm
  have hPKbar : PK.map h.bar = ((P : Matrix (Fin n) (Fin n) K₀).map
      (unitaryInvolution K₀ ℓ (f / p))).map K₀.subtype := by
    ext i j
    simp only [hPK, Matrix.map_apply]
    exact (hσ₀ _).symm
  have hMU : (Mm.map h.bar)ᵀ * Mm = 1 := by
    have e := congrArg (fun X => X.map K₀.subtype) hP
    simp only [conjTr, Matrix.map_mul, Matrix.transpose_map, Matrix.map_one _ (map_zero _)
      (map_one _)] at e
    rw [hMm, Matrix.map_mul, Matrix.transpose_mul, hPKbar, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Bm.map h.bar)ᵀ, ← hGB, ← Matrix.mul_assoc, hPK]
    exact e
  set Mg : GL (Fin n) K := ⟨Mm, (Mm.map h.bar)ᵀ, mul_eq_one_comm.mp hMU, hMU⟩ with hMg
  have hMgU : Mg ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one]
    exact hMU
  have hcol : ∀ j, (fun i => Mm i j) = ∑ k, ((P k j : K₀) : K) • bb k := fun j => by
    funext i
    simp only [hMm, hBm, hPK, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hγcol : ∀ j, γ (fun i => Mm i j) = fun i => Mm i j := fun j => by
    rw [hcol, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hPkj : σ ((P k j : K₀) : K) = (P k j : K₀) := RingHom.mem_eqLocusField.mp (P k j).2
    rw [hγ, semilin_smul, ← hγ, hbb, hPkj]
  have hfixM : A * glAut σ Mg = Mg := by
    apply Units.ext
    rw [Units.val_mul, coe_glAut]
    ext i j
    have := congrFun (hγcol j) i
    rw [hγ, semilin_apply] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, hMg] using this
  exact ⟨Mg, hMgU, hfixM⟩

section Subfield

variable (h : UnitaryFieldData ℓ f K) {e : ℕ} {k : Subfield K} (h₀ : UnitaryFieldData ℓ e k)
  (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) (n : ℕ)

include hbar in
theorem uni_subfieldGL_mem_unitary {g : GL (Fin n) k}
    (hg : g ∈ primeFormUnitary h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) :
    subfieldGL k n g ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have h1 := mem_primeFormUnitary.1 hg
  rw [Units.val_one, Matrix.mul_one] at h1
  rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one, coe_subfieldGL,
    map_subtype_map_bar h h₀ hbar, ← transpose_map, ← Matrix.map_mul, h1,
    Matrix.map_one _ (map_zero _) (map_one _)]

include hbar in
theorem uni_mem_unitary_of_subfieldGL {g₀ : GL (Fin n) k}
    (hg : subfieldGL k n g₀ ∈
      primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    g₀ ∈ primeFormUnitary h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  have h1 := mem_primeFormUnitary.1 hg
  rw [Units.val_one, Matrix.mul_one, coe_subfieldGL, map_subtype_map_bar h h₀ hbar,
    ← transpose_map, ← Matrix.map_mul] at h1
  rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one]
  refine Matrix.map_injective (f := (k.subtype : k → K)) Subtype.val_injective ?_
  change (((g₀ : Matrix (Fin n) (Fin n) k).map h₀.bar)ᵀ * g₀).map k.subtype =
    (1 : Matrix (Fin n) (Fin n) k).map k.subtype
  rw [h1, Matrix.map_one _ (map_zero _) (map_one _)]

end Subfield

theorem uni_pow_apply_fix {σ : K ≃+* K} (c : CFSG.LieType.Chevalley.fixSubfield σ) (k : ℕ) :
    (σ ^ k) (c : K) = c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, RingAut.mul_apply, (CFSG.LieType.Chevalley.mem_fixSubfield σ).1 c.2, ih]

theorem uni_glAut_pow_subfieldGL {σ : K ≃+* K}
    (g₀ : GL (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) (k : ℕ) :
    glAut (σ ^ k) (subfieldGL (CFSG.LieType.Chevalley.fixSubfield σ) n g₀) =
      subfieldGL (CFSG.LieType.Chevalley.fixSubfield σ) n g₀ := by
  apply Units.ext
  rw [coe_glAut, coe_subfieldGL]
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply]
  exact uni_pow_apply_fix _ k

section NormalForm

variable (h : UnitaryFieldData ℓ f K) (h3 : 3 ∣ ℓ ^ f + 1) (Ω : Set (UniGamma h n))
  (hΩc : ∀ x ∈ Ω, ∀ y ∈ Ω, x * y = y * x) (hΩ3 : ∀ x ∈ Ω, x ^ 3 = 1)

include h3 hΩc hΩ3 in
theorem uni_normal_form_linear (hI : ∀ x ∈ Ω, x.right = 1) :
    ∃ (P : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (σ : K ≃+* K),
      σ ^ 3 = 1 ∧ ∀ x ∈ Ω, ∃ D : primeFormUnitary h ((1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K), ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag ∧
          D ^ 3 = 1 ∧ ∃ k : ℕ, (SemidirectProduct.inl P)⁻¹ * x * SemidirectProduct.inl P =
            SemidirectProduct.inl D * SemidirectProduct.inr (σ ^ k) := by
  classical
  have hx : ∀ x ∈ Ω, x = SemidirectProduct.inl x.left := fun x hx => by
    calc x = SemidirectProduct.inl x.left * SemidirectProduct.inr x.right :=
          (SemidirectProduct.inl_left_mul_inr_right x).symm
      _ = SemidirectProduct.inl x.left := by rw [hI x hx, map_one, mul_one]
  have hcube : ∀ x ∈ Ω, x.left ^ 3 = 1 := fun x hxΩ => by
    have h1 := hΩ3 x hxΩ
    rw [hx x hxΩ, ← map_pow] at h1
    exact SemidirectProduct.inl_injective (h1.trans (map_one _).symm)
  obtain ⟨P, hP, hPd⟩ := exists_unitary_isDiag_conj h h3
    ((fun x : UniGamma h n => ((x.left : primeFormUnitary h _) : GL (Fin n) K)) '' Ω)
    (by rintro _ ⟨x, -, rfl⟩; exact x.left.2)
    (by
      rintro _ ⟨x, hxΩ, rfl⟩ _ ⟨y, hyΩ, rfl⟩
      have e := congrArg (fun z : UniGamma h n =>
        ((z.left : primeFormUnitary h _) : GL (Fin n) K)) (hΩc x hxΩ y hyΩ)
      simp only [SemidirectProduct.mul_left, hI x hxΩ, hI y hyΩ, map_one, MulAut.one_apply,
        Subgroup.coe_mul] at e
      exact e)
    (by
      rintro _ ⟨x, hxΩ, rfl⟩
      rw [← Subgroup.coe_pow, hcube x hxΩ, Subgroup.coe_one])
  refine ⟨⟨P, hP⟩, 1, one_pow 3, fun x hxΩ => ?_⟩
  refine ⟨⟨P, hP⟩⁻¹ * x.left * ⟨P, hP⟩, ?_, ?_, 0, ?_⟩
  · have hd := hPd ((x.left : primeFormUnitary h _) : GL (Fin n) K) ⟨x, hxΩ, rfl⟩
    have e : ((((⟨P, hP⟩ : primeFormUnitary h _)⁻¹ * x.left * ⟨P, hP⟩ :
        primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) =
        ((P⁻¹ * ((x.left : primeFormUnitary h _) : GL (Fin n) K) * P : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) := rfl
    rw [e]
    exact hd
  · rw [uni_conj_pow, hcube x hxΩ, mul_one, inv_mul_cancel]
  · conv_lhs => rw [hx x hxΩ]
    rw [pow_zero, map_one, mul_one, ← map_inv, ← map_mul, ← map_mul]

include h3 hΩc hΩ3 in
theorem uni_normal_form_field {x₀ : UniGamma h n} (hx₀ : x₀ ∈ Ω) (hσ1 : x₀.right ≠ 1) :
    ∃ (P : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (σ : K ≃+* K),
      σ ^ 3 = 1 ∧ ∀ x ∈ Ω, ∃ D : primeFormUnitary h ((1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K), ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag ∧
          D ^ 3 = 1 ∧ ∃ k : ℕ, (SemidirectProduct.inl P)⁻¹ * x * SemidirectProduct.inl P =
            SemidirectProduct.inl D * SemidirectProduct.inr (σ ^ k) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite K := h.finite
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  have : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hright3 : ∀ x ∈ Ω, x.right ^ 3 = 1 := fun x hx => by
    rw [← uniGamma_pow_right, hΩ3 x hx]
    rfl
  obtain ⟨σ, hσdef⟩ : ∃ σ : K ≃+* K, x₀.right = σ := ⟨_, rfl⟩
  have hσ3 : σ ^ 3 = 1 := hσdef ▸ hright3 x₀ hx₀
  have hσo : orderOf σ = 3 := orderOf_eq_prime hσ3 (hσdef ▸ hσ1)
  have hL : twistedNorm σ ((x₀.left : primeFormUnitary h _) : GL (Fin n) K) 3 = 1 := by
    have e := uniGamma_pow_left h x₀ 3
    rw [hσdef, hΩ3 x₀ hx₀] at e
    exact e.symm
  obtain ⟨M, hMU, hM⟩ := uni_exists_fixed_unitary h Nat.prime_three (by norm_num) hσo
    x₀.left.2 hL
  obtain ⟨Mu, hMu⟩ : ∃ Mu : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      (Mu : GL (Fin n) K) = M := ⟨⟨M, hMU⟩, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : UniGamma h n → UniGamma h n, ∀ x,
      c x = (SemidirectProduct.inl Mu)⁻¹ * x * SemidirectProduct.inl Mu := ⟨_, fun _ => rfl⟩
  have hdec : ∀ x, c x = SemidirectProduct.inl (c x).left * SemidirectProduct.inr (c x).right :=
    fun x => (SemidirectProduct.inl_left_mul_inr_right _).symm
  have hcr : ∀ x, (c x).right = x.right := fun x => by
    rw [hc]
    simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
      SemidirectProduct.right_inl, inv_one, one_mul, mul_one]
  have hφM : x₀.left * primeFormFieldU h isPrimeFormGram_one σ Mu = Mu := Subtype.ext (by
    rw [Subgroup.coe_mul, coe_primeFormFieldU, hMu]
    exact hM)
  have hc₀ : c x₀ = SemidirectProduct.inr σ := by
    rw [hc, mul_assoc, inv_mul_eq_iff_eq_mul]
    calc x₀ * SemidirectProduct.inl Mu = SemidirectProduct.inl x₀.left *
          (SemidirectProduct.inr σ * SemidirectProduct.inl Mu) := by
          rw [← mul_assoc, ← hσdef, SemidirectProduct.inl_left_mul_inr_right]
      _ = SemidirectProduct.inl x₀.left *
          (SemidirectProduct.inl (primeFormFieldU h isPrimeFormGram_one σ Mu) *
            SemidirectProduct.inr σ) := by rw [uni_inr_mul_inl]
      _ = SemidirectProduct.inl Mu * SemidirectProduct.inr σ := by
          rw [← mul_assoc, ← map_mul, hφM]
  have hcc : ∀ x ∈ Ω, ∀ y ∈ Ω, c x * c y = c y * c x := fun x hx y hy => by
    rw [hc, hc, uni_conj_mul_conj, uni_conj_mul_conj, hΩc x hx y hy]
  have hdata : ∀ x ∈ Ω, ∃ k : ℕ, (c x).right = σ ^ k := fun x hx => by
    rw [hcr]
    exact uni_eq_pow_of_cube hσo (hright3 x hx)
  have hfixY : ∀ x ∈ Ω, primeFormFieldU h isPrimeFormGram_one σ (c x).left = (c x).left := by
    intro x hx
    obtain ⟨k, hk⟩ := hdata x hx
    have hcomm := hcc x hx x₀ hx₀
    rw [hc₀, hdec x, hk] at hcomm
    have e1 : (SemidirectProduct.inr (σ ^ k) : UniGamma h n) * SemidirectProduct.inr σ =
        SemidirectProduct.inr σ * SemidirectProduct.inr (σ ^ k) := by
      rw [← map_mul, ← map_mul, ← pow_succ, ← pow_succ']
    have e2 : SemidirectProduct.inl (c x).left * (SemidirectProduct.inr σ *
        SemidirectProduct.inr (σ ^ k)) =
        SemidirectProduct.inl (primeFormFieldU h isPrimeFormGram_one σ (c x).left) *
          (SemidirectProduct.inr σ * SemidirectProduct.inr (σ ^ k) : UniGamma h n) := by
      calc _ = SemidirectProduct.inl (c x).left * SemidirectProduct.inr (σ ^ k) *
            SemidirectProduct.inr σ := by rw [mul_assoc, e1]
        _ = SemidirectProduct.inr σ * (SemidirectProduct.inl (c x).left *
            SemidirectProduct.inr (σ ^ k)) := hcomm
        _ = _ := by rw [← mul_assoc, uni_inr_mul_inl, mul_assoc]
    exact (SemidirectProduct.inl_injective (mul_right_cancel e2)).symm
  have hfixYk : ∀ x ∈ Ω, ∀ k : ℕ,
      primeFormFieldU h isPrimeFormGram_one (σ ^ k) (c x).left = (c x).left := by
    intro x hx k
    induction k with
    | zero =>
      rw [pow_zero, map_one]
      rfl
    | succ k ih => rw [pow_succ, map_mul, MulAut.mul_apply, hfixY x hx, ih]
  have hY3 : ∀ x ∈ Ω, (c x).left ^ 3 = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hdata x hx
    have hcom : Commute (SemidirectProduct.inl (c x).left : UniGamma h n)
        (SemidirectProduct.inr (σ ^ k)) := by
      show _ * _ = _ * _
      rw [uni_inr_mul_inl, hfixYk x hx k]
    have h1 : c x ^ 3 = 1 := by
      rw [hc, uni_conj_pow, hΩ3 x hx, mul_one, inv_mul_cancel]
    rw [hdec x, hk, hcom.mul_pow, ← map_pow, ← map_pow, ← pow_mul, mul_comm k 3, pow_mul, hσ3,
      one_pow, map_one, mul_one] at h1
    exact SemidirectProduct.inl_injective (h1.trans (map_one _).symm)
  have hYc : ∀ x ∈ Ω, ∀ y ∈ Ω, (c x).left * (c y).left = (c y).left * (c x).left := by
    intro x hx y hy
    obtain ⟨k, hk⟩ := hdata x hx
    obtain ⟨m, hm⟩ := hdata y hy
    have e := congrArg SemidirectProduct.left (hcc x hx y hy)
    simp only [SemidirectProduct.mul_left] at e
    rw [hk, hm, hfixYk y hy, hfixYk x hx] at e
    exact e
  have hY0 : ∀ x ∈ Ω, ∃ g₀ : GL (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ),
      subfieldGL _ n g₀ = ((c x).left : GL (Fin n) K) := by
    intro x hx
    have e := congrArg Subtype.val (hfixY x hx)
    rw [coe_primeFormFieldU] at e
    exact exists_subfieldGL_eq_of_fixed n e
  have hbar := fixSubfield_unitaryFieldData_bar h Nat.prime_three (by norm_num) hσo
  have h3f : 3 ∣ f := (dvd_and_card_fixSubfield_unitary h Nat.prime_three (by norm_num) hσo).1
  have h3₀ : 3 ∣ ℓ ^ (f / 3) + 1 := by
    apply uni_three_dvd_of_cube
    rw [← pow_mul, Nat.div_mul_cancel h3f]
    exact h3
  obtain ⟨P₀, hP₀, hP₀d⟩ := exists_unitary_isDiag_conj
    (fixSubfield_unitaryFieldData h Nat.prime_three (by norm_num) hσo) h3₀
    {g₀ | ∃ x ∈ Ω, subfieldGL _ n g₀ = ((c x).left : GL (Fin n) K)}
    (by
      rintro g₀ ⟨x, -, hg₀⟩
      refine uni_mem_unitary_of_subfieldGL h _ hbar n ?_
      rw [hg₀]
      exact (c x).left.2)
    (by
      rintro g₀ ⟨x, hx, hg₀⟩ g₁ ⟨y, hy, hg₁⟩
      apply subfieldGL_injective _ n
      rw [map_mul, map_mul, hg₀, hg₁]
      exact congrArg Subtype.val (hYc x hx y hy))
    (by
      rintro g₀ ⟨x, hx, hg₀⟩
      apply subfieldGL_injective _ n
      rw [map_pow, hg₀, map_one, ← Subgroup.coe_pow, hY3 x hx, Subgroup.coe_one])
  have hPU := uni_subfieldGL_mem_unitary h _ hbar n hP₀
  obtain ⟨Pu, hPu⟩ : ∃ Pu : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      (Pu : GL (Fin n) K) = subfieldGL _ n P₀ := ⟨⟨_, hPU⟩, rfl⟩
  have hφP : ∀ k : ℕ, primeFormFieldU h isPrimeFormGram_one (σ ^ k) Pu = Pu := fun k =>
    Subtype.ext (by rw [coe_primeFormFieldU, hPu, uni_glAut_pow_subfieldGL])
  refine ⟨Mu * Pu, σ, hσ3, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hdata x hx
  obtain ⟨g₀, hg₀⟩ := hY0 x hx
  refine ⟨Pu⁻¹ * (c x).left * Pu, ?_, ?_, k, ?_⟩
  · have hd := hP₀d g₀ ⟨x, hx, hg₀⟩
    have e : ((Pu⁻¹ * (c x).left * Pu : primeFormUnitary h _) : GL (Fin n) K) =
        subfieldGL _ n (P₀⁻¹ * g₀ * P₀) := by
      rw [map_mul, map_mul, map_inv, hg₀, ← hPu]
      rfl
    rw [e, coe_subfieldGL]
    exact hd.map rfl
  · rw [uni_conj_pow, hY3 x hx, mul_one, inv_mul_cancel]
  · have e3 : (SemidirectProduct.inr (σ ^ k) : UniGamma h n) * SemidirectProduct.inl Pu =
        SemidirectProduct.inl Pu * SemidirectProduct.inr (σ ^ k) := by
      rw [uni_inr_mul_inl, hφP k]
    calc (SemidirectProduct.inl (Mu * Pu))⁻¹ * x * SemidirectProduct.inl (Mu * Pu)
        = (SemidirectProduct.inl Pu)⁻¹ * c x * SemidirectProduct.inl Pu := by
          rw [hc, map_mul]
          group
      _ = (SemidirectProduct.inl Pu)⁻¹ * SemidirectProduct.inl (c x).left *
          (SemidirectProduct.inr (σ ^ k) * SemidirectProduct.inl Pu) := by
          conv_lhs => rw [hdec x, hk]
          group
      _ = _ := by
          rw [e3, map_mul, map_mul, map_inv]
          group

end NormalForm

theorem uni_normal_form_mat (h : UnitaryFieldData ℓ f K) (h3 : 3 ∣ ℓ ^ f + 1)
    (Ω : Set (UniGamma h n)) (hΩc : ∀ x ∈ Ω, ∀ y ∈ Ω, x * y = y * x)
    (hΩ3 : ∀ x ∈ Ω, x ^ 3 = 1) :
    ∃ (P : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (σ : K ≃+* K),
      σ ^ 3 = 1 ∧ ∀ x ∈ Ω, ∃ D : primeFormUnitary h ((1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K), ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag ∧
          D ^ 3 = 1 ∧ ∃ k : ℕ, (SemidirectProduct.inl P)⁻¹ * x * SemidirectProduct.inl P =
            SemidirectProduct.inl D * SemidirectProduct.inr (σ ^ k) := by
  by_cases hI : ∀ x ∈ Ω, x.right = 1
  · exact uni_normal_form_linear h h3 Ω hΩc hΩ3 hI
  · push Not at hI
    obtain ⟨x₀, hx₀, hσ1⟩ := hI
    exact uni_normal_form_field h h3 Ω hΩc hΩ3 hx₀ hσ1

end CFSG.HardMathSupport.Dickson.Bal207.Uni

end
