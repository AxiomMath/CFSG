module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.AutNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Transport

@[expose] def miyamotoBarEquiv : K ≃+* K where
  toFun := h.bar
  invFun := h.bar
  left_inv := h.bar_bar
  right_inv := h.bar_bar
  map_mul' := map_mul h.bar
  map_add' := map_add h.bar

@[simp] theorem miyamotoBarEquiv_apply (c : K) : miyamotoBarEquiv h c = h.bar c :=
  rfl

theorem miyamotoFieldFactor_eq_bar {α : MulAut (gramSU h (miyamotoJ4 K))} (hα : orderOf α = 2)
    (hσ : miyamotoFieldFactor h α ≠ 1) : miyamotoFieldFactor h α = miyamotoBarEquiv h := by
  have h2 : miyamotoFieldFactor h α * miyamotoFieldFactor h α = 1 := by
    have e := pow_orderOf_eq_one α
    rw [hα] at e
    rw [← map_mul, ← sq, e, map_one]
  rcases ringEquiv_eq_refl_or_bar h h2 with h1 | h1
  · exact absurd h1 hσ
  · exact RingEquiv.ext h1

theorem coe_apply_of_congr_eq_psi {α : MulAut (gramSU h (miyamotoJ4 K))}
    {A : primeFormUnitary h (miyamotoJ4 K)} {φ : K ≃+* K}
    (hα : MulAut.congr (miyamotoProjEquiv h) α =
      primeFormPsi h (C := miyamotoJ4GL K) (isPrimeFormGram_miyamotoJ4GL (K := K)) ⟨A, φ⟩)
    (g : gramSU h (miyamotoJ4 K)) :
    ((α g : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) =
      A * glAut φ (g : GL (Fin 4) K) * (A : GL (Fin 4) K)⁻¹ := by
  have e1 : ((α g : gramSU h (miyamotoJ4 K)) : primeFormP h (miyamotoJ4 K)) =
      MulAut.congr (miyamotoProjEquiv h) α (g : primeFormP h (miyamotoJ4 K)) := by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      miyamotoProjEquiv_symm_mk, miyamotoProjEquiv_apply]
  rw [hα, primeFormPsi_apply, MulAut.mul_apply] at e1
  change _ = primeFormConjHom h (miyamotoJ4 K) A (primeFormFieldAut h
    (isPrimeFormGram_miyamotoJ4GL (K := K)) φ (g : primeFormP h _)) at e1
  rw [primeFormFieldAut_mk, primeFormConjHom_mk] at e1
  exact congrArg Subtype.val (mk_injective_miyamoto h e1)

theorem mul_map_bar_eq_of_mulVec {A H : GL (Fin 4) K}
    (hv : ∀ v : Fin 4 → K, ((H⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
      ((A : Matrix (Fin 4) (Fin 4) K) *ᵥ fun i => h.bar (((H : Matrix (Fin 4) (Fin 4) K) *ᵥ v) i)) =
        fun i => h.bar (v i)) :
    (A : Matrix (Fin 4) (Fin 4) K) * (H : Matrix (Fin 4) (Fin 4) K).map h.bar = H := by
  have hbb := h.bar_bar
  have hHH : (H : Matrix (Fin 4) (Fin 4) K) * ((H⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine Matrix.ext_of_mulVec_single fun j => ?_
  set v : Fin 4 → K := fun i => h.bar ((Pi.single j (1 : K) : Fin 4 → K) i) with hvdef
  have hbv : (fun i => h.bar (v i)) = (Pi.single j (1 : K) : Fin 4 → K) := by
    funext i
    rw [hvdef, hbb]
  have hbar : (fun i => h.bar (((H : Matrix (Fin 4) (Fin 4) K) *ᵥ v) i)) =
      (H : Matrix (Fin 4) (Fin 4) K).map h.bar *ᵥ Pi.single j 1 := by
    funext i
    rw [RingHom.map_mulVec, ← hbv]
    rfl
  have e := congrArg (fun w => (H : Matrix (Fin 4) (Fin 4) K) *ᵥ w) (hv v)
  simp only [hbar, hbv] at e
  rw [mulVec_mulVec, hHH, one_mulVec, mulVec_mulVec] at e
  exact e

end Transport

section Conjugacy

theorem exists_conj_of_same_gram {A A' H H' : GL (Fin 4) K} {C₀ : Matrix (Fin 4) (Fin 4) K}
    {φ : K ≃+* K} (hφ : ∀ x, φ x = h.bar x)
    (hA : (A : Matrix (Fin 4) (Fin 4) K) * (H : Matrix (Fin 4) (Fin 4) K).map h.bar = H)
    (hA' : (A' : Matrix (Fin 4) (Fin 4) K) * (H' : Matrix (Fin 4) (Fin 4) K).map h.bar = H')
    (hH : ((H : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * miyamotoJ4 K * H = C₀)
    (hH' : ((H' : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * miyamotoJ4 K * H' = C₀) :
    ∃ t : gramSU h (miyamotoJ4 K), ∀ g : GL (Fin 4) K,
      A' * glAut φ g * A'⁻¹ = (t : GL (Fin 4) K) *
        (A * glAut φ ((t : GL (Fin 4) K)⁻¹ * g * (t : GL (Fin 4) K)) * A⁻¹) *
          (t : GL (Fin 4) K)⁻¹ := by
  have hmap : ∀ M : Matrix (Fin 4) (Fin 4) K, M.map φ = M.map h.bar := fun M =>
    Matrix.ext fun i j => hφ _
  have hAφ : A * glAut φ H = H := Units.ext (by rw [Units.val_mul, coe_glAut, hmap, hA])
  have hA'φ : A' * glAut φ H' = H' := Units.ext (by rw [Units.val_mul, coe_glAut, hmap, hA'])
  set B := H' * H⁻¹ with hB
  have hBU : B ∈ primeFormUnitary h (miyamotoJ4 K) := by
    rw [mem_primeFormUnitary, hB, Units.val_mul, conjTranspose_mul_mul, hH', ← hH,
      ← conjTranspose_mul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one, Matrix.one_mul,
      Matrix.mul_one]
  obtain ⟨t, ht⟩ := exists_mem_gramSU_conj_eq h hBU
  have ht' : ∀ g : GL (Fin 4) K,
      B⁻¹ * g * B = (t : GL (Fin 4) K)⁻¹ * g * (t : GL (Fin 4) K) := by
    intro g
    have e := ht ((t : GL (Fin 4) K)⁻¹ * g * (t : GL (Fin 4) K))
    rw [show (t : GL (Fin 4) K) * ((t : GL (Fin 4) K)⁻¹ * g * (t : GL (Fin 4) K)) *
      (t : GL (Fin 4) K)⁻¹ = g by group] at e
    conv_lhs => rw [← e]
    group
  have hA'eq : A' = B * A * glAut φ B⁻¹ := by
    have e1 : A' = H' * (glAut φ H')⁻¹ := eq_mul_inv_iff_mul_eq.mpr hA'φ
    have e2 : A = H * (glAut φ H)⁻¹ := eq_mul_inv_iff_mul_eq.mpr hAφ
    rw [e1, e2, hB, map_inv, map_mul, map_inv]
    group
  refine ⟨t, fun g => ?_⟩
  rw [hA'eq, ← ht, ← ht' g]
  simp only [map_mul, map_inv]
  group

@[expose] def miyamotoPi (K : Type) [Field K] : GL (Fin 4) K where
  val := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  inv := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem miyamotoPi_descent :
    ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((miyamotoPi K : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar = miyamotoPi K ∧
      (((miyamotoPi K : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * miyamotoJ4 K *
        (miyamotoPi K : Matrix (Fin 4) (Fin 4) K) = blockSwapJ 4 2 := by
  refine ⟨?_, ?_⟩
  · rw [Units.val_one, Matrix.one_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [miyamotoPi]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [miyamotoPi, miyamotoJ4, blockSwapJ, Matrix.mul_apply, Fin.sum_univ_four]

theorem exists_add_bar_eq_one : ∃ ω : K, ω + h.bar ω = 1 := by
  have : CharP K 2 := h.charP
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have hc0 : c + h.bar c ≠ 0 := add_bar_ne_zero h hc
  refine ⟨c / (c + h.bar c), ?_⟩
  rw [map_div₀, map_add, h.bar_bar, add_comm (h.bar c) c, ← add_div, div_self hc0]

@[expose] def miyamotoH1Mat (ω : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 1, 1, 1; 0, 1, 0, 1; 0, 0, 1, 1; ω, ω + 1, ω + 1, h.bar ω]

theorem miyamotoH1Mat_gram {ω : K} (hω : ω + h.bar ω = 1) :
    ((miyamotoH1Mat h ω).map h.bar)ᵀ * miyamotoJ4 K * miyamotoH1Mat h ω = 1 := by
  have : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hb : h.bar ω = 1 + ω := by linear_combination hω - ω * h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [miyamotoH1Mat, miyamotoJ4, Matrix.mul_apply, Fin.sum_univ_four, hb] <;>
    ring_nf <;> simp [h2] <;> first | linear_combination h2 | linear_combination 2 * h2

theorem det_miyamotoH1Mat_ne_zero {ω : K} (hω : ω + h.bar ω = 1) :
    (miyamotoH1Mat h ω).det ≠ 0 := by
  intro e
  have := congrArg Matrix.det (miyamotoH1Mat_gram h hω)
  rw [det_mul, e, mul_zero, det_one] at this
  exact zero_ne_one this

@[expose] def miyamotoH1 {ω : K} (hω : ω + h.bar ω = 1) : GL (Fin 4) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (miyamotoH1Mat h ω) (det_miyamotoH1Mat_ne_zero h hω)

@[expose] def miyamotoZ1S : gramSU h (miyamotoJ4 K) :=
  ⟨miyamotoXGL h 0 0 0 1, miyamotoUnipotent_le_SU h true true (by
    have : CharP K 2 := h.charP
    exact (miyamotoXGL_mem_Z2 h).mpr ⟨rfl, rfl, map_one _⟩)⟩

theorem miyamotoZ1S_mem_A1 : ((miyamotoZ1S h : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) ∈
    miyamotoA1 h := by
  have : CharP K 2 := h.charP
  exact (miyamotoXGL_mem_A1 h).mpr ⟨rfl, map_zero _, map_one _⟩

theorem miyamotoH1_descent {ω : K} (hω : ω + h.bar ω = 1) :
    (((miyamotoZ1S h : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((miyamotoH1 h hω : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar = miyamotoH1 h hω ∧
      (((miyamotoH1 h hω : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * miyamotoJ4 K *
        (miyamotoH1 h hω : Matrix (Fin 4) (Fin 4) K) = 1 := by
  have : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hb : h.bar ω = 1 + ω := by linear_combination hω - ω * h2
  refine ⟨?_, miyamotoH1Mat_gram h hω⟩
  change miyamotoX h 0 0 0 1 * (miyamotoH1Mat h ω).map h.bar = miyamotoH1Mat h ω
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [miyamotoX, miyamotoH1Mat, Matrix.mul_apply, Fin.sum_univ_four, hb] <;>
    ring_nf <;> simp [h2] <;> linear_combination h2

end Conjugacy

section Classes

theorem exists_conj_eq_u_or_uz1 {α : MulAut (gramSU h (miyamotoJ4 K))} (hα : orderOf α = 2)
    (hσ : miyamotoFieldFactor h α ≠ 1) :
    ∃ t : gramSU h (miyamotoJ4 K),
      MulAut.conj t * α * (MulAut.conj t)⁻¹ = miyamotoFieldAut h (miyamotoBarEquiv h) ∨
        MulAut.conj t * α * (MulAut.conj t)⁻¹ =
          MulAut.conj (miyamotoZ1S h) * miyamotoFieldAut h (miyamotoBarEquiv h) := by
  set hC := isPrimeFormGram_miyamotoJ4GL (K := K)
  have hn : 3 ≤ 4 := by norm_num
  have hq : ¬(4 = 3 ∧ 2 ^ f = 2) := fun e => absurd e.1 (by norm_num)
  have hσbar := miyamotoFieldFactor_eq_bar h hα hσ
  set α' := MulAut.congr (miyamotoProjEquiv h) α with hα'def
  have hα' : orderOf α' = 2 := by rw [hα'def, MulEquiv.orderOf_eq, hα]
  have hφ' : primeFormFieldFactor h hC hn hq α' = miyamotoBarEquiv h := by
    rw [← hσbar, miyamotoFieldFactor_apply]
  obtain ⟨A, H, C₀, -, hcase, hαA, -, hHg, hv, -⟩ :=
    even_unitary_antiunitary_involution_descent h hC hn hq α' hα'
      (fun x => by rw [hφ']; rfl)
  rw [hφ'] at hαA
  have hαg := coe_apply_of_congr_eq_psi h hαA
  have hAH := mul_map_bar_eq_of_mulVec h hv
  have hφ : ∀ x, miyamotoBarEquiv h x = h.bar x := fun x => rfl
  have key : ∀ (A' H' : GL (Fin 4) K),
      (A' : Matrix (Fin 4) (Fin 4) K) * (H' : Matrix (Fin 4) (Fin 4) K).map h.bar = H' →
      ((H' : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * miyamotoJ4 K * H' = C₀ →
      ∀ β : MulAut (gramSU h (miyamotoJ4 K)),
        (∀ g : gramSU h (miyamotoJ4 K), ((β g : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) =
          A' * glAut (miyamotoBarEquiv h) (g : GL (Fin 4) K) * A'⁻¹) →
      ∃ t : gramSU h (miyamotoJ4 K), MulAut.conj t * α * (MulAut.conj t)⁻¹ = β := by
    intro A' H' hA'H' hH' β hβ
    obtain ⟨t, ht⟩ := exists_conj_of_same_gram h hφ hAH hA'H' hHg hH'
    refine ⟨t, MulEquiv.ext fun g => Subtype.ext ?_⟩
    rw [hβ, ht, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, ← map_inv,
      MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hαg,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  rcases hcase with hC0 | ⟨r, hr, hC0⟩
  ·
    obtain ⟨ω, hω⟩ := exists_add_bar_eq_one h
    obtain ⟨hd1, hd2⟩ := miyamotoH1_descent h hω
    obtain ⟨t, ht⟩ := key _ _ hd1 (by rw [hd2, hC0])
      (MulAut.conj (miyamotoZ1S h) * miyamotoFieldAut h (miyamotoBarEquiv h)) fun g => by
        rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
          Subgroup.coe_inv, coe_miyamotoFieldAut_apply]
    exact ⟨t, Or.inr ht⟩
  ·
    obtain rfl : r = 2 := by omega
    obtain ⟨hd1, hd2⟩ := miyamotoPi_descent h
    obtain ⟨t, ht⟩ := key _ _ hd1 (by rw [hd2, hC0])
      (miyamotoFieldAut h (miyamotoBarEquiv h)) fun g => by
        rw [coe_miyamotoFieldAut_apply, one_mul, inv_one, mul_one]
    exact ⟨t, Or.inl ht⟩

end Classes

section Rank

@[expose] def miyamotoA1Bar : Subgroup (GL (Fin 4) K) :=
  miyamotoA1 h ⊓ MonoidHom.eqLocus (glAut (miyamotoBarEquiv h)).toMonoidHom (MonoidHom.id _)

theorem mem_miyamotoA1Bar {g : GL (Fin 4) K} : g ∈ miyamotoA1Bar h ↔
    ∃ b c d : K, h.bar b = b ∧ h.bar c = c ∧ h.bar d = d ∧ g = miyamotoXGL h 0 b c d := by
  have : CharP K 2 := h.charP
  constructor
  · rintro ⟨hA, hfix⟩
    obtain ⟨b, c, d, hb, hd, rfl⟩ := (mem_A1 h).mp hA
    have e : glAut (miyamotoBarEquiv h) (miyamotoXGL h 0 b c d) = miyamotoXGL h 0 b c d := hfix
    rw [glAut_miyamotoXGL, miyamotoXGL_inj] at e
    exact ⟨b, c, d, hb, e.2.2.1, hd, rfl⟩
  · rintro ⟨b, c, d, hb, hc, hd, rfl⟩
    refine ⟨(miyamotoXGL_mem_A1 h).mpr ⟨rfl, hb, hd⟩, ?_⟩
    change glAut (miyamotoBarEquiv h) (miyamotoXGL h 0 b c d) = miyamotoXGL h 0 b c d
    rw [glAut_miyamotoXGL]
    simp only [miyamotoBarEquiv_apply, map_zero, hb, hc, hd]

theorem isElementaryAbelian_miyamotoA1Bar : CFSG.IsElementaryAbelian 2 (miyamotoA1Bar h) := by
  have : CharP K 2 := h.charP
  have hA := isElementaryAbelian_miyamotoA1 h
  refine isElementaryAbelian_two_of_forall (fun x hx y hy => ?_) fun x hx => ?_
  · exact congrArg Subtype.val (mul_comm' (⟨x, hx.1⟩ : miyamotoA1 h) ⟨y, hy.1⟩)
  · have := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := miyamotoA1 h) (p := 2) x hx.1
    rwa [sq] at this

theorem card_miyamotoA1Bar : Nat.card (miyamotoA1Bar h) = (2 ^ f) ^ 3 := by
  have := h.finite
  have : Finite h.fixedField := Subtype.finite
  rw [card_eq_of_param (X := h.fixedField × h.fixedField × h.fixedField)
    (fun x => miyamotoXGL h 0 x.1 x.2.1 x.2.2) ?_ ?_, Nat.card_prod, Nat.card_prod,
    h.card_fixedField]
  · ring
  · rintro ⟨b, c, d⟩ ⟨b', c', d'⟩ e
    obtain ⟨-, e1, e2, e3⟩ := (miyamotoXGL_inj h).mp e
    exact Prod.ext (Subtype.ext e1) (Prod.ext (Subtype.ext e2) (Subtype.ext e3))
  · intro g
    rw [mem_miyamotoA1Bar]
    constructor
    · rintro ⟨b, c, d, hb, hc, hd, rfl⟩
      exact ⟨(⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩), rfl⟩
    · rintro ⟨⟨b, c, d⟩, rfl⟩
      exact ⟨b, c, d, b.2, c.2, d.2, rfl⟩

theorem fixes_miyamotoA1Bar {β : MulAut (gramSU h (miyamotoJ4 K))}
    (hβ : β = miyamotoFieldAut h (miyamotoBarEquiv h) ∨
      β = MulAut.conj (miyamotoZ1S h) * miyamotoFieldAut h (miyamotoBarEquiv h))
    (g : gramSU h (miyamotoJ4 K)) (hg : (g : GL (Fin 4) K) ∈ miyamotoA1Bar h) : β g = g := by
  have hu : miyamotoFieldAut h (miyamotoBarEquiv h) g = g := Subtype.ext hg.2
  rcases hβ with rfl | rfl
  · exact hu
  · rw [MulAut.mul_apply, hu]
    apply Subtype.ext
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      miyamotoA1_mul_comm h (miyamotoZ1S_mem_A1 h) hg.1]
    group

theorem exists_elementaryAbelian_fixed_of_outer {α : MulAut (gramSU h (miyamotoJ4 K))}
    (hα : orderOf α = 2) (hσ : miyamotoFieldFactor h α ≠ 1) :
    ∃ E : Subgroup (GL (Fin 4) K), E ≤ gramSU h (miyamotoJ4 K) ∧
      (∀ g : gramSU h (miyamotoJ4 K), (g : GL (Fin 4) K) ∈ E → α g = g) ∧
        CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = (2 ^ f) ^ 3 := by
  obtain ⟨t, ht⟩ := exists_conj_eq_u_or_uz1 h hα hσ
  set β := MulAut.conj t * α * (MulAut.conj t)⁻¹ with hβdef
  have hαβ : α = (MulAut.conj t)⁻¹ * β * MulAut.conj t := by rw [hβdef]; group
  set c : MulAut (GL (Fin 4) K) := MulAut.conj ((t : GL (Fin 4) K)⁻¹) with hc
  have hE₀S : miyamotoA1Bar h ≤ gramSU h (miyamotoJ4 K) :=
    fun g hg => miyamotoUnipotent_le_SU h true false hg.1
  refine ⟨(miyamotoA1Bar h).map c.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    change (t : GL (Fin 4) K)⁻¹ * e * (t : GL (Fin 4) K)⁻¹⁻¹ ∈ gramSU h (miyamotoJ4 K)
    exact mul_mem (mul_mem (inv_mem t.2) (hE₀S he)) (by rw [inv_inv]; exact t.2)
  · rintro g ⟨e, he, hge⟩
    have hge' : (g : GL (Fin 4) K) = (t : GL (Fin 4) K)⁻¹ * e * t := by
      rw [← hge]
      change (t : GL (Fin 4) K)⁻¹ * e * (t : GL (Fin 4) K)⁻¹⁻¹ = _
      rw [inv_inv]
    have hte : MulAut.conj t g = ⟨e, hE₀S he⟩ := by
      apply Subtype.ext
      rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hge']
      group
    rw [hαβ, MulAut.mul_apply, MulAut.mul_apply, hte, fixes_miyamotoA1Bar h ht _ he]
    apply Subtype.ext
    rw [← map_inv, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      inv_inv, hge']
  · have hA := isElementaryAbelian_miyamotoA1Bar h
    refine isElementaryAbelian_two_of_forall (fun x hx y hy => ?_) fun x hx => ?_
    · obtain ⟨e, he, rfl⟩ := hx
      obtain ⟨e', he', rfl⟩ := hy
      rw [← map_mul, ← map_mul]
      exact congrArg _ (congrArg Subtype.val (mul_comm' (⟨e, he⟩ : miyamotoA1Bar h) ⟨e', he'⟩))
    · obtain ⟨e, he, rfl⟩ := hx
      have := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := miyamotoA1Bar h) (p := 2) e he
      rw [← map_mul, ← sq, this, map_one]
  · rw [Subgroup.card_map_of_injective c.injective, card_miyamotoA1Bar]

end Rank

section CentralizerU

@[expose] def miyamotoFixBar : Subgroup (gramSU h (miyamotoJ4 K)) :=
  MonoidHom.eqLocus (miyamotoFieldAut h (miyamotoBarEquiv h)).toMonoidHom (MonoidHom.id _)

theorem mem_miyamotoFixBar_iff (g : gramSU h (miyamotoJ4 K)) :
    g ∈ miyamotoFixBar h ↔ ∀ i j, h.bar (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j) =
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j := by
  change miyamotoFieldAut h (miyamotoBarEquiv h) g = g ↔ _
  constructor
  · intro e i j
    have := congrFun (congrFun (congrArg (fun x : gramSU h (miyamotoJ4 K) =>
      ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) e) i) j
    simpa [coe_glAut] using this
  · intro e
    apply Subtype.ext
    apply Units.ext
    rw [coe_miyamotoFieldAut_apply, coe_glAut]
    exact Matrix.ext e

@[expose] def miyamotoSp4 : Subgroup (GL (Fin 4) h.fixedField) where
  carrier := {g | (g : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ * miyamotoJ4 h.fixedField * g =
    miyamotoJ4 h.fixedField}
  mul_mem' {g g'} hg hg' := by
    have hg1 : (g : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ * miyamotoJ4 h.fixedField * g =
        miyamotoJ4 h.fixedField := hg
    have hg2 : (g' : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ * miyamotoJ4 h.fixedField * g' =
        miyamotoJ4 h.fixedField := hg'
    change ((g * g' : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ *
      miyamotoJ4 h.fixedField * (g * g' : GL (Fin 4) h.fixedField) = _
    calc ((g * g' : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ *
          miyamotoJ4 h.fixedField * (g * g' : GL (Fin 4) h.fixedField) =
        (g' : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ *
          ((g : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ * miyamotoJ4 h.fixedField * g) * g' := by
          rw [Units.val_mul, transpose_mul]; simp only [Matrix.mul_assoc]
      _ = miyamotoJ4 h.fixedField := by rw [hg1, hg2]
  one_mem' := by
    change ((1 : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ *
      miyamotoJ4 h.fixedField * (1 : GL (Fin 4) h.fixedField) = _
    rw [Units.val_one, transpose_one, Matrix.one_mul, Matrix.mul_one]
  inv_mem' {g} hg := by
    have hgg : (g : Matrix (Fin 4) (Fin 4) h.fixedField) *
        ((g⁻¹ : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    change ((g⁻¹ : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ *
      miyamotoJ4 h.fixedField * (g⁻¹ : GL (Fin 4) h.fixedField) = _
    have hg' : (g : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ * miyamotoJ4 h.fixedField * g =
        miyamotoJ4 h.fixedField := hg
    calc ((g⁻¹ : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ *
          miyamotoJ4 h.fixedField * (g⁻¹ : GL (Fin 4) h.fixedField) =
        ((g⁻¹ : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ *
          ((g : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ * miyamotoJ4 h.fixedField * g) *
            (g⁻¹ : GL (Fin 4) h.fixedField) := by rw [hg']
      _ = ((g : Matrix (Fin 4) (Fin 4) h.fixedField) *
            ((g⁻¹ : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField))ᵀ *
          miyamotoJ4 h.fixedField * ((g : Matrix (Fin 4) (Fin 4) h.fixedField) *
            ((g⁻¹ : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField)) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = miyamotoJ4 h.fixedField := by rw [hgg, transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem miyamotoJ4_map_subtype :
    (miyamotoJ4 h.fixedField).map h.fixedField.subtype = miyamotoJ4 K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoJ4]

theorem bar_map_subtype (M : Matrix (Fin 4) (Fin 4) h.fixedField) :
    (M.map h.fixedField.subtype).map h.bar = M.map h.fixedField.subtype :=
  Matrix.ext fun i j => (M i j).2

theorem map_mem_miyamotoFixBar {g : GL (Fin 4) h.fixedField} (hg : g ∈ miyamotoSp4 h) :
    ∃ hS : Matrix.GeneralLinearGroup.map h.fixedField.subtype g ∈ gramSU h (miyamotoJ4 K),
      (⟨_, hS⟩ : gramSU h (miyamotoJ4 K)) ∈ miyamotoFixBar h := by
  have : CharP K 2 := h.charP
  have hgK : ((Matrix.GeneralLinearGroup.map h.fixedField.subtype g : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = (g : Matrix (Fin 4) (Fin 4) h.fixedField).map
        h.fixedField.subtype := rfl
  have hU : (((Matrix.GeneralLinearGroup.map h.fixedField.subtype g : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * miyamotoJ4 K *
        (Matrix.GeneralLinearGroup.map h.fixedField.subtype g : GL (Fin 4) K) = miyamotoJ4 K := by
    have hg' : (g : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ * miyamotoJ4 h.fixedField * g =
        miyamotoJ4 h.fixedField := hg
    rw [hgK, bar_map_subtype, ← miyamotoJ4_map_subtype h, ← transpose_map, ← Matrix.map_mul,
      ← Matrix.map_mul, hg']
  have hdet : (((Matrix.GeneralLinearGroup.map h.fixedField.subtype g : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K)).det = 1 := by
    have e := congrArg Matrix.det hU
    rw [det_mul, det_mul, det_transpose, hgK, bar_map_subtype] at e
    have e2 : ((g : Matrix (Fin 4) (Fin 4) h.fixedField).map h.fixedField.subtype).det ^ 2 =
        1 ^ 2 := by
      rw [one_pow]
      refine mul_right_cancel₀ (det_miyamotoJ4_ne_zero (K := K)) ?_
      linear_combination e
    rw [hgK]
    exact eq_of_sq_eq_sq e2
  refine ⟨mem_gramSU.mpr ⟨hU, hdet⟩, (mem_miyamotoFixBar_iff h _).mpr fun i j => ?_⟩
  exact ((g : Matrix (Fin 4) (Fin 4) h.fixedField) i j).2

@[expose] def miyamotoSp4EquivFixBar : miyamotoSp4 h ≃* miyamotoFixBar h :=
  MulEquiv.ofBijective
    ({ toFun := fun g => ⟨⟨_, (map_mem_miyamotoFixBar h g.2).1⟩,
        (map_mem_miyamotoFixBar h g.2).2⟩
       map_one' := Subtype.ext (Subtype.ext (map_one _))
       map_mul' := fun g g' => Subtype.ext (Subtype.ext (map_mul _ _ _)) } :
      miyamotoSp4 h →* miyamotoFixBar h)
    ⟨fun g g' e => by
      have e1 := congrArg (fun x : miyamotoFixBar h =>
        (((x : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) e
      refine Subtype.ext (Units.ext (Matrix.ext fun i j => Subtype.ext ?_))
      exact congrFun (congrFun e1 i) j, fun x => by
      obtain ⟨⟨x, hxS⟩, hx⟩ := x
      have hF := (mem_miyamotoFixBar_iff h ⟨x, hxS⟩).mp hx
      set M : Matrix (Fin 4) (Fin 4) h.fixedField :=
        Matrix.of fun i j => ⟨(x : Matrix (Fin 4) (Fin 4) K) i j, hF i j⟩ with hM
      have hMK : M.map h.fixedField.subtype = (x : Matrix (Fin 4) (Fin 4) K) := rfl
      have hdet : M.det ≠ 0 := by
        intro e
        have e2 : (x : Matrix (Fin 4) (Fin 4) K).det = 0 := by
          have e3 := RingHom.map_det h.fixedField.subtype M
          rw [e, map_zero] at e3
          rw [← hMK]
          exact e3.symm
        rw [(mem_gramSU.mp hxS).2] at e2
        exact one_ne_zero e2
      set g := Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet with hg
      have hgSp : g ∈ miyamotoSp4 h := by
        change Mᵀ * miyamotoJ4 h.fixedField * M = miyamotoJ4 h.fixedField
        have key : (Mᵀ * miyamotoJ4 h.fixedField * M).map h.fixedField.subtype =
            (miyamotoJ4 h.fixedField).map h.fixedField.subtype := by
          have hxbar : (x : Matrix (Fin 4) (Fin 4) K).map h.bar = x := Matrix.ext hF
          rw [Matrix.map_mul, Matrix.map_mul, transpose_map, miyamotoJ4_map_subtype, hMK]
          conv_rhs => rw [← (mem_gramSU.mp hxS).1, hxbar]
        exact Matrix.map_injective h.fixedField.subtype_injective key
      exact ⟨⟨g, hgSp⟩, Subtype.ext (Subtype.ext (Units.ext rfl))⟩⟩

end CentralizerU

end CFSG.LocalAnalysis.EvenBN.U4
