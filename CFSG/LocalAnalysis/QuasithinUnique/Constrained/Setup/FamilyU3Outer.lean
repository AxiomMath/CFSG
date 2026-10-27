module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Cover
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyInnerAction

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

section Field

variable {p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p 1 K)

@[expose] noncomputable def barEquiv : K ≃+* K :=
  RingEquiv.ofBijective h.bar (Function.Involutive.bijective h.bar_bar)

theorem barEquiv_apply (c : K) : barEquiv h c = h.bar c := rfl

theorem barEquiv_mul_self : barEquiv h * barEquiv h = 1 :=
  RingEquiv.ext fun c => h.bar_bar c

theorem barEquiv_ne_one : barEquiv h ≠ 1 := by
  intro h1
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  apply hc
  have := congrArg (fun φ : K ≃+* K => φ c) h1
  simpa [barEquiv_apply] using this

theorem ringEquiv_eq_one_or_barEquiv (φ : K ≃+* K) : φ = 1 ∨ φ = barEquiv h := by
  by_cases h1 : φ = 1
  · exact Or.inl h1
  · right
    have : Finite K := h.finite
    have hcard := (card_ringAut_and_isCyclic (p := p) (n := 2) h.prime K
      (by rw [h.card])).1
    have hfin : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by omega)
    obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : RingAut K)).mp hcard
    exact (huniq φ h1).trans (huniq _ (barEquiv_ne_one h)).symm

theorem symm_of_unitary_mul_bar (h2 : (2 : K) ≠ 0) {Am : Matrix (Fin 3) (Fin 3) K}
    (hU : (Am.map h.bar)ᵀ * Am = 1) {c : K} (hc : h.norm c = 1)
    (hAB : Am * Am.map h.bar = c • 1) : Amᵀ = Am ∧ c = 1 := by
  have hc0 : c ≠ 0 := fun h0 => by
    rw [h0, UnitaryFieldData.norm, zero_mul] at hc
    exact zero_ne_one hc
  set Bm := Am.map h.bar with hBm
  have hBmT : Bmᵀ = c⁻¹ • Bm := by
    have h1 : Am * (c⁻¹ • Bm) = 1 := by
      rw [Matrix.mul_smul, hAB, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    exact left_inv_eq_right_inv hU h1
  have hBm0 : Bm ≠ 0 := by
    intro h0
    rw [h0, Matrix.mul_zero] at hAB
    have := congrFun (congrFun hAB.symm 0) 0
    simp [hc0] at this
  have hBm2 : Bm = c⁻¹ • Bmᵀ := by
    have := congrArg Matrix.transpose hBmT
    rwa [Matrix.transpose_transpose, Matrix.transpose_smul] at this
  have hcsq : c * c = 1 := by
    have h3 : Bm = (c⁻¹ * c⁻¹) • Bm := by
      conv_lhs => rw [hBm2, hBmT]
      rw [smul_smul]
    have h4 : (1 - c⁻¹ * c⁻¹) • Bm = 0 := by rw [sub_smul, one_smul, ← h3, sub_self]
    rcases smul_eq_zero.1 h4 with h5 | h5
    · field_simp at h5
      linear_combination h5
    · exact absurd h5 hBm0
  have hbar : ∀ x, h.bar (h.bar x) = x := h.bar_bar
  have hAT : ∀ i j, Am j i = h.bar c⁻¹ * Am i j := by
    intro i j
    have e := congrFun (congrFun hBmT i) j
    simp only [hBm, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at e
    have e2 := congrArg h.bar e
    rwa [map_mul, hbar, hbar] at e2
  have hdetA : (Am.det) ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hU
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  rcases mul_self_eq_one_iff.1 hcsq with h1 | h1
  · refine ⟨?_, h1⟩
    ext i j
    rw [Matrix.transpose_apply, hAT j i, h1, inv_one, map_one, one_mul]
  · exfalso
    have hAT' : Amᵀ = -Am := by
      ext i j
      rw [Matrix.transpose_apply, hAT, h1, inv_neg, inv_one, map_neg, map_one, Matrix.neg_apply]
      ring
    have := congrArg Matrix.det hAT'
    rw [Matrix.det_transpose, Matrix.det_neg] at this
    simp only [Fintype.card_fin] at this
    apply hdetA
    have h22 : (2 : K) * Am.det = 0 := by linear_combination this
    exact (mul_eq_zero.1 h22).resolve_left h2

end Field

abbrev UI {p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p 1 K) : Subgroup (GL (Fin 3) K) :=
  primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

section Beta

variable {p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p 1 K} {X : Type*} [Group X]
  {L : Subgroup X} (D : CoverDataU h L)

@[expose] noncomputable def CoverDataU.beta {g : X} (hg : g ∈ Subgroup.normalizer (L : Set X)) :
    MulAut (PUI h) :=
  MulAut.congr D.ψ (normConjQ hg)

theorem CoverDataU.beta_mk {g : X} (hg : g ∈ Subgroup.normalizer (L : Set X)) (x : ↥(SUI h)) :
    D.beta hg (QuotientGroup.mk x : PUI h) = D.ψ (QuotientGroup.mk (normConj hg (D.φ x))) := by
  rw [← D.hψ x]
  simp [CoverDataU.beta, normConjQ_mk]

theorem CoverDataU.beta_mul {g g' : X} (hg : g ∈ Subgroup.normalizer (L : Set X))
    (hg' : g' ∈ Subgroup.normalizer (L : Set X)) :
    D.beta (Subgroup.mul_mem _ hg hg') = D.beta hg * D.beta hg' := by
  unfold CoverDataU.beta
  rw [normConjQ_mul, map_mul]

theorem CoverDataU.beta_sq {g : X} (hg : g ∈ Subgroup.normalizer (L : Set X)) (hg2 : g * g = 1) :
    D.beta hg * D.beta hg = 1 := by
  unfold CoverDataU.beta
  rw [← map_mul, normConjQ_sq hg hg2, map_one]

theorem CoverDataU.conj_eq (hperf : Group.IsPerfect ↥(SUI h)) {b : X}
    (hb : b ∈ Subgroup.normalizer (L : Set X)) (τ : MulAut ↥(SUI h))
    (hτ : ∀ x : ↥(SUI h),
      D.beta hb (QuotientGroup.mk x : PUI h) = (QuotientGroup.mk (τ x) : PUI h))
    (x : ↥(SUI h)) : b * ((D.φ x : ↥L) : X) * b⁻¹ = ((D.φ (τ x) : ↥L) : X) := by
  have key : ((normConj hb : MulAut ↥L) : ↥L →* ↥L).comp D.φ =
      D.φ.comp (τ : ↥(SUI h) →* ↥(SUI h)) := by
    refine hom_eq_of_central_diff hperf _ _ fun x => ?_
    have h1 := D.beta_mk hb x
    rw [hτ x, ← D.hψ (τ x)] at h1
    have h2 := D.ψ.injective h1
    exact QuotientGroup.eq.1 h2.symm
  have := DFunLike.congr_fun key x
  exact congrArg (fun z : ↥L => (z : X)) this

end Beta

section Auto

variable {p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p 1 K)

@[expose] noncomputable def tauU (A : UI h) (φ : K ≃+* K) : MulAut ↥(SUI h) :=
  (primeFormFieldSU h (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin 3) K)) φ).trans
    (primeFormConjSU h _ A)

theorem coe_tauU (A : UI h) (φ : K ≃+* K) (x : ↥(SUI h)) :
    ((tauU h A φ x : ↥(SUI h)) : GL (Fin 3) K) = A * glAut φ (x : GL (Fin 3) K) * A⁻¹ :=
  rfl

theorem conjField_mk (A : UI h) (φ : K ≃+* K) (x : ↥(SUI h)) :
    (primeFormConjHom h _ A * primeFormFieldHom h
      (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin 3) K)) φ) (QuotientGroup.mk x : PUI h) =
        (QuotientGroup.mk (tauU h A φ x) : PUI h) := by
  rw [MulAut.mul_apply]
  change primeFormConjAut h _ A (primeFormFieldAut h _ φ (QuotientGroup.mk x : PUI h)) = _
  rw [primeFormFieldAut_mk, primeFormConjAut_mk]
  rfl

end Auto

section Inner

variable {p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p 1 K)

theorem exists_SUI_conj_eq_of_sq (A : UI h) {c : Kˣ} (hc : h.norm (c : K) = 1)
    (hAA : (A : GL (Fin 3) K) * A = GeneralLinearGroup.scalar (Fin 3) c) :
    ∃ s : ↥(SUI h), primeFormConjHom h _ A =
      primeFormConjHom h _ ⟨(s : GL (Fin 3) K), s.2.1⟩ := by
  set d : Kˣ := Matrix.GeneralLinearGroup.det (A : GL (Fin 3) K) with hd
  have hdN : h.norm (d : K) = 1 := by
    have := norm_det_eq_one h (1 : GL (Fin 3) K) A.2
    rwa [← Matrix.GeneralLinearGroup.val_det_apply] at this
  have hc3 : c ^ 3 = d * d := by
    have := congrArg Matrix.GeneralLinearGroup.det hAA
    rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at this
    exact this.symm
  set u : Kˣ := c * d⁻¹ with hu
  have hu3 : u ^ 3 * d = 1 := by
    calc u ^ 3 * d = c ^ 3 * (d ^ 3)⁻¹ * d := by rw [hu, mul_pow, inv_pow]
      _ = d * d * (d ^ 3)⁻¹ * d := by rw [hc3]
      _ = 1 := by group
  have hunorm : h.norm (u : K) = 1 := by
    rw [hu, Units.val_mul, norm_mul_eq h, Units.val_inv_eq_inv_val, norm_inv_eq h, hc, hdN]
    simp
  have hscal : GeneralLinearGroup.scalar (Fin 3) u ∈
      primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [mem_primeFormUnitary, GeneralLinearGroup.coe_scalar]
    have := scalar_barTranspose_mul_mul h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) (u : K)
    rw [this, hunorm, one_smul]
  have hdet1 : Matrix.GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) u *
      (A : GL (Fin 3) K)) = 1 := by
    rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, ← hd]
    exact hu3
  have hmem : GeneralLinearGroup.scalar (Fin 3) u * (A : GL (Fin 3) K) ∈ SUI h := by
    rw [SUI, mem_gramSU_iff_unitary]
    refine ⟨mul_mem hscal A.2, ?_⟩
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet1, Units.val_one]
  refine ⟨⟨_, hmem⟩, ?_⟩
  apply MulEquiv.ext
  intro x
  refine QuotientGroup.induction_on x fun g => ?_
  rw [primeFormConjHom_mk, primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  have hcomm : ∀ Y : GL (Fin 3) K,
      GeneralLinearGroup.scalar (Fin 3) u * Y * (GeneralLinearGroup.scalar (Fin 3) u)⁻¹ = Y :=
    fun Y => by rw [← (commute_scalar u Y).eq, mul_assoc, mul_inv_cancel, mul_one]
  show (A : GL (Fin 3) K) * (g : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ =
    (GeneralLinearGroup.scalar (Fin 3) u * (A : GL (Fin 3) K)) * (g : GL (Fin 3) K) *
      (GeneralLinearGroup.scalar (Fin 3) u * (A : GL (Fin 3) K))⁻¹
  rw [_root_.mul_inv_rev, show (GeneralLinearGroup.scalar (Fin 3) u * (A : GL (Fin 3) K)) *
    (g : GL (Fin 3) K) * ((A : GL (Fin 3) K)⁻¹ * (GeneralLinearGroup.scalar (Fin 3) u)⁻¹) =
    GeneralLinearGroup.scalar (Fin 3) u * ((A : GL (Fin 3) K) * (g : GL (Fin 3) K) *
      (A : GL (Fin 3) K)⁻¹) * (GeneralLinearGroup.scalar (Fin 3) u)⁻¹ by group, hcomm]

variable {h}

theorem CoverDataU.mem_of_conj (hperf : Group.IsPerfect ↥(SUI h)) {W : Type}
    [CommGroup W] {L : Subgroup (MulAut W)} (D : CoverDataU h L) (hW : ∀ w : W, w * w = 1)
    (hL : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (hb2 : b * b = 1) (A : UI h)
    (hβ : D.beta hb = primeFormConjHom h _ A) : b ∈ L := by
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  have hΨ : primeFormPsi h hC ⟨A * A, 1⟩ = 1 := by
    rw [primeFormPsi_apply, map_one, mul_one, map_mul]
    have := D.beta_sq hb hb2
    rwa [hβ] at this
  obtain ⟨-, c, hcN, hcA⟩ := (primeFormPsi_eq_one_iff h hC le_rfl ⟨A * A, 1⟩).1 hΨ
  obtain ⟨s, hs⟩ := exists_SUI_conj_eq_of_sq h A hcN hcA
  have hτ : ∀ x : ↥(SUI h), D.beta hb (QuotientGroup.mk x : PUI h) =
      (QuotientGroup.mk (MulAut.conj s x) : PUI h) := by
    intro x
    rw [hβ, hs, primeFormConjHom_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext rfl)
  have hbl : ∀ y ∈ L, b * y * b⁻¹ = (D.φ s : MulAut W) * y * (D.φ s : MulAut W)⁻¹ := by
    intro y hy
    obtain ⟨x, hx⟩ := D.surj ⟨y, hy⟩
    have := D.conj_eq hperf hb (MulAut.conj s) hτ x
    rw [hx, MulAut.conj_apply, map_mul, map_mul, map_inv, hx] at this
    simpa using this
  exact mem_of_inner_action hW hL hodd (D.φ s).2 hb2 hbl

end Inner

section Dichotomy

variable {p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p 1 K}

theorem CoverDataU.dichotomy (hp5 : 5 ≤ p) (hperf : Group.IsPerfect ↥(SUI h)) {W : Type}
    [CommGroup W] {L : Subgroup (MulAut W)} (D : CoverDataU h L) (hW : ∀ w : W, w * w = 1)
    (hL : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (hb2 : b * b = 1) :
    b ∈ L ∨ ∃ A : UI h, ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ =
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∧
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar = 1 ∧
      D.beta hb = primeFormConjHom h _ A * primeFormFieldHom h
        (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin 3) K)) (barEquiv h) := by
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  have hq : ¬(3 = 3 ∧ p ^ 1 = 2) := by
    rintro ⟨-, h5⟩
    rw [pow_one] at h5
    omega
  have h2 : (2 : K) ≠ 0 := by
    have : CharP K p := h.charP
    exact Ring.two_ne_zero (by rw [ringChar.eq K p]; omega)
  obtain ⟨φ, ⟨A, hA⟩, -⟩ := existsUnique_primeFormFieldFactor h hC le_rfl hq (D.beta hb)
  rcases ringEquiv_eq_one_or_barEquiv h φ with rfl | rfl
  · left
    rw [map_one, mul_one] at hA
    exact D.mem_of_conj hperf hW hL hodd hb hb2 A hA
  · right
    refine ⟨A, ?_⟩
    have hΨ : primeFormPsi h hC (⟨A, barEquiv h⟩ * ⟨A, barEquiv h⟩) = 1 := by
      rw [map_mul, primeFormPsi_apply, ← hA]
      exact D.beta_sq hb hb2
    obtain ⟨-, c, hcN, hcA⟩ := (primeFormPsi_eq_one_iff h hC le_rfl _).1 hΨ
    rw [SemidirectProduct.mul_left] at hcA
    have hcA' : (A : GL (Fin 3) K) * glAut (barEquiv h) (A : GL (Fin 3) K) =
        GeneralLinearGroup.scalar (Fin 3) c := hcA
    have hAB : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar = (c : K) • 1 := by
      have := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K)) hcA'
      simp only [Units.val_mul, coe_glAut, GeneralLinearGroup.coe_scalar, scalar_apply] at this
      exact this.trans (smul_one_eq_diagonal _).symm
    have hU : (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      have := mem_primeFormUnitary.1 A.2
      simpa using this
    obtain ⟨hsym, hc1⟩ := symm_of_unitary_mul_bar h h2 hU hcN hAB
    refine ⟨hsym, ?_, hA⟩
    rw [hAB, hc1, one_smul]

theorem CoverDataU.mul_mem (hperf : Group.IsPerfect ↥(SUI h)) {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} (D : CoverDataU h L) (hW : ∀ w : W, w * w = 1)
    (hL : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) {a a' : MulAut W}
    (ha : a ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (ha' : a' ∈ Subgroup.normalizer (L : Set (MulAut W))) {A A' : UI h}
    (hβ : D.beta ha = primeFormConjHom h _ A * primeFormFieldHom h
      (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin 3) K)) (barEquiv h))
    (hβ' : D.beta ha' = primeFormConjHom h _ A' * primeFormFieldHom h
      (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin 3) K)) (barEquiv h))
    (hsq : a * a' * (a * a') = 1) : a * a' ∈ L := by
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  have hfield : primeFormFieldHom h hC (barEquiv h) * primeFormFieldHom h hC (barEquiv h) = 1 := by
    rw [← map_mul, barEquiv_mul_self, map_one]
  have hfinv : (primeFormFieldHom h hC (barEquiv h))⁻¹ = primeFormFieldHom h hC (barEquiv h) :=
    inv_eq_of_mul_eq_one_right hfield
  refine D.mem_of_conj hperf hW hL hodd (Subgroup.mul_mem _ ha ha') hsq
    (A * primeFormFieldU h hC (barEquiv h) A') ?_
  rw [D.beta_mul ha ha', hβ, hβ', map_mul, ← primeFormField_conj_eq h hC (barEquiv h) A', hfinv]
  simp only [mul_assoc]

end Dichotomy


end CFSG.QuasithinUnique.Setup.Family
