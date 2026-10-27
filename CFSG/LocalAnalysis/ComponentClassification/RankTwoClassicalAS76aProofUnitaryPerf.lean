module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOmegaPerf
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUSetup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTypes

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open scoped Matrix commutatorElement

section Levi

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] (σ : K →+* K)

@[expose] def hpCol (e f : ι → K) : Matrix ι (Fin 2) K := Matrix.of fun r k => ![e, f] k r

@[expose] def hpRow (e f : ι → K) : Matrix (Fin 2) ι K := Matrix.of fun k r => σ (![f, e] k r)

@[expose] noncomputable def hypLeviMat (e f : ι → K) (A : Matrix (Fin 2) (Fin 2) K) :
    Matrix ι ι K :=
  1 + hpCol e f * (A - 1) * hpRow σ e f

variable {σ}

omit [Fintype ι] [DecidableEq ι] in
theorem hpCol_mulVec (e f : ι → K) (c : Fin 2 → K) : hpCol e f *ᵥ c = c 0 • e + c 1 • f := by
  ext r
  simp [hpCol, mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

omit [DecidableEq ι] in
theorem hpRow_mulVec (e f v : ι → K) : hpRow σ e f *ᵥ v = ![hform σ f v, hform σ e v] := by
  ext k
  fin_cases k <;> simp [hpRow, mulVec, hform, dotProduct, Function.comp]

omit [DecidableEq ι] in
theorem hpRow_mul_hpCol {e f : ι → K} (he : hform σ e e = 0) (hf : hform σ f f = 0)
    (hef : hform σ e f = 1) (hfe : hform σ f e = 1) : hpRow σ e f * hpCol e f = 1 :=
  Matrix.ext_iff_mulVec.mpr fun c => by
    rw [← mulVec_mulVec, hpCol_mulVec, hpRow_mulVec, one_mulVec]
    simp only [hform_add_right, hform_smul_right, he, hf, hef, hfe, mul_zero, mul_one, add_zero,
      zero_add]
    ext k
    fin_cases k <;> rfl

omit [Fintype ι] in
theorem hypLeviMat_one (e f : ι → K) : hypLeviMat σ e f 1 = 1 := by
  simp [hypLeviMat]

theorem hypLeviMat_mul {e f : ι → K} (hP : hpRow σ e f * hpCol e f = 1)
    (A B : Matrix (Fin 2) (Fin 2) K) :
    hypLeviMat σ e f (A * B) = hypLeviMat σ e f A * hypLeviMat σ e f B := by
  have h1 : hpCol e f * (A - 1) * hpRow σ e f * (hpCol e f * (B - 1) * hpRow σ e f) =
      hpCol e f * ((A - 1) * (B - 1)) * hpRow σ e f := by
    rw [show hpCol e f * (A - 1) * hpRow σ e f * (hpCol e f * (B - 1) * hpRow σ e f) =
      hpCol e f * (A - 1) * (hpRow σ e f * hpCol e f) * (B - 1) * hpRow σ e f by
        simp only [Matrix.mul_assoc], hP, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  have h2 : A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by noncomm_ring
  simp only [hypLeviMat]
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, h1, h2, Matrix.mul_add,
    Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  abel

theorem det_hypLeviMat {e f : ι → K} (hP : hpRow σ e f * hpCol e f = 1)
    (A : Matrix (Fin 2) (Fin 2) K) : (hypLeviMat σ e f A).det = A.det := by
  rw [hypLeviMat, Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hP,
    Matrix.mul_one, add_sub_cancel]

theorem hypLeviMat_mulVec_of_perp {e f v : ι → K} (hfv : hform σ f v = 0)
    (hev : hform σ e v = 0) (A : Matrix (Fin 2) (Fin 2) K) : hypLeviMat σ e f A *ᵥ v = v := by
  have h0 : hpRow σ e f *ᵥ v = 0 := by
    rw [hpRow_mulVec, hfv, hev]
    ext k
    fin_cases k <;> rfl
  rw [hypLeviMat, add_mulVec, one_mulVec, ← mulVec_mulVec, h0, mulVec_zero, add_zero]

theorem hform_hypLeviMat_mulVec {e f u : ι → K} (hue : hform σ u e = 0) (huf : hform σ u f = 0)
    (A : Matrix (Fin 2) (Fin 2) K) (v : ι → K) :
    hform σ u (hypLeviMat σ e f A *ᵥ v) = hform σ u v := by
  rw [hypLeviMat, add_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hpCol_mulVec,
    hform_add_right, hform_add_right, hform_smul_right, hform_smul_right, hue, huf, mul_zero,
    mul_zero, add_zero, add_zero]

theorem hypLeviMat_mulVec_left {e f : ι → K} (he : hform σ e e = 0) (hfe : hform σ f e = 1)
    (A : Matrix (Fin 2) (Fin 2) K) : hypLeviMat σ e f A *ᵥ e = A 0 0 • e + A 1 0 • f := by
  have h0 : hpRow σ e f *ᵥ e = Pi.single 0 1 := by
    rw [hpRow_mulVec, hfe, he]
    ext k
    fin_cases k <;> rfl
  have h1 : (A - 1) *ᵥ (Pi.single 0 1 : Fin 2 → K) = ![A 0 0 - 1, A 1 0] := by
    ext k
    fin_cases k <;> simp [mulVec, dotProduct, Pi.single_apply, Matrix.one_apply]
  rw [hypLeviMat, add_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, h0, h1, hpCol_mulVec]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_smul, one_smul]
  abel

theorem frH_mul_frH : frH K * frH K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frH, Matrix.mul_apply, Fin.sum_univ_two]

omit [Fintype ι] in
theorem adjM_hypLeviMat (hσ : ∀ x, σ (σ x) = x) (e f : ι → K) (A : Matrix (Fin 2) (Fin 2) K) :
    adjM σ (hypLeviMat σ e f A) = hypLeviMat σ e f (frH K * (A.map σ)ᵀ * frH K) := by
  have hE : ((hpCol e f).map σ)ᵀ = frH K * hpRow σ e f := by
    ext k r
    fin_cases k <;> simp [hpCol, hpRow, frH, Matrix.mul_apply, Fin.sum_univ_two]
  have hR : ((hpRow σ e f).map σ)ᵀ = hpCol e f * frH K := by
    ext r k
    fin_cases k <;> simp [hpCol, hpRow, frH, Matrix.mul_apply, Fin.sum_univ_two, hσ]
  have hA1 : ((A - 1).map σ)ᵀ = (A.map σ)ᵀ - 1 := by
    ext i j
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
  calc adjM σ (hypLeviMat σ e f A) =
      1 + hpCol e f * frH K * (((A.map σ)ᵀ - 1) * (frH K * hpRow σ e f)) := by
        rw [hypLeviMat, adjM_add, adjM_one, adjM, Matrix.map_mul, Matrix.map_mul, transpose_mul,
          transpose_mul, hE, hR, hA1]
    _ = 1 + hpCol e f * (frH K * ((A.map σ)ᵀ - 1) * frH K) * hpRow σ e f := by
        simp only [Matrix.mul_assoc]
    _ = hypLeviMat σ e f (frH K * (A.map σ)ᵀ * frH K) := by
        rw [hypLeviMat, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, frH_mul_frH]

theorem adjM_hypLeviMat_mul_self [CharP K 2] (hσ : ∀ x, σ (σ x) = x) {e f : ι → K}
    (hP : hpRow σ e f * hpCol e f = 1) {A : Matrix (Fin 2) (Fin 2) K} (hAσ : A.map σ = A)
    (hdet : A.det = 1) : adjM σ (hypLeviMat σ e f A) * hypLeviMat σ e f A = 1 := by
  have hJt : (frH K)ᵀ = frH K := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h1 := congrArg transpose (mul_frH A)
  rw [transpose_mul, transpose_mul, transpose_transpose, hJt] at h1
  have hadj : frH K * Aᵀ * frH K * A = 1 := by
    rw [h1, Matrix.mul_assoc (adjugate A), frH_mul_frH, Matrix.mul_one, adjugate_mul, hdet,
      one_smul]
  rw [adjM_hypLeviMat hσ, hAσ, ← hypLeviMat_mul hP, hadj, hypLeviMat_one]

theorem hypLeviMat_coe_mul {e f : ι → K} (hP : hpRow σ e f * hpCol e f = 1)
    (g g' : Matrix.SpecialLinearGroup (Fin 2) K) :
    hypLeviMat σ e f ↑(g * g') = hypLeviMat σ e f g * hypLeviMat σ e f g' := by
  rw [Matrix.SpecialLinearGroup.coe_mul, hypLeviMat_mul hP]

omit [Fintype ι] in
theorem hypLeviMat_coe_one (e f : ι → K) :
    hypLeviMat σ e f ↑(1 : Matrix.SpecialLinearGroup (Fin 2) K) = 1 := by
  rw [Matrix.SpecialLinearGroup.coe_one, hypLeviMat_one]

@[expose] noncomputable def hypLevi {e f : ι → K} (hP : hpRow σ e f * hpCol e f = 1) :
    Matrix.SpecialLinearGroup (Fin 2) K →* GL ι K where
  toFun g := ⟨hypLeviMat σ e f g, hypLeviMat σ e f ↑g⁻¹,
    by rw [← hypLeviMat_coe_mul hP, mul_inv_cancel, hypLeviMat_coe_one],
    by rw [← hypLeviMat_coe_mul hP, inv_mul_cancel, hypLeviMat_coe_one]⟩
  map_one' := Units.ext (hypLeviMat_coe_one e f)
  map_mul' g g' := Units.ext (hypLeviMat_coe_mul hP g g')

end Levi

section Root

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {σ : K →+* K}

variable (σ) in
@[expose] noncomputable def uSiegel (u x : ι → K) : Matrix ι ι K :=
  vecMulVec x (σ ∘ u) + vecMulVec u (σ ∘ x)

omit [DecidableEq ι] in
theorem uSiegel_mulVec (u x v : ι → K) :
    uSiegel σ u x *ᵥ v = hform σ u v • x + hform σ x v • u := by
  rw [uSiegel, add_mulVec, vecMulVec_mulVec', vecMulVec_mulVec']
  rfl

omit [DecidableEq ι] in
theorem vecMulVec_comp_mulVec (u v : ι → K) :
    vecMulVec u (σ ∘ u) *ᵥ v = hform σ u v • u := by
  rw [vecMulVec_mulVec']
  rfl

omit [DecidableEq ι] in
theorem uSiegel_sub (u x y : ι → K) : uSiegel σ u x - uSiegel σ u y = uSiegel σ u (x - y) :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    rw [sub_mulVec, uSiegel_mulVec, uSiegel_mulVec, uSiegel_mulVec, hform_sub_left, sub_smul,
      smul_sub]
    abel

omit [DecidableEq ι] in
theorem uSiegel_mul (hσ : ∀ x, σ (σ x) = x) {u x y : ι → K} (huu : hform σ u u = 0)
    (hux : hform σ u x = 0) (huy : hform σ u y = 0) :
    uSiegel σ u x * uSiegel σ u y = hform σ x y • vecMulVec u (σ ∘ u) :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    have hxu : hform σ x u = 0 := by rw [hform_comm hσ, hux, map_zero]
    rw [← mulVec_mulVec, uSiegel_mulVec u y v, mulVec_add, mulVec_smul, mulVec_smul,
      uSiegel_mulVec, uSiegel_mulVec, huy, huu, hxu, smul_mulVec, vecMulVec_comp_mulVec]
    simp only [zero_smul, zero_add, add_zero, smul_zero, smul_smul, mul_comm]

omit [DecidableEq ι] in
theorem vecMulVec_mul_uSiegel {u x : ι → K} (huu : hform σ u u = 0) (hux : hform σ u x = 0) :
    vecMulVec u (σ ∘ u) * uSiegel σ u x = 0 :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, vecMulVec_comp_mulVec, uSiegel_mulVec, hform_add_right,
      hform_smul_right, hform_smul_right, hux, huu, mul_zero, mul_zero, add_zero, zero_smul,
      zero_mulVec]

omit [DecidableEq ι] in
theorem uSiegel_mul_vecMulVec (hσ : ∀ x, σ (σ x) = x) {u x : ι → K} (huu : hform σ u u = 0)
    (hux : hform σ u x = 0) : uSiegel σ u x * vecMulVec u (σ ∘ u) = 0 :=
  Matrix.ext_iff_mulVec.mpr fun v => by
    have hxu : hform σ x u = 0 := by rw [hform_comm hσ, hux, map_zero]
    rw [← mulVec_mulVec, vecMulVec_comp_mulVec, mulVec_smul, uSiegel_mulVec, huu, hxu,
      zero_smul, zero_smul, add_zero, smul_zero, zero_mulVec]

omit [DecidableEq ι] in
theorem uSiegel_mul_self (hσ : ∀ x, σ (σ x) = x) {u x : ι → K} (huu : hform σ u u = 0)
    (hux : hform σ u x = 0) (hxx : hform σ x x = 0) : uSiegel σ u x * uSiegel σ u x = 0 := by
  rw [uSiegel_mul hσ huu hux hux, hxx, zero_smul]

omit [Fintype ι] [DecidableEq ι] in
theorem adjM_uSiegel (hσ : ∀ x, σ (σ x) = x) (u x : ι → K) :
    adjM σ (uSiegel σ u x) = uSiegel σ u x := by
  have hc : ∀ w : ι → K, σ ∘ (σ ∘ w) = w := fun w => funext fun i => hσ (w i)
  rw [uSiegel, adjM_add, adjM_vecMulVec, adjM_vecMulVec, hc, hc, add_comm]

theorem conj_uSiegel {D : GL ι K} (hD : adjM σ (D : Matrix ι ι K) * D = 1) {u : ι → K}
    (hDu : (D : Matrix ι ι K) *ᵥ u = u) (x : ι → K) :
    (D : Matrix ι ι K) * uSiegel σ u x * ((D⁻¹ : GL ι K) : Matrix ι ι K) =
      uSiegel σ u ((D : Matrix ι ι K) *ᵥ x) := by
  have hDi : ((D⁻¹ : GL ι K) : Matrix ι ι K) = adjM σ (D : Matrix ι ι K) := by
    calc ((D⁻¹ : GL ι K) : Matrix ι ι K) =
        adjM σ (D : Matrix ι ι K) * D * ((D⁻¹ : GL ι K) : Matrix ι ι K) := by rw [hD, one_mul]
      _ = adjM σ (D : Matrix ι ι K) := by rw [mul_assoc, Units.mul_inv, mul_one]
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, uSiegel_mulVec, uSiegel_mulVec, hDi, mulVec_add,
    mulVec_smul, mulVec_smul, hDu, ← hform_mulVec, ← hform_mulVec, hDu]

theorem commutatorElement_uSiegel (hσ : ∀ x, σ (σ x) = x) {u x y : ι → K}
    (huu : hform σ u u = 0) (hux : hform σ u x = 0) (huy : hform σ u y = 0)
    (hX : uSiegel σ u x * uSiegel σ u x = 0) (hY : uSiegel σ u y * uSiegel σ u y = 0) :
    ((⁅sqZeroGL (uSiegel σ u x) hX, sqZeroGL (uSiegel σ u y) hY⁆ : GL ι K) : Matrix ι ι K) =
      1 + (hform σ x y - hform σ y x) • vecMulVec u (σ ∘ u) := by
  have e1 : ((sqZeroGL (uSiegel σ u x) hX)⁻¹ : GL ι K) = (1 - uSiegel σ u x : Matrix ι ι K) :=
    rfl
  have e2 : ((sqZeroGL (uSiegel σ u y) hY)⁻¹ : GL ι K) = (1 - uSiegel σ u y : Matrix ι ι K) :=
    rfl
  rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, coe_sqZeroGL,
    coe_sqZeroGL, e1, e2, commutator_expand_of_mul_self hX hY, uSiegel_mul hσ huu hux huy,
    uSiegel_mul hσ huu huy hux]
  simp only [Matrix.smul_mul, vecMulVec_mul_uSiegel huu hux, vecMulVec_mul_uSiegel huu huy,
    smul_zero, Matrix.zero_mul, sub_zero, add_zero, sub_smul]

end Root

section SU

variable {n q : ℕ} {K : Type} [Field K] [CharP K 2] {σ : K →+* K}

theorem sqZeroGL_mem_statedSU (hσq : ∀ x, σ x = x ^ q) {P : Matrix (Fin n) (Fin n) K}
    (hP : P * P = 0) (hPh : adjM σ P = P) : sqZeroGL P hP ∈ StatedSU n q K := by
  refine mem_statedSU_of hσq ?_ ?_
  · apply eq_one_of_sq_eq_one_of_charTwo
    rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, sqZeroGL_sq, Units.val_one, Matrix.det_one]
  · rw [coe_sqZeroGL, adjM_add, adjM_one, hPh, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
      Matrix.mul_one, hP, add_zero, add_assoc, ← two_smul K P, CharTwo.two_eq_zero, zero_smul,
      add_zero]

end SU

theorem mem_perfectCore_of_unitary_transvection {n m : ℕ} {K : Type} [Field K] [Finite K]
    (hn : 4 ≤ n) (hm : 2 ≤ m) (hK : Nat.card K = (2 ^ m) ^ 2) {M : GL (Fin n) K}
    (hM : M ∈ StatedSU n (2 ^ m) K) (hM2 : orderOf M = 2) (hr : commRank M = 1) :
    M ∈ perfectCore (StatedSU n (2 ^ m) K ⊓ centralizer ({M} : Set (GL (Fin n) K))) := by
  classical
  have h := unitaryFieldData_of_card hK (by omega)
  have : CharP K 2 := h.charP
  have hσ : ∀ x, h.bar (h.bar x) = x := h.bar_bar
  have hσq : ∀ x, h.bar x = x ^ 2 ^ m := h.bar_apply
  have hU := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK
  have hσU : ∀ x, h.bar x = CFSG.LieType.BorelTits.unitaryInvolution K 2 m x := fun x => by
    rw [hσq, CFSG.LieType.BorelTits.unitaryInvolution_apply]
  have htr : ∀ a, h.bar a = a → ∃ d, d + h.bar d = a := fun a ha => by
    obtain ⟨d, hd⟩ := hU.trace_surj a (by rw [← hσU]; exact ha)
    exact ⟨d, by rw [hσU]; exact hd⟩
  have hMu := adjM_mul_self_of_mem_statedSU hσ hσq hM
  have hMM : (M : Matrix (Fin n) (Fin n) K) * M = 1 := by
    have h1 := pow_orderOf_eq_one M
    rw [hM2, sq] at h1
    rw [← Units.val_mul, h1, Units.val_one]
  have hMadj : adjM h.bar (M : Matrix (Fin n) (Fin n) K) = M := by
    calc adjM h.bar (M : Matrix (Fin n) (Fin n) K) =
        adjM h.bar (M : Matrix (Fin n) (Fin n) K) * (M * M) := by rw [hMM, mul_one]
      _ = M := by rw [← mul_assoc, hMu, one_mul]
  have hNh : adjM h.bar ((M : Matrix (Fin n) (Fin n) K) - 1) =
      (M : Matrix (Fin n) (Fin n) K) - 1 := by
    rw [adjM_sub, hMadj, adjM_one]
  obtain ⟨u, c, hu, -, hσc, huu, huc⟩ := exists_hermitian_rank_one hσ hNh
    (sub_one_mul_self_eq_zero hM2) hr
  have hMT : (M : Matrix (Fin n) (Fin n) K) = 1 + c • vecMulVec u (h.bar ∘ u) := by
    have h1 : (M : Matrix (Fin n) (Fin n) K) - 1 = c • vecMulVec u (h.bar ∘ u) :=
      Matrix.ext_iff_mulVec.mpr fun v => by
        rw [huc, smul_mulVec, vecMulVec_comp_mulVec, smul_smul]
    rw [← h1, add_sub_cancel]
  obtain ⟨τ, hτ⟩ := htr 1 (map_one h.bar)
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin n := ⟨1, by omega⟩ with hi₁
  set i₂ : Fin n := ⟨2, by omega⟩ with hi₂
  set i₃ : Fin n := ⟨3, by omega⟩ with hi₃
  have h01 : i₀ ≠ i₁ := by simp [hi₀, hi₁, Fin.ext_iff]
  have h23 : i₂ ≠ i₃ := by simp [hi₂, hi₃, Fin.ext_iff]
  obtain ⟨s, hs⟩ : ∃ s : Fin n → K, s = Pi.single i₀ 1 + Pi.single i₁ 1 := ⟨_, rfl⟩
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : Fin n → K, v₀ = Pi.single i₂ 1 + Pi.single i₃ 1 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : Fin n → K, t = Pi.single i₀ 1 + τ • s := ⟨_, rfl⟩
  have hss : hform h.bar s s = 0 := by rw [hs]; exact hform_single_add_single h.bar h01
  have hv₀v₀ : hform h.bar v₀ v₀ = 0 := by rw [hv₀]; exact hform_single_add_single h.bar h23
  have hv₀0 : v₀ ≠ 0 := fun h0 => by
    have := congrFun h0 i₂
    simp [hv₀, h23] at this
  have hv₀s : hform h.bar v₀ s = 0 := by
    rw [hv₀, hform_add_left, hform_single_one_left, hform_single_one_left, hs]
    simp [hi₀, hi₁, hi₂, hi₃, Fin.ext_iff]
  have hv₀e₀ : hform h.bar v₀ (Pi.single i₀ 1) = 0 := by
    rw [hv₀, hform_add_left, hform_single_one_left, hform_single_one_left]
    simp [hi₀, hi₂, hi₃, Fin.ext_iff]
  have he₀s : hform h.bar (Pi.single i₀ 1) s = 1 := by
    rw [hform_single_one_left, hs]
    simp [h01]
  have hse₀ : hform h.bar s (Pi.single i₀ 1) = 1 := by rw [hform_comm hσ, he₀s, map_one]
  have he₀e₀ : hform h.bar (Pi.single i₀ 1 : Fin n → K) (Pi.single i₀ 1) = 1 := by
    rw [hform_single_one_left]
    simp
  have hst : hform h.bar s t = 1 := by
    rw [ht, hform_add_right, hform_smul_right, hss, mul_zero, add_zero, hse₀]
  have htt : hform h.bar t t = 0 := by
    rw [ht]
    simp only [hform_add_left, hform_add_right, hform_smul_left, hform_smul_right, he₀e₀, he₀s,
      hse₀, hss]
    linear_combination hτ + CharTwo.two_eq_zero (R := K)
  have hv₀t : hform h.bar v₀ t = 0 := by
    rw [ht, hform_add_right, hform_smul_right, hv₀e₀, hv₀s, mul_zero, add_zero]
  obtain ⟨g, hg⟩ := exists_statedSU_mulVec_eq h (n := n) (by omega) hv₀0 hv₀v₀ hu huu
  obtain ⟨e, he⟩ : ∃ e, e = (g : GL (Fin n) K).val *ᵥ s := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, f = (g : GL (Fin n) K).val *ᵥ t := ⟨_, rfl⟩
  have hee : hform h.bar e e = 0 := by rw [he, hform_mulVec_mulVec h, hss]
  have hff : hform h.bar f f = 0 := by rw [hf, hform_mulVec_mulVec h, htt]
  have hef : hform h.bar e f = 1 := by rw [he, hf, hform_mulVec_mulVec h, hst]
  have hfe : hform h.bar f e = 1 := by rw [hform_comm hσ, hef, map_one]
  have hue : hform h.bar u e = 0 := by rw [← hg, he, hform_mulVec_mulVec h, hv₀s]
  have huf : hform h.bar u f = 0 := by rw [← hg, hf, hform_mulVec_mulVec h, hv₀t]
  have heu : hform h.bar e u = 0 := by rw [hform_comm hσ, hue, map_zero]
  have hfu : hform h.bar f u = 0 := by rw [hform_comm hσ, huf, map_zero]
  have hP := hpRow_mul_hpCol hee hff hef hfe
  have hTD : ∀ {D : Matrix (Fin n) (Fin n) K}, D *ᵥ u = u →
      (∀ v, hform h.bar u (D *ᵥ v) = hform h.bar u v) →
      D * (M : Matrix (Fin n) (Fin n) K) = M * D := fun {D} hDu hDv => by
    have h1 : D * vecMulVec u (h.bar ∘ u) = vecMulVec u (h.bar ∘ u) * D :=
      Matrix.ext_iff_mulVec.mpr fun v => by
        rw [← mulVec_mulVec, ← mulVec_mulVec, vecMulVec_comp_mulVec, vecMulVec_comp_mulVec,
          mulVec_smul, hDu, hDv]
    rw [hMT, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul, h1]
  set F := CFSG.LieType.Steinberg.fixedSubfield K 2 m with hFdef
  have hFσ : ∀ a : F, h.bar (a : K) = a := fun a => by rw [hσU]; exact a.2
  set LF := (hypLevi hP).comp (Matrix.SpecialLinearGroup.map F.subtype) with hLF
  have hLFv : ∀ a, ((LF a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      hypLeviMat h.bar e f ((a : Matrix (Fin 2) (Fin 2) F).map F.subtype) := fun _ => rfl
  have hLFu : ∀ a, ((LF a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u = u := fun a => by
    rw [hLFv]
    exact hypLeviMat_mulVec_of_perp hfu heu _
  have hLFadj : ∀ a, adjM h.bar ((LF a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((LF a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := fun a => by
    rw [hLFv]
    refine adjM_hypLeviMat_mul_self hσ hP ?_ ?_
    · ext i j
      simp [hFσ]
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, a.2, map_one]
  have hLFdet : ∀ a, ((LF a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := fun a => by
    rw [hLFv, det_hypLeviMat hP, ← RingHom.mapMatrix_apply, ← RingHom.map_det, a.2, map_one]
  have hLFM : ∀ a, LF a * M = M * LF a := fun a => Units.ext (by
    rw [Units.val_mul, Units.val_mul]
    exact hTD (hLFu a) fun v => by rw [hLFv]; exact hform_hypLeviMat_mulVec hue huf _ v)
  have hperf : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)), ⊤⁆ = ⊤ :=
    (CFSG.LinearGroups.special_linear_dimension_two_perfect
      (exists_finset_fixedSubfield hK hm)).commutator_eq_top
  have hLperf : ⁅LF.range, LF.range⁆ = LF.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hperf]
  have hLC : LF.range ≤ StatedSU n (2 ^ m) K ⊓ centralizer ({M} : Set (GL (Fin n) K)) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨mem_statedSU_of hσq (hLFdet a) (hLFadj a), mem_centralizer_singleton_iff.mpr (hLFM a)⟩
  have hLcore : LF.range ≤
      perfectCore (StatedSU n (2 ^ m) K ⊓ centralizer ({M} : Set (GL (Fin n) K))) :=
    CFSG.Quasithin.le_perfectCore_of_perfect hLC hLperf
  have hρ : ∀ {x : Fin n → K} (hux : hform h.bar u x = 0) (hxx : hform h.bar x x = 0),
      sqZeroGL (uSiegel h.bar u x) (uSiegel_mul_self hσ huu hux hxx) ∈
        StatedSU n (2 ^ m) K ⊓ centralizer ({M} : Set (GL (Fin n) K)) := fun {x} hux hxx => by
    refine ⟨sqZeroGL_mem_statedSU hσq _ (adjM_uSiegel hσ u x),
      mem_centralizer_singleton_iff.mpr (Units.ext ?_)⟩
    rw [Units.val_mul, Units.val_mul, coe_sqZeroGL, hMT]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_smul,
      Matrix.smul_mul, uSiegel_mul_vecMulVec hσ huu hux, vecMulVec_mul_uSiegel huu hux,
      smul_zero, add_zero]
    abel
  obtain ⟨l, hl0, hl1⟩ : ∃ l : F, l ≠ 0 ∧ l ≠ 1 := by
    obtain ⟨s', hs'⟩ := exists_finset_fixedSubfield hK hm
    by_contra! hcon
    have hsub : s' ⊆ {0, 1} := fun a _ => by
      by_cases ha : a = 0
      · simp [ha]
      · simp [hcon a ha]
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le (0 : F) {1}
    rw [Finset.card_singleton] at h2
    omega
  have hl1' : (l : K) - 1 ≠ 0 := fun h0 => hl1 (Subtype.ext (by
    rw [sub_eq_zero] at h0
    simpa using h0))
  let dl : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![l, 0; 0, l⁻¹], by simp [det_fin_two, hl0]⟩
  have hDe : ((LF dl : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ e = (l : K) • e := by
    rw [hLFv, hypLeviMat_mulVec_left hee hfe]
    simp [dl]
  have hux₁ : hform h.bar u (((l : K) - 1) • e) = 0 := by rw [hform_smul_right, hue, mul_zero]
  have hxx₁ : hform h.bar (((l : K) - 1) • e) (((l : K) - 1) • e) = 0 := by
    rw [hform_smul_left, hform_smul_right, hee, mul_zero, mul_zero]
  have hcomm₁ : ⁅LF dl, sqZeroGL (uSiegel h.bar u e) (uSiegel_mul_self hσ huu hue hee)⁆ =
      sqZeroGL (uSiegel h.bar u (((l : K) - 1) • e)) (uSiegel_mul_self hσ huu hux₁ hxx₁) := by
    apply Units.ext
    have hc := conj_uSiegel (hLFadj dl) (hLFu dl) e
    rw [hDe] at hc
    have hm : uSiegel h.bar u ((l : K) • e) * uSiegel h.bar u e = 0 := by
      rw [uSiegel_mul hσ huu (by rw [hform_smul_right, hue, mul_zero]) hue, hform_smul_left, hee,
        mul_zero, zero_smul]
    have e1 : ((sqZeroGL (uSiegel h.bar u e) (uSiegel_mul_self hσ huu hue hee))⁻¹ :
        GL (Fin n) K) = (1 - uSiegel h.bar u e : Matrix (Fin n) (Fin n) K) := rfl
    rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, coe_sqZeroGL, e1,
      coe_sqZeroGL, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Units.mul_inv, hc,
      Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hm, sub_zero, sub_smul,
      one_smul, ← uSiegel_sub]
    abel
  have hx₁core : sqZeroGL (uSiegel h.bar u (((l : K) - 1) • e))
      (uSiegel_mul_self hσ huu hux₁ hxx₁) ∈
        perfectCore (StatedSU n (2 ^ m) K ⊓ centralizer ({M} : Set (GL (Fin n) K))) :=
    hcomm₁ ▸ commutatorElement_mem_perfectCore' (hρ hue hee) (hLcore ⟨dl, rfl⟩)
  obtain ⟨δ, hδ⟩ := htr (c * ((l : K) - 1)⁻¹) (by rw [map_mul, map_inv₀, map_sub, map_one, hσc,
    hFσ])
  have hux₂ : hform h.bar u (δ • f) = 0 := by rw [hform_smul_right, huf, mul_zero]
  have hxx₂ : hform h.bar (δ • f) (δ • f) = 0 := by
    rw [hform_smul_left, hform_smul_right, hff, mul_zero, mul_zero]
  have hMc : M = ⁅sqZeroGL (uSiegel h.bar u (((l : K) - 1) • e))
      (uSiegel_mul_self hσ huu hux₁ hxx₁),
      sqZeroGL (uSiegel h.bar u (δ • f)) (uSiegel_mul_self hσ huu hux₂ hxx₂)⁆ := by
    apply Units.ext
    rw [commutatorElement_uSiegel hσ huu hux₁ hux₂, hMT]
    congr 2
    rw [hform_smul_left, hform_smul_right, hform_smul_left, hform_smul_right, hef, hfe, map_sub,
      map_one, hFσ]
    linear_combination (-((l : K) - 1)) * hδ - c * mul_inv_cancel₀ hl1' +
      ((l : K) - 1) * h.bar δ * CharTwo.two_eq_zero (R := K)
  have h1 := commutatorElement_mem_perfectCore' (hρ hux₂ hxx₂) hx₁core
  rwa [← hMc] at h1

theorem unitaryTransvectionPerfect : UnitaryTransvectionPerfect := by
  intro n m K _ _ hn hq hK M hM hM2 hr
  have hm : 2 ≤ m := by
    by_contra h
    have h1 : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact mem_perfectCore_of_unitary_transvection hn hm hK hM hM2 hr

theorem classicalPrimaryPerfect : ClassicalPrimaryPerfect :=
  classicalPrimaryPerfect_of_unitary_orthogonal unitaryTransvectionPerfect
    orthogonalSingularPerfect

end CFSG.ComponentClassification.RankTwoClassical
