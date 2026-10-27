module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangUnitFix
public import CFSG.LieType.Steinberg.CentralExt.HermitianBasis

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open Matrix CFSG.HardMathSupport.Foote.ModuleExclusions CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg

variable {K : Type} [Field K]

theorem exists_unit_norm_prod [Finite K] {σ bar : K ≃+* K} (hbar : IsUnitaryInvolution bar)
    (hcomm : ∀ x, σ (bar x) = bar (σ x)) (hE1 : ∃ x, σ x = x ∧ bar x ≠ x) {c : K}
    (hσc : σ c = c) (hc : bar c * c = 1) :
    ∃ t : K, t ≠ 0 ∧ bar t * t = 1 ∧ ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) t = c := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have hpow : ∀ (i : ℕ) (x : K), (σ ^ i) (bar x) = bar ((σ ^ i) x) := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ i ih => intro x; simp only [pow_succ', RingAut.mul_apply, ih, hcomm]
  obtain ⟨x, hxσ, hρ0⟩ : ∃ x, σ x = x ∧ x + c * bar x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 : c = -1 := by
      have := hcon 1 (map_one σ)
      rw [map_one, mul_one] at this
      linear_combination this
    obtain ⟨x₁, hx₁σ, hx₁b⟩ := hE1
    apply hx₁b
    have := hcon x₁ hx₁σ
    rw [h1] at this
    linear_combination (-1 : K) * this
  set ρ := x + c * bar x with hρ
  have hσρ : σ ρ = ρ := by
    rw [hρ, map_add, map_mul, hxσ, hσc, hcomm, hxσ]
  have hcρ : c * bar ρ = ρ := by
    rw [hρ, map_add, map_mul, hbar.invol]
    linear_combination x * hc
  have hbρ0 : bar ρ ≠ 0 := fun h => hρ0 (by simpa using (map_eq_zero_iff bar bar.injective).1 h)
  obtain ⟨κ, hκ0, hκ⟩ := exists_prod_pow_eq σ ρ hσρ hρ0
  have hbκ0 : bar κ ≠ 0 := fun h => hκ0 ((map_eq_zero_iff bar bar.injective).1 h)
  refine ⟨κ * (bar κ)⁻¹, mul_ne_zero hκ0 (inv_ne_zero hbκ0), ?_, ?_⟩
  · rw [map_mul, map_inv₀, hbar.invol]
    field_simp
  · simp only [map_mul, map_inv₀, Finset.prod_mul_distrib, Finset.prod_inv_distrib, hpow, ← map_prod, hκ]
    exact (mul_inv_eq_iff_eq_mul₀ hbρ0).2 hcρ.symm

variable {d : ℕ}

theorem conjTr_conjTr' (bar : K ≃+* K) (hbb : ∀ x, bar (bar x) = x) (M : Matrix (Fin d) (Fin d) K) :
    conjTr bar (conjTr bar M) = M := by
  ext i j
  simp [conjTr, hbb]

theorem conjTr_smul' (bar : K ≃+* K) (c : K) (M : Matrix (Fin d) (Fin d) K) :
    conjTr bar (c • M) = bar c • conjTr bar M := by
  ext i j
  simp [conjTr]

theorem map_conjTr (bar σ : K ≃+* K) (hcomm : ∀ x, σ (bar x) = bar (σ x)) (M : Matrix (Fin d) (Fin d) K) :
    (conjTr bar M).map σ = conjTr bar (M.map σ) := by
  ext i j
  simp [conjTr, hcomm]

theorem fixed_of_Ai_scalar [Finite K] [NeZero d] (σ : K ≃+* K) (M : Matrix (Fin d) (Fin d) K)
    (hM : M.det ≠ 0) (c : K) (hc : Ai σ M (orderOf σ) = c • (1 : Matrix (Fin d) (Fin d) K)) : σ c = c := by
  set r := orderOf σ with hr
  have hσr : σ ^ r = 1 := by rw [hr]; exact pow_orderOf_eq_one σ
  have h1 : Ai σ M (r + 1) = σ c • M := by
    have : Ai σ M (r + 1) = M * (Ai σ M r).map σ := rfl
    rw [this, hc]
    ext i j
    simp [Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, apply_ite σ, mul_ite,
      mul_comm]
  have h2 : Ai σ M (r + 1) = c • M := by
    rw [Ai_succ_right, hc, hσr]
    ext i j
    simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
  rw [h1] at h2
  by_contra hne
  have hdiff : σ c - c ≠ 0 := sub_ne_zero.mpr hne
  have hA' : M = 0 := by
    ext i j
    have := congrFun (congrFun h2 i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    have h3 : (σ c - c) * M i j = 0 := by linear_combination this
    simpa [hdiff] using h3
  rw [hA'] at hM
  haveI : Nonempty (Fin d) := ⟨0⟩
  have : (0 : Matrix (Fin d) (Fin d) K).det = 0 := Matrix.det_zero
  exact hM this

theorem conjTr_Ai_mul (bar σ : K ≃+* K) (hcomm : ∀ x, σ (bar x) = bar (σ x)) (M : Matrix (Fin d) (Fin d) K)
    (hM : conjTr bar M * M = 1) (k : ℕ) : conjTr bar (Ai σ M k) * Ai σ M k = 1 := by
  induction k with
  | zero => simp [Ai, conjTr_one]
  | succ k ih =>
    change conjTr bar (M * (Ai σ M k).map σ) * (M * (Ai σ M k).map σ) = 1
    rw [conjTr_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (conjTr bar M), hM, Matrix.one_mul,
      ← map_conjTr bar σ hcomm, ← Matrix.map_mul, ih]
    simp

theorem map_conjTr_fix {σ bar : K ≃+* K} (hcomm : ∀ x, σ (bar x) = bar (σ x)) (hbb : ∀ x, bar (bar x) = x)
    (X : Matrix (Fin d) (Fin d) (fixField σ)) :
    (conjTr (barFix σ bar hcomm hbb) X).map (fixField σ).subtype =
      conjTr bar (X.map (fixField σ).subtype) := by
  ext i j
  simp [conjTr, coe_barFix]

theorem exists_fixed_orthonormal {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hK : Nat.card K = p ^ e)
    {σ bar : K ≃+* K} (hbar : IsUnitaryInvolution bar) (hcomm : ∀ x, σ (bar x) = bar (σ x))
    (hodd : Odd (orderOf σ)) {H : Matrix (Fin d) (Fin d) K} (hσ : H.map σ = H)
    (hH : conjTr bar H = H) (hdet : H.det ≠ 0) :
    ∃ P : GL (Fin d) K, glMap σ P = P ∧
      conjTr bar (P : Matrix (Fin d) (Fin d) K) * H * (P : Matrix (Fin d) (Fin d) K) = 1 := by
  have hbF := isUnitaryInvolution_barFix hp he hK hbar hcomm hodd
  set H₀ : Matrix (Fin d) (Fin d) (fixField σ) :=
    Matrix.of fun i j => ⟨H i j, mem_fixField.2 (congrFun (congrFun hσ i) j)⟩ with hH₀def
  have hH₀ : H₀.map (fixField σ).subtype = H := by
    ext i j
    rfl
  have hinj : Function.Injective fun N : Matrix (Fin d) (Fin d) (fixField σ) =>
      N.map (fixField σ).subtype := Matrix.map_injective (fixField σ).subtype_injective
  have hherm : conjTr (barFix σ bar hcomm hbar.invol) H₀ = H₀ := by
    apply hinj
    show (conjTr (barFix σ bar hcomm hbar.invol) H₀).map (fixField σ).subtype = H₀.map (fixField σ).subtype
    rw [map_conjTr_fix, hH₀, hH]
  have hdet₀ : H₀.det ≠ 0 := by
    intro h
    apply hdet
    rw [← hH₀, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
  obtain ⟨P₀, hP₀⟩ := exists_conjTr_mul_mul_eq_one_of_isUnitaryInvolution hbF hherm hdet₀
  refine ⟨glFixEmb σ P₀, mem_glFix.1 (glFixEmb_mem σ P₀), ?_⟩
  have h1 : ((glFixEmb σ P₀ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (P₀ : Matrix (Fin d) (Fin d) (fixField σ)).map (fixField σ).subtype := by
    ext i j
    rw [glFixEmb_apply]
    rfl
  have h2 := congrArg (fun N : Matrix (Fin d) (Fin d) (fixField σ) => N.map (fixField σ).subtype) hP₀
  simp only [Matrix.map_mul, map_conjTr_fix, hH₀] at h2
  rw [h1]
  simpa using h2

theorem coe_scalar_mul (l : Kˣ) (A : GL (Fin d) K) :
    ((Matrix.GeneralLinearGroup.scalar (Fin d) l * A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (l : K) • (A : Matrix (Fin d) (Fin d) K) := by
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.mul_apply]

theorem exists_unitary_cocycle {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hK : Nat.card K = p ^ e)
    {σ bar : K ≃+* K} (hbar : IsUnitaryInvolution bar) (hcomm : ∀ x, σ (bar x) = bar (σ x))
    (hodd : Odd (orderOf σ)) [NeZero d] (A : GL (Fin d) K) {μ c : K} (hμ : bar μ = μ) (hμ0 : μ ≠ 0)
    (hA : conjTr bar (A : Matrix (Fin d) (Fin d) K) * (A : Matrix (Fin d) (Fin d) K) = μ • 1)
    (hc : Ai σ (A : Matrix (Fin d) (Fin d) K) (orderOf σ) = c • (1 : Matrix (Fin d) (Fin d) K)) :
    ∃ (u : GL (Fin d) K) (l : Kˣ),
      conjTr bar (u : Matrix (Fin d) (Fin d) K) * (u : Matrix (Fin d) (Fin d) K) = 1 ∧
      Matrix.GeneralLinearGroup.scalar (Fin d) l * A = u⁻¹ * glMap σ u := by
  haveI : Finite K := CFSG.Semidihedral.FixedFieldData.finite_of_prime_power_card K hp hK
  haveI : Nonempty (Fin d) := ⟨0⟩
  have hbb := hbar.invol
  have hbne : bar ≠ 1 := by
    obtain ⟨c', hc'⟩ := hbar.exists_ne
    intro h
    exact hc' (by rw [h]; rfl)
  have hE1 : ∃ x, σ x = x ∧ bar x ≠ x :=
    exists_fixed_ne_of_odd hp he hK σ bar (RingEquiv.ext hbb) hbne hodd
  set Am : Matrix (Fin d) (Fin d) K := (A : Matrix (Fin d) (Fin d) K) with hAm
  obtain ⟨l₁, hl₁⟩ := hbar.exists_norm (d := μ⁻¹) (by rw [map_inv₀, hμ])
  have hl₁0 : l₁ ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hl₁
    exact (inv_ne_zero hμ0) hl₁.symm
  set A₁ : Matrix (Fin d) (Fin d) K := l₁ • Am with hA₁
  have hA₁iso : conjTr bar A₁ * A₁ = 1 := by
    rw [hA₁, conjTr_smul' bar, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hA, smul_smul, hl₁,
      inv_mul_cancel₀ hμ0, one_smul]
  have hdet : Am.det ≠ 0 := A.det_ne_zero
  have hA₁det : A₁.det ≠ 0 := by
    rw [hA₁, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hl₁0) hdet
  set m := orderOf σ with hm
  set N₁ : K := ∏ i ∈ Finset.range m, (σ ^ i) l₁ with hN₁
  have hAi₁ : Ai σ A₁ m = (N₁ * c) • (1 : Matrix (Fin d) (Fin d) K) := by
    rw [hA₁, Ai_smul, hc, smul_smul]
  set c₁ := N₁ * c with hc₁
  have hc₁σ : σ c₁ = c₁ := fixed_of_Ai_scalar σ A₁ hA₁det c₁ hAi₁
  have hc₁n : bar c₁ * c₁ = 1 := by
    have h := conjTr_Ai_mul bar σ hcomm A₁ hA₁iso m
    rw [hAi₁, conjTr_smul' bar, Matrix.smul_mul, Matrix.mul_smul, smul_smul, conjTr_one,
      Matrix.one_mul] at h
    have := congrFun (congrFun h 0) 0
    simpa using this
  have hc₁0 : c₁ ≠ 0 := by
    intro h
    rw [h, map_zero, zero_mul] at hc₁n
    exact zero_ne_one hc₁n
  obtain ⟨t, ht0, htn, htN⟩ := exists_unit_norm_prod hbar hcomm hE1 hc₁σ hc₁n
  rw [← hm] at htN
  have hl : t⁻¹ * l₁ ≠ 0 := mul_ne_zero (inv_ne_zero ht0) hl₁0
  set A₂g : GL (Fin d) K := Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 (t⁻¹ * l₁) hl) * A with hA₂g
  have hA₂ : (A₂g : Matrix (Fin d) (Fin d) K) = t⁻¹ • A₁ := by
    rw [hA₂g, coe_scalar_mul, Units.val_mk0, hA₁, smul_smul]
  have hAi₂ : Ai σ (A₂g : Matrix (Fin d) (Fin d) K) m = 1 := by
    rw [hA₂, Ai_smul, hAi₁, smul_smul]
    have : ∏ i ∈ Finset.range m, (σ ^ i) t⁻¹ = c₁⁻¹ := by
      simp only [map_inv₀, Finset.prod_inv_distrib, htN]
    rw [this, inv_mul_cancel₀ hc₁0, one_smul]
  have hA₂iso : conjTr bar (A₂g : Matrix (Fin d) (Fin d) K) * (A₂g : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [hA₂, conjTr_smul' bar, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hA₁iso]
    have : bar t⁻¹ * t⁻¹ = 1 := by
      rw [map_inv₀, ← mul_inv, htn, inv_one]
    rw [this, one_smul]
  have hnp : normProd σ A₂g m = 1 := by
    apply Units.ext
    rw [coe_normProd, hAi₂]
    rfl
  obtain ⟨y, hy⟩ := exists_inv_mul_glMap σ A₂g hnp
  set Bg : GL (Fin d) K := y⁻¹ with hBg
  have hBgrel : A₂g * glMap σ Bg = Bg := by
    rw [hy, hBg, map_inv]
    group
  set Bm : Matrix (Fin d) (Fin d) K := (Bg : Matrix (Fin d) (Fin d) K) with hBm
  have hBm' : Bm = (A₂g : Matrix (Fin d) (Fin d) K) * Bm.map σ := by
    have := congrArg (fun z : GL (Fin d) K => (z : Matrix (Fin d) (Fin d) K)) hBgrel
    simpa [Units.val_mul, coe_glMap] using this.symm
  set H : Matrix (Fin d) (Fin d) K := conjTr bar Bm * Bm with hH
  have hHσ : H.map σ = H := by
    calc H.map σ = conjTr bar (Bm.map σ) * Bm.map σ := by
          rw [hH, Matrix.map_mul, map_conjTr bar σ hcomm]
      _ = conjTr bar ((A₂g : Matrix (Fin d) (Fin d) K) * Bm.map σ) *
            ((A₂g : Matrix (Fin d) (Fin d) K) * Bm.map σ) := by
          rw [conjTr_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (conjTr bar (A₂g : Matrix (Fin d) (Fin d) K)),
            hA₂iso, Matrix.one_mul]
      _ = H := by rw [← hBm']
  have hHherm : conjTr bar H = H := by rw [hH, conjTr_mul, conjTr_conjTr' bar hbb]
  have hHdet : H.det ≠ 0 := by
    rw [hH, Matrix.det_mul]
    refine mul_ne_zero ?_ Bg.det_ne_zero
    have h1 : (Bm.map bar).det = bar Bm.det := (RingHom.map_det (bar : K →+* K) Bm).symm
    rw [conjTr, Matrix.det_transpose, h1]
    exact fun h => Bg.det_ne_zero ((map_eq_zero_iff bar bar.injective).1 h)
  obtain ⟨P, hPσ, hPH⟩ := exists_fixed_orthonormal hp he hK hbar hcomm hodd hHσ hHherm hHdet
  set W : GL (Fin d) K := Bg * P with hW
  have hWiso : conjTr bar (W : Matrix (Fin d) (Fin d) K) * (W : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [hW, Units.val_mul, conjTr_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (conjTr bar Bm),
      ← hH, ← Matrix.mul_assoc, hPH]
  have hWσ : A₂g * glMap σ W = W := by
    rw [hW, map_mul, hPσ, ← mul_assoc, hBgrel]
  refine ⟨W⁻¹, Units.mk0 (t⁻¹ * l₁) hl, ?_, ?_⟩
  · have h1 : conjTr bar (W : Matrix (Fin d) (Fin d) K) = ((W⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
      calc conjTr bar (W : Matrix (Fin d) (Fin d) K)
          = conjTr bar (W : Matrix (Fin d) (Fin d) K) *
              ((W : Matrix (Fin d) (Fin d) K) * ((W⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
        _ = (conjTr bar (W : Matrix (Fin d) (Fin d) K) * (W : Matrix (Fin d) (Fin d) K)) *
              ((W⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by rw [Matrix.mul_assoc]
        _ = ((W⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by rw [hWiso, Matrix.one_mul]
    have h2 : conjTr bar ((W⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        (W : Matrix (Fin d) (Fin d) K) := by
      rw [← h1, conjTr_conjTr' bar hbb]
    rw [h2, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  · rw [inv_inv, map_inv]
    exact eq_mul_inv_of_mul_eq hWσ

end CFSG.LieType.SemisimpleCentralizers.HeldLang
