module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bThree
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent

public section

namespace CFSG.QuasithinUnique.Setup.X5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

section Matrices

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem glAut_bar_glAut_bar (g : GL (Fin 3) K) :
    glAut (unitaryBarEquiv h) (glAut (unitaryBarEquiv h) g) = g := by
  rw [← MulAut.mul_apply, ← map_mul, unitaryBarEquiv_mul_self, map_one, MulAut.one_apply]

theorem coe_glAut_bar (g : GL (Fin 3) K) :
    ((glAut (unitaryBarEquiv h) g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (g : Matrix (Fin 3) (Fin 3) K).map h.bar := rfl

theorem cP_mul_self : (cP : Matrix (Fin 3) (Fin 3) K) * cP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cP]

theorem cP_transpose : (cP : Matrix (Fin 3) (Fin 3) K)ᵀ = cP := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cP]

variable {h}

@[expose] def gT1 (h2 : (2 : K) = 0) (a : K) : GL (Fin 3) K := invGL (cT1 a) (cT1_sq a h2)
@[expose] def gT2 (h2 : (2 : K) = 0) (a b : K) : GL (Fin 3) K := invGL (cT2 a b) (cT2_sq a b h2)
@[expose] def gT3 (h2 : (2 : K) = 0) (b : K) : GL (Fin 3) K := invGL (cT3 b) (cT3_sq b h2)
@[expose] def gP : GL (Fin 3) K := invGL cP cP_mul_self
@[expose] def gG (h2 : (2 : K) = 0) (a b : K) : GL (Fin 3) K := gT1 h2 a * gT2 h2 a b * gT3 h2 b

theorem coe_gG (h2 : (2 : K) = 0) (a b : K) :
    ((gG h2 a b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = cG a b := rfl

theorem gT1_mul_self (h2 : (2 : K) = 0) (a : K) : gT1 h2 a * gT1 h2 a = 1 := invGL_mul_self _ _
theorem gT2_mul_self (h2 : (2 : K) = 0) (a b : K) : gT2 h2 a b * gT2 h2 a b = 1 :=
  invGL_mul_self _ _
theorem gT3_mul_self (h2 : (2 : K) = 0) (b : K) : gT3 h2 b * gT3 h2 b = 1 := invGL_mul_self _ _
theorem gP_mul_self : (gP : GL (Fin 3) K) * gP = 1 := invGL_mul_self _ _

theorem gG_inv (h2 : (2 : K) = 0) (a b : K) :
    (gG h2 a b)⁻¹ = gT3 h2 b * gT2 h2 a b * gT1 h2 a := by
  rw [gG, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_eq_of_mul_eq_one_right (gT1_mul_self h2 a),
    inv_eq_of_mul_eq_one_right (gT2_mul_self h2 a b),
    inv_eq_of_mul_eq_one_right (gT3_mul_self h2 b), mul_assoc]

theorem gP_inv : (gP : GL (Fin 3) K)⁻¹ = gP := inv_eq_of_mul_eq_one_right gP_mul_self

theorem gP_glAut_gT1 (h2 : (2 : K) = 0) {a b : K} (hb : b = h.bar a) :
    gP * glAut (unitaryBarEquiv h) (gT1 h2 a) * gP = gT3 h2 b := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_glAut_bar]
  change cP * (cT1 a).map h.bar * cP = cT3 b
  rw [map_cT1, ← hb]
  exact cP_cT1_cP b

theorem gP_glAut_gT2 (h2 : (2 : K) = 0) {a b : K} (hb : b = h.bar a) (hbb : h.bar b = a) :
    gP * glAut (unitaryBarEquiv h) (gT2 h2 a b) * gP = gT2 h2 a b := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_glAut_bar]
  change cP * (cT2 a b).map h.bar * cP = cT2 a b
  rw [map_cT2, ← hb, hbb]
  exact cP_cT2_cP a b

theorem gP_glAut_gT3 (h2 : (2 : K) = 0) {a b : K} (hbb : h.bar b = a) :
    gP * glAut (unitaryBarEquiv h) (gT3 h2 b) * gP = gT1 h2 a := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_glAut_bar]
  change cP * (cT3 b).map h.bar * cP = cT1 a
  rw [map_cT3, hbb]
  exact cP_cT3_cP a

theorem gP_glAut_gG (h2 : (2 : K) = 0) {a b : K} (hb : b = h.bar a) (hbb : h.bar b = a) :
    gP * glAut (unitaryBarEquiv h) (gG h2 a b) * gP = (gG h2 a b)⁻¹ := by
  have e : ∀ X Y : GL (Fin 3) K, gP * (X * Y) * gP = (gP * X * gP) * (gP * Y * gP) := by
    intro X Y
    calc gP * (X * Y) * gP = gP * X * (gP * gP) * Y * gP := by
          rw [gP_mul_self, mul_one]; simp only [mul_assoc]
      _ = (gP * X * gP) * (gP * Y * gP) := by simp only [mul_assoc]
  rw [gG_inv, gG, map_mul, map_mul, e, e, gP_glAut_gT1 h2 hb, gP_glAut_gT2 h2 hb hbb,
    gP_glAut_gT3 h2 hbb]

theorem cG_ne_one {a b : K} (hne : a ^ 2 + b ^ 2 ≠ 0) (h2 : (2 : K) = 0) : cG a b ≠ 1 := by
  intro hmat
  have := cG_charpoly a b h2
  rw [hmat] at this
  have h00 := congrFun (congrFun this 0) 0
  simp at h00
  apply hne
  linear_combination h00 - h2

theorem coe_unitaryBarEquiv : (⇑(unitaryBarEquiv h) : K → K) = ⇑h.bar := rfl

theorem A_mem_primeFormUnitary {a b : K} (hb : b = h.bar a) (hbb : h.bar b = a) {H : GL (Fin 3) K}
    (hH : ((H : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * cM a b * H = 1) :
    H⁻¹ * gP * glAut (unitaryBarEquiv h) H ∈
      primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [mem_primeFormUnitary]
  have e1 := inv_gram_eq h hH
  have e2 : (((H : Matrix (Fin 3) (Fin 3) K).map h.bar).map h.bar)ᵀ * cM b a *
      (H : Matrix (Fin 3) (Fin 3) K).map h.bar = 1 := by
    have := map_barTranspose_mul_mul h (unitaryBarEquiv h) (cM a b) (H : Matrix (Fin 3) (Fin 3) K)
    rw [hH] at this
    simp only [coe_unitaryBarEquiv] at this
    rw [map_cM, ← hb, hbb] at this
    rw [this, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]
  have hPm : ((gP : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = cP := rfl
  rw [Units.val_mul, Units.val_mul, conjTranspose_mul_mul, conjTranspose_mul_mul, Units.val_one,
    e1, hPm, map_cP, cP_transpose, cP_cM_cP, coe_glAut_bar]
  exact e2

theorem gT1_mem_gramSU (h2 : (2 : K) = 0) {a b : K} (hb : b = h.bar a) :
    gT1 h2 a ∈ gramSU h (cM a b) := by
  refine mem_gramSU.mpr ⟨?_, ?_⟩
  · change ((cT1 a).map h.bar)ᵀ * cM a b * cT1 a = cM a b
    rw [map_cT1, ← hb]
    exact cT1_iso a b h2
  · exact det_cT1 a

theorem gT2_mem_gramSU (h2 : (2 : K) = 0) {a b : K} (hb : b = h.bar a) (hbb : h.bar b = a) :
    gT2 h2 a b ∈ gramSU h (cM a b) := by
  refine mem_gramSU.mpr ⟨?_, ?_⟩
  · change ((cT2 a b).map h.bar)ᵀ * cM a b * cT2 a b = cM a b
    rw [map_cT2, ← hb, hbb]
    exact cT2_iso a b h2
  · exact det_cT2 a b

theorem gT3_mem_gramSU (h2 : (2 : K) = 0) {a b : K} (hbb : h.bar b = a) :
    gT3 h2 b ∈ gramSU h (cM a b) := by
  refine mem_gramSU.mpr ⟨?_, ?_⟩
  · change ((cT3 b).map h.bar)ᵀ * cM a b * cT3 b = cM a b
    rw [map_cT3, hbb]
    exact cT3_iso a b h2
  · exact det_cT3 b

theorem gG_mem_gramSU (h2 : (2 : K) = 0) {a b : K} (hb : b = h.bar a) (hbb : h.bar b = a) :
    gG h2 a b ∈ gramSU h (cM a b) :=
  mul_mem (mul_mem (gT1_mem_gramSU h2 hb) (gT2_mem_gramSU h2 hb hbb)) (gT3_mem_gramSU h2 hbb)

theorem glAut_gP : glAut (unitaryBarEquiv h) (gP : GL (Fin 3) K) = gP := by
  apply Units.ext
  rw [coe_glAut_bar]
  exact map_cP h

theorem exists_model (hf : 2 ≤ f) {ℓ : ℕ} (hℓ : ℓ.Prime) (hord : orderOf (2 : ZMod ℓ) = 6 * f) :
    ∃ A g : GL (Fin 3) K,
      A ∈ primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∧
      g ∈ gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∧
      A * glAut (unitaryBarEquiv h) A = 1 ∧
      A * glAut (unitaryBarEquiv h) g * A⁻¹ = g⁻¹ ∧ g ^ ℓ = 1 ∧ g ≠ 1 := by
  have hK2 : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨a, b, H, hb, hbb, ha0, hb0, hne, hGℓ, hH⟩ := exists_setup hf h hℓ hord
  have hgG := gG_mem_gramSU (h := h) h2 hb hbb
  refine ⟨H⁻¹ * gP * glAut (unitaryBarEquiv h) H, H⁻¹ * gG h2 a b * H,
    A_mem_primeFormUnitary hb hbb hH, ?_, ?_, ?_, ?_, ?_⟩
  · have := conj_mem_gramSU_of_gram h (inv_gram_eq h hH) hgG
    rw [inv_inv] at this
    exact this
  · rw [map_mul, map_mul, map_inv, glAut_bar_glAut_bar, glAut_gP]
    calc H⁻¹ * gP * glAut (unitaryBarEquiv h) H *
          ((glAut (unitaryBarEquiv h) H)⁻¹ * gP * H) = H⁻¹ * (gP * gP) * H := by group
      _ = 1 := by rw [gP_mul_self]; group
  · rw [map_mul, map_mul, map_inv]
    calc H⁻¹ * gP * glAut (unitaryBarEquiv h) H * ((glAut (unitaryBarEquiv h) H)⁻¹ *
          glAut (unitaryBarEquiv h) (gG h2 a b) * glAut (unitaryBarEquiv h) H) *
          (H⁻¹ * gP * glAut (unitaryBarEquiv h) H)⁻¹ =
        H⁻¹ * (gP * glAut (unitaryBarEquiv h) (gG h2 a b) * gP⁻¹) * H := by group
      _ = H⁻¹ * (gG h2 a b)⁻¹ * H := by rw [gP_inv, gP_glAut_gG h2 hb hbb]
      _ = (H⁻¹ * gG h2 a b * H)⁻¹ := by group
  · have hGpow : (gG h2 a b) ^ ℓ = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, coe_gG, hGℓ]
      rfl
    have : H⁻¹ * gG h2 a b * H = H⁻¹ * gG h2 a b * H⁻¹⁻¹ := by rw [inv_inv]
    rw [this, conj_pow, hGpow, mul_one, mul_inv_cancel]
  · intro h0
    apply cG_ne_one hne h2
    have h1 : gG h2 a b = 1 := by
      calc gG h2 a b = H * (H⁻¹ * gG h2 a b * H) * H⁻¹ := by group
        _ = 1 := by rw [h0]; group
    exact congrArg Units.val h1

end Matrices

section Aut

open CFSG.ComponentClassification

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem not_three_two_of_two_le (hf : 2 ≤ f) : ¬((3 : ℕ) = 3 ∧ 2 ^ f = 2) := by
  rintro ⟨-, h2⟩
  have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

theorem exists_conj_fieldBar (hf : 2 ≤ f)
    (β : MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))
    (hβ2 : β * β = 1)
    (hfac : ∀ x, primeFormFieldFactor h (isPrimeFormGram_one' (K := K) (n := 3)) (le_refl 3)
      (not_three_two_of_two_le hf) β x = h.bar x) :
    ∃ θ : primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≃*
        primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
      ∀ x, β x = θ (primeFormFieldAut h (isPrimeFormGram_one' (K := K) (n := 3))
        (unitaryBarEquiv h) (θ.symm x)) := by
  have hq := not_three_two_of_two_le hf
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one'
  have hβ1 : β ≠ 1 := by
    intro h0
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    apply hc
    have := hfac c
    rw [h0, map_one] at this
    exact this.symm
  have hord : orderOf β = 2 := orderOf_eq_prime (by rw [sq]; exact hβ2) hβ1
  obtain ⟨A, H, C₀, hC₀, hC₀form, hΨ, hA1, hHC, hHv, ⟨θ, hθ1, hθ2⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent h hC (le_refl 3) hq β hord hfac
  have hC₀1 : C₀ = 1 := by
    rcases hC₀form with h1 | ⟨r, hr, -⟩
    · exact Units.ext (by rw [h1, Units.val_one])
    · omega
  subst hC₀1
  have hφ : primeFormFieldFactor h hC (le_refl 3) hq β = unitaryBarEquiv h := RingEquiv.ext hfac
  refine ⟨θ, fun x => ?_⟩
  rw [hθ2 x, hφ]

theorem exists_model_aut (hf : 2 ≤ f) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3)
    (hord : orderOf (2 : ZMod ℓ) = 6 * f) :
    ∃ (α₀ : MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))
      (x : primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)),
      α₀ * α₀ = 1 ∧ (∀ y, primeFormFieldFactor h (isPrimeFormGram_one' (K := K) (n := 3))
        (le_refl 3) (not_three_two_of_two_le hf) α₀ y = h.bar y) ∧ orderOf x = ℓ ∧
        α₀ x = x⁻¹ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hq := not_three_two_of_two_le hf
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one'
  obtain ⟨A, g, hA, hg, hAA, hAg, hgℓ, hg1⟩ := exists_model (h := h) hf hℓ hord
  let AU : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := ⟨A, hA⟩
  let φ := unitaryBarEquiv h
  have hf2 : primeFormFieldHom h hC φ * primeFormFieldHom h hC φ = 1 := by
    rw [← map_mul, unitaryBarEquiv_mul_self, map_one]
  have hcomm : primeFormFieldHom h hC φ * primeFormConjHom h _ AU =
      primeFormConjHom h _ (primeFormFieldU h hC φ AU) * primeFormFieldHom h hC φ := by
    have key := primeFormField_conj_eq h hC φ AU
    rwa [mul_inv_eq_iff_eq_mul] at key
  have hAU : AU * primeFormFieldU h hC φ AU = 1 := Subtype.ext hAA
  refine ⟨primeFormConjHom h _ AU * primeFormFieldHom h hC φ,
    ((⟨g, hg⟩ : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) : primeFormP h _),
    ?_, ?_, ?_, ?_⟩
  · calc primeFormConjHom h _ AU * primeFormFieldHom h hC φ *
          (primeFormConjHom h _ AU * primeFormFieldHom h hC φ)
        = primeFormConjHom h _ AU * (primeFormFieldHom h hC φ * primeFormConjHom h _ AU) *
            primeFormFieldHom h hC φ := by simp only [mul_assoc]
      _ = primeFormConjHom h _ AU * (primeFormConjHom h _ (primeFormFieldU h hC φ AU) *
            primeFormFieldHom h hC φ) * primeFormFieldHom h hC φ := by rw [hcomm]
      _ = primeFormConjHom h _ (AU * primeFormFieldU h hC φ AU) *
            (primeFormFieldHom h hC φ * primeFormFieldHom h hC φ) := by
          rw [map_mul]; simp only [mul_assoc]
      _ = 1 := by rw [hAU, map_one, hf2, mul_one]
  · intro y
    rw [primeFormFieldFactor_apply h hC (le_refl 3) hq AU φ]
    rfl
  · have hxℓ : ((⟨g, hg⟩ : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
        primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ^ ℓ = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : (⟨g, hg⟩ : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ^ ℓ = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hgℓ)
      rw [this, QuotientGroup.mk_one]
    have hx1 : ((⟨g, hg⟩ : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
        primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ≠ 1 := by
      intro h0
      obtain ⟨c, -, hc3, hgc⟩ := (QuotientGroup.eq_one_iff _).mp h0
      apply hg1
      apply eq_one_of_pow_prime_of_pow_three hℓ hℓ3 hgℓ
      have hgc' : g = Matrix.GeneralLinearGroup.scalar (Fin 3) c := hgc
      rw [hgc', ← map_pow, hc3, map_one]
    exact orderOf_eq_prime hxℓ hx1
  · change primeFormConjHom h _ AU (primeFormFieldAut h hC φ
      ((⟨g, hg⟩ : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
        primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) = _
    rw [primeFormFieldAut_mk, primeFormConjHom_mk, ← QuotientGroup.mk_inv]
    congr 1
    apply Subtype.ext
    exact hAg

theorem outerInverter_holds : OuterInverter := by
  intro f hf K _ h ℓ hℓ _ hord α hα2 hαin
  have hℓ3 : ℓ ≠ 3 := ne_three_of_orderOf_two (by omega) hord
  have hq := not_three_two_of_two_le hf
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one'
  obtain ⟨e⟩ := nonempty_primeFormP_mulEquiv h hC
  obtain ⟨β, hβdef⟩ : ∃ β : MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)),
      β = (MulAut.congr e).symm α := ⟨_, rfl⟩
  have hβα : MulAut.congr e β = α := by rw [hβdef]; exact (MulAut.congr e).apply_symm_apply α
  have hβ2 : β * β = 1 := by rw [hβdef, ← map_mul, hα2, map_one]
  have hβin : β ∉ OuterAutomorphisms.inner
      (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
    intro hin
    apply hαin
    rw [← OuterAutomorphisms.inner_map_congr e]
    exact ⟨β, hin, hβα⟩
  have hβ1 : β ≠ 1 := fun h0 => hβin (by rw [h0]; exact one_mem _)
  have hord2 : orderOf β = 2 := orderOf_eq_prime (by rw [sq]; exact hβ2) hβ1
  obtain ⟨hfac1, hrefl, -, -⟩ := even_unitary_involution_matrix_lifts h hC (le_refl 3) hq β hord2
  have hfac : ∀ y, primeFormFieldFactor h hC (le_refl 3) hq β y = h.bar y := by
    rcases hfac1 with hr | hb
    · exfalso
      obtain ⟨s, -, -, hs⟩ := hrefl hr
      exact hβin ((mem_inner_primeFormP h _ β).mpr ⟨s, hs⟩)
    · exact hb
  obtain ⟨α₀, x₀, hα₀2, hα₀fac, hx₀, hα₀x₀⟩ := exists_model_aut h hf hℓ hℓ3 hord
  obtain ⟨θ₁, hθ₁⟩ := exists_conj_fieldBar h hf β hβ2 hfac
  obtain ⟨θ₀, hθ₀⟩ := exists_conj_fieldBar h hf α₀ hα₀2 hα₀fac
  have hy₀ : primeFormFieldAut h hC (unitaryBarEquiv h) (θ₀.symm x₀) = (θ₀.symm x₀)⁻¹ := by
    apply θ₀.injective
    have := hθ₀ x₀
    rw [hα₀x₀] at this
    rw [map_inv, θ₀.apply_symm_apply]
    exact this.symm
  refine ⟨e (θ₁ (θ₀.symm x₀)), ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, MulEquiv.orderOf_eq]
    exact hx₀
  · rw [← hβα]
    change e (β (e.symm (e (θ₁ (θ₀.symm x₀))))) = _
    rw [e.symm_apply_apply, hθ₁ (θ₁ (θ₀.symm x₀)), θ₁.symm_apply_apply, hy₀, map_inv, map_inv]

end Aut

end CFSG.QuasithinUnique.Setup.X5
