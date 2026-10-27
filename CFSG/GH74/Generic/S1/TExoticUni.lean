module

public import CFSG.GH74.Generic.S1.TExoticLin

public section

namespace CFSG.GH74.Generic.S1

open Matrix

section Aux

variable {F : Type} [Field F]

theorem gramForm_smul_left {G : Matrix (Fin 4) (Fin 4) F} (c : F) (x y : Fin 4 → F) :
    gramForm G (c • x) y = c * gramForm G x y := by
  unfold gramForm
  rw [smul_dotProduct, smul_eq_mul]

theorem gramForm_smul_right {G : Matrix (Fin 4) (Fin 4) F} (c : F) (x y : Fin 4 → F) :
    gramForm G x (c • y) = c * gramForm G x y := by
  unfold gramForm
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem bar_bar_of_card [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2) (bar : F →+* F)
    (hbar : ∀ x, bar x = x ^ q) (x : F) : bar (bar x) = x := by
  have := Fintype.ofFinite F
  have hc : Fintype.card F = q ^ 2 := by rw [← Nat.card_eq_fintype_card, hF]
  rw [hbar, hbar, ← pow_mul, ← sq, ← hc, FiniteField.pow_card]

theorem exists_bar_neg [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2) (hq : 2 ≤ q)
    (bar : F →+* F) (hbar : ∀ x, bar x = x ^ q) : ∃ θ : F, θ ≠ 0 ∧ bar θ = -θ := by
  have := Fintype.ofFinite F
  have hbb := bar_bar_of_card hF bar hbar
  obtain ⟨w, hw⟩ : ∃ w : F, bar w ≠ w := by
    by_contra hcon
    push Not at hcon
    have hcard := Polynomial.card_le_degree_of_subset_roots
      (p := (Polynomial.X ^ q - Polynomial.X : Polynomial F)) (Z := Finset.univ) (fun x _ => by
        rw [Polynomial.mem_roots', Polynomial.IsRoot.def]
        refine ⟨FiniteField.X_pow_card_sub_X_ne_zero F hq, ?_⟩
        simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
        rw [← hbar, hcon, sub_self])
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq F hq, Finset.card_univ,
      ← Nat.card_eq_fintype_card, hF] at hcard
    nlinarith
  refine ⟨w - bar w, sub_ne_zero.2 hw.symm, ?_⟩
  rw [map_sub, hbb, neg_sub]

@[expose] def uniSigma (bar : F →+* F) (G : Matrix (Fin 4) (Fin 4) F) (v : Fin 4 → F) :
    Fin 4 → F :=
  G.map bar *ᵥ (bar ∘ v)

variable {bar : F →+* F} {G : Matrix (Fin 4) (Fin 4) F}

theorem uniSigma_add (v w : Fin 4 → F) :
    uniSigma bar G (v + w) = uniSigma bar G v + uniSigma bar G w := by
  unfold uniSigma
  rw [← Matrix.mulVec_add]
  congr 1
  ext r
  simp

theorem uniSigma_neg (v : Fin 4 → F) : uniSigma bar G (-v) = -uniSigma bar G v := by
  unfold uniSigma
  rw [← Matrix.mulVec_neg]
  congr 1
  ext r
  simp

theorem uniSigma_sub (v w : Fin 4 → F) :
    uniSigma bar G (v - w) = uniSigma bar G v - uniSigma bar G w := by
  unfold uniSigma
  rw [← Matrix.mulVec_sub]
  congr 1
  ext r
  simp

theorem uniSigma_smul (c : F) (v : Fin 4 → F) :
    uniSigma bar G (c • v) = bar c • uniSigma bar G v := by
  unfold uniSigma
  rw [← Matrix.mulVec_smul]
  congr 1
  ext r
  simp

theorem bar_uniSigma (hbb : ∀ x, bar (bar x) = x) (v : Fin 4 → F) :
    bar ∘ uniSigma bar G v = G *ᵥ v := by
  ext r
  unfold uniSigma
  rw [Function.comp_apply, RingHom.map_mulVec]
  have h1 : (G.map bar).map bar = G := by
    ext i j
    simp [hbb]
  have h2 : bar ∘ (bar ∘ v) = v := by
    ext i
    simp [hbb]
  rw [h1, h2]

theorem mulVec_uniSigma (hGGb : G * G.map bar = 1) (v : Fin 4 → F) :
    G *ᵥ uniSigma bar G v = bar ∘ v := by
  unfold uniSigma
  rw [Matrix.mulVec_mulVec, hGGb, Matrix.one_mulVec]

theorem uniSigma_uniSigma (hbb : ∀ x, bar (bar x) = x) (hGbG : G.map bar * G = 1)
    (v : Fin 4 → F) : uniSigma bar G (uniSigma bar G v) = v := by
  show G.map bar *ᵥ (bar ∘ uniSigma bar G v) = v
  rw [bar_uniSigma hbb, Matrix.mulVec_mulVec, hGbG, Matrix.one_mulVec]

theorem uniSigma_mulVec (hbb : ∀ x, bar (bar x) = x) {d : Matrix (Fin 4) (Fin 4) F}
    (hd : G * d = d.map bar * G) (v : Fin 4 → F) :
    uniSigma bar G (d *ᵥ v) = d *ᵥ uniSigma bar G v := by
  have h1 : G.map bar * d.map bar = d * G.map bar := by
    have h := congrArg (fun M => M.map bar) hd
    simp only [Matrix.map_mul] at h
    have h2 : (d.map bar).map bar = d := by
      ext i j
      simp [hbb]
    rwa [h2] at h
  have h3 : bar ∘ (d *ᵥ v) = d.map bar *ᵥ (bar ∘ v) := by
    ext r
    exact RingHom.map_mulVec bar d v r
  unfold uniSigma
  rw [h3, Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec]

theorem mulVec_of_uniFixed (hGGb : G * G.map bar = 1) {y : Fin 4 → F}
    (hy : uniSigma bar G y = y) : G *ᵥ y = bar ∘ y := by
  have h := mulVec_uniSigma hGGb y
  rwa [hy] at h

theorem bar_gramForm_uniFixed (hbb : ∀ x, bar (bar x) = x) (hGGb : G * G.map bar = 1)
    {x : Fin 4 → F} (hx : uniSigma bar G x = x) : bar (gramForm G x x) = gramForm G x x := by
  have h := mulVec_of_uniFixed hGGb hx
  unfold gramForm
  rw [h, RingHom.map_dotProduct, dotProduct_comm]
  congr 1
  ext i
  simp [hbb]

theorem uniSigma_fixedParts (hbb : ∀ x, bar (bar x) = x) (hGbG : G.map bar * G = 1)
    {θ : F} (hθ : bar θ = -θ) {z : Matrix (Fin 4) (Fin 4) F}
    (hzs : ∀ v, uniSigma bar G (z *ᵥ v) = z *ᵥ uniSigma bar G v) {v : Fin 4 → F}
    (hv : z *ᵥ v = -v) :
    uniSigma bar G (v + uniSigma bar G v) = v + uniSigma bar G v ∧
    z *ᵥ (v + uniSigma bar G v) = -(v + uniSigma bar G v) ∧
    uniSigma bar G (θ • (v - uniSigma bar G v)) = θ • (v - uniSigma bar G v) ∧
    z *ᵥ (θ • (v - uniSigma bar G v)) = -(θ • (v - uniSigma bar G v)) := by
  have hzv : z *ᵥ uniSigma bar G v = -uniSigma bar G v := by
    rw [← hzs, hv, uniSigma_neg]
  have hss := uniSigma_uniSigma hbb hGbG v
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [uniSigma_add, hss, add_comm]
  · rw [Matrix.mulVec_add, hv, hzv, neg_add]
  · rw [uniSigma_smul, uniSigma_sub, hss, hθ]
    module
  · rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hv, hzv]
    module

theorem uniSigma_decompose (hbb : ∀ x, bar (bar x) = x) (hGbG : G.map bar * G = 1)
    {θ : F} (hθ0 : θ ≠ 0) (hθ : bar θ = -θ) {z : Matrix (Fin 4) (Fin 4) F}
    (hzs : ∀ v, uniSigma bar G (z *ᵥ v) = z *ᵥ uniSigma bar G v) {v : Fin 4 → F}
    (hv : z *ᵥ v = -v) :
    ∃ v₁ v₂ : Fin 4 → F, uniSigma bar G v₁ = v₁ ∧ z *ᵥ v₁ = -v₁ ∧
      uniSigma bar G v₂ = v₂ ∧ z *ᵥ v₂ = -v₂ ∧ (2 : F) • v = v₁ + θ⁻¹ • v₂ := by
  obtain ⟨h1, h2, h3, h4⟩ := uniSigma_fixedParts hbb hGbG hθ hzs hv
  refine ⟨_, _, h1, h2, h3, h4, ?_⟩
  rw [smul_smul, inv_mul_cancel₀ hθ0, one_smul]
  module

theorem exists_uniFixed_aniso_neg (hbb : ∀ x, bar (bar x) = x) (hGbG : G.map bar * G = 1)
    (h2 : (2 : F) ≠ 0) (hGs : Gᵀ = G) (hGd : G.det ≠ 0) {θ : F} (hθ0 : θ ≠ 0)
    (hθ : bar θ = -θ) {z : Matrix (Fin 4) (Fin 4) F} (hzG : zᵀ * G * z = G) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hzs : ∀ v, uniSigma bar G (z *ᵥ v) = z *ᵥ uniSigma bar G v) :
    ∃ x : Fin 4 → F, uniSigma bar G x = x ∧ z *ᵥ x = -x ∧ gramForm G x x ≠ 0 := by
  obtain ⟨u, w, hu, hw, hne⟩ := exists_pair_neg h2 hGs hGd hzG hz2 hz1
  by_contra hall
  push Not at hall
  have hpol : ∀ y y' : Fin 4 → F, uniSigma bar G y = y → z *ᵥ y = -y →
      uniSigma bar G y' = y' → z *ᵥ y' = -y' → gramForm G y y' = 0 := by
    intro y y' hy hzy hy' hzy'
    have e1 := hall y hy hzy
    have e2 := hall y' hy' hzy'
    have hs : uniSigma bar G (y + y') = y + y' := by rw [uniSigma_add, hy, hy']
    have hzs' : z *ᵥ (y + y') = -(y + y') := by rw [Matrix.mulVec_add, hzy, hzy', neg_add]
    have e3 := hall (y + y') hs hzs'
    rw [gramForm_add_left, gramForm_add_right, gramForm_add_right, e1, e2,
      gramForm_comm hGs y' y] at e3
    have : (2 : F) * gramForm G y y' = 0 := by linear_combination e3
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h h2
    · exact h
  obtain ⟨u₁, u₂, hu₁, hu₁z, hu₂, hu₂z, hue⟩ := uniSigma_decompose hbb hGbG hθ0 hθ hzs hu
  obtain ⟨w₁, w₂, hw₁, hw₁z, hw₂, hw₂z, hwe⟩ := uniSigma_decompose hbb hGbG hθ0 hθ hzs hw
  have h4 : gramForm G ((2 : F) • u) ((2 : F) • w) = 0 := by
    rw [hue, hwe]
    simp only [gramForm_add_left, gramForm_add_right, gramForm_smul_left, gramForm_smul_right,
      hpol _ _ hu₁ hu₁z hw₁ hw₁z, hpol _ _ hu₁ hu₁z hw₂ hw₂z, hpol _ _ hu₂ hu₂z hw₁ hw₁z,
      hpol _ _ hu₂ hu₂z hw₂ hw₂z]
    ring
  rw [gramForm_smul_left, gramForm_smul_right] at h4
  apply hne
  have h5 : (2 : F) * (2 * gramForm G u w) = 0 := h4
  rcases mul_eq_zero.1 h5 with h | h
  · exact absurd h h2
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h h2
  · exact h

end Aux

theorem no_q8_isometry_uni {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : 2 ≤ q) (h2 : (2 : F) ≠ 0) (bar : F →+* F) (hbar : ∀ x, bar x = x ^ q)
    {G a b z : Matrix (Fin 4) (Fin 4) F} (hGs : Gᵀ = G) (hGu : (G.map bar)ᵀ * G = 1)
    (hGd : ¬ ∃ u : F, u ^ (q + 1) = 1 ∧ u * u = G.det)
    (hGa : aᵀ * G * a = G) (hGb : bᵀ * G * b = G)
    (hσa : G * a = a.map bar * G) (hσb : G * b = b.map bar * G)
    (ha2 : a * a = z) (hb2 : b * b = z) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hab : a * b = z * (b * a)) : False := by
  have hbb := bar_bar_of_card hF bar hbar
  have hGbG : G.map bar * G = 1 := by
    have hT : (G.map bar)ᵀ = G.map bar := by rw [← Matrix.transpose_map, hGs]
    rwa [hT] at hGu
  have hGGb : G * G.map bar = 1 := mul_eq_one_comm.1 hGbG
  have hG0 : G.det ≠ 0 := by
    have h : (G.map bar).det * G.det = 1 := by rw [← Matrix.det_mul, hGbG, Matrix.det_one]
    exact right_ne_zero_of_mul_eq_one h
  have hzG : zᵀ * G * z = G := by
    rw [← ha2, Matrix.transpose_mul]
    calc aᵀ * aᵀ * G * (a * a) = aᵀ * (aᵀ * G * a) * a := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hGa, hGa]
  have hσz : G * z = z.map bar * G := by
    rw [← ha2]
    calc G * (a * a) = G * a * a := by rw [Matrix.mul_assoc]
      _ = a.map bar * G * a := by rw [hσa]
      _ = a.map bar * (G * a) := by rw [Matrix.mul_assoc]
      _ = a.map bar * (a.map bar * G) := by rw [hσa]
      _ = (a * a).map bar * G := by rw [Matrix.map_mul, Matrix.mul_assoc]
  have hzs : ∀ v, uniSigma bar G (z *ᵥ v) = z *ᵥ uniSigma bar G v := uniSigma_mulVec hbb hσz
  obtain ⟨θ, hθ0, hθ⟩ := exists_bar_neg hF hq bar hbar
  obtain ⟨x, hxσ, hxz, hxn⟩ :=
    exists_uniFixed_aniso_neg hbb hGbG h2 hGs hG0 hθ0 hθ hzG hz2 hz1 hzs
  have hPG := q8Frame_gram h2 hGs hGa hGb ha2 hb2 hz2 hab hxz
  set β := gramForm G x x with hβ
  set P := q8Frame a b x with hP
  have hdet : G.det * P.det ^ 2 = β ^ 4 := by
    have h1 := congrArg Matrix.det hPG
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one] at h1
    simp only [Fintype.card_fin, mul_one] at h1
    linear_combination h1
  have hP0 : P.det ≠ 0 := by
    intro h
    rw [h] at hdet
    simp at hdet
    exact hxn ((pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).1 hdet.symm)
  have hxa : uniSigma bar G (a *ᵥ x) = a *ᵥ x := by rw [uniSigma_mulVec hbb hσa, hxσ]
  have hxb : uniSigma bar G (b *ᵥ x) = b *ᵥ x := by rw [uniSigma_mulVec hbb hσb, hxσ]
  have hxab : uniSigma bar G ((a * b) *ᵥ x) = (a * b) *ᵥ x := by
    rw [← Matrix.mulVec_mulVec, uniSigma_mulVec hbb hσa, uniSigma_mulVec hbb hσb, hxσ]
  have hcol : ∀ k, uniSigma bar G (fun s => P s k) = fun s => P s k := by
    intro k
    fin_cases k
    · exact hxσ
    · exact hxa
    · exact hxb
    · exact hxab
  have hGP : G * P = P.map bar := by
    ext r k
    have hk := mulVec_of_uniFixed hGGb (hcol k)
    have := congrFun hk r
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hdetbar : G.det * P.det = bar P.det := by
    have h1 := congrArg Matrix.det hGP
    have hmap : (P.map bar).det = bar P.det := by
      rw [RingHom.map_det]
      rfl
    rwa [Matrix.det_mul, hmap] at h1
  have hβbar : bar β = β := bar_gramForm_uniFixed hbb hGGb hxσ
  have hbP : bar P.det ≠ 0 := by
    rw [← hdetbar]
    exact mul_ne_zero hG0 hP0
  have hprod : P.det * bar P.det = β ^ 4 := by
    rw [← hdetbar]
    linear_combination hdet
  apply hGd
  refine ⟨β ^ 2 / P.det, ?_, ?_⟩
  · rw [pow_succ, ← hbar, map_div₀, map_pow, hβbar, div_mul_div_comm,
      div_eq_one_iff_eq (mul_ne_zero hbP hP0)]
    linear_combination (-1 : F) * hprod
  · rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hP0 hP0)]
    linear_combination (-1 : F) * hdet

end CFSG.GH74.Generic.S1
