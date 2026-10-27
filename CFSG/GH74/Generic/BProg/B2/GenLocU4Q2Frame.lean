module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutFrExt

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix GenLocU4Basic GenLocU4Out CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary

namespace GenLocU4Q2

@[expose] def q2Y {K : Type} [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]

end GenLocU4Q2

namespace GenLocU4Q2Frame

variable {K : Type} [Field K]

section TwoByTwo

variable (σ : K ≃+* K)

@[expose] def Sf (m00 m01 m10 m11 s t s' t' : K) : K :=
  σ s * (m00 * s' + m01 * t') + σ t * (m10 * s' + m11 * t')

theorem Sf_skew (hinv : ∀ x, σ (σ x) = x) {m00 m01 m10 m11 : K} (h00 : σ m00 = -m00) (h11 : σ m11 = -m11)
    (h10 : m10 = -σ m01) (s t s' t' : K) :
    Sf σ m00 m01 m10 m11 s' t' s t = -σ (Sf σ m00 m01 m10 m11 s t s' t') := by
  have hm01 : σ m01 = -m10 := by linear_combination h10
  have hm10 : σ m10 = -m01 := by rw [h10, map_neg, hinv]
  simp only [Sf, map_add, map_mul, hinv, h00, h11, hm01, hm10]
  ring

theorem Sf_iso (hσ : IsUnitaryInvolution σ) {m00 m01 m10 m11 : K} (h00 : σ m00 = -m00) (h11 : σ m11 = -m11)
    (h10 : m10 = -σ m01) (hdet : m00 * m11 - m01 * m10 ≠ 0) :
    ∃ s t : K, (s ≠ 0 ∨ t ≠ 0) ∧ Sf σ m00 m01 m10 m11 s t s t = 0 := by
  have hinv := hσ.invol
  have hm01 : σ m01 = -m10 := by linear_combination h10
  have hm10 : σ m10 = -m01 := by rw [h10, map_neg, hinv]
  by_cases h0 : m00 = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, by simp [Sf, h0]⟩
  · have hdetfix : σ (m00 * m11 - m01 * m10) = m00 * m11 - m01 * m10 := by
      simp only [map_sub, map_mul, h00, h11, hm01, hm10]
      ring
    have hd : σ (-(m00 * m11 - m01 * m10) / (m00 * m00)) = -(m00 * m11 - m01 * m10) / (m00 * m00) := by
      simp only [map_div₀, map_neg, map_mul, hdetfix, h00]
      field_simp
    obtain ⟨l, hl⟩ := hσ.exists_norm hd
    have hl' : m00 * m00 * (σ l * l) + (m00 * m11 - m01 * m10) = 0 := by
      rw [hl]
      field_simp
      ring
    set c : K := -m01 / m00 with hc
    have hc1 : m00 * c + m01 = 0 := by
      rw [hc]
      field_simp
      ring
    have hσc : m00 * σ c + m10 = 0 := by
      rw [hc]
      simp only [map_div₀, map_neg, hm01, h00]
      field_simp
      ring
    refine ⟨l + c, 1, Or.inr one_ne_zero, ?_⟩
    have hQ : m00 * Sf σ m00 m01 m10 m11 (l + c) 1 (l + c) 1 = 0 := by
      simp only [Sf, map_add, map_one, one_mul]
      linear_combination hl' + (m00 * σ l + m00 * σ c + m10) * hc1 + (m00 * l) * hσc
    exact (mul_eq_zero.1 hQ).resolve_left h0

theorem Sf_partner {m00 m01 m10 m11 : K} (hdet : m00 * m11 - m01 * m10 ≠ 0) {s t : K} (hst : s ≠ 0 ∨ t ≠ 0)
    (c : K) : ∃ s' t' : K, Sf σ m00 m01 m10 m11 s t s' t' = c := by
  have hS : ∀ s' t', Sf σ m00 m01 m10 m11 s t s' t' =
      (σ s * m00 + σ t * m10) * s' + (σ s * m01 + σ t * m11) * t' := fun s' t' => by
    simp only [Sf]
    ring
  have hαβ : σ s * m00 + σ t * m10 ≠ 0 ∨ σ s * m01 + σ t * m11 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨ha, hb⟩ := hcon
    have e1 : σ s * (m00 * m11 - m01 * m10) = 0 := by linear_combination m11 * ha - m10 * hb
    have e2 : σ t * (m00 * m11 - m01 * m10) = 0 := by linear_combination m00 * hb - m01 * ha
    have hs : σ s = 0 := (mul_eq_zero.1 e1).resolve_right hdet
    have ht : σ t = 0 := (mul_eq_zero.1 e2).resolve_right hdet
    have hs0 : s = 0 := (map_eq_zero_iff σ σ.injective).1 hs
    have ht0 : t = 0 := (map_eq_zero_iff σ σ.injective).1 ht
    rcases hst with h | h
    · exact h hs0
    · exact h ht0
  rcases hαβ with h | h
  · exact ⟨c / (σ s * m00 + σ t * m10), 0, by rw [hS]; field_simp; ring⟩
  · exact ⟨0, c / (σ s * m01 + σ t * m11), by rw [hS]; field_simp; ring⟩

theorem Sf_fix (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) ≠ 0) {m00 m01 m10 m11 : K} (h00 : σ m00 = -m00)
    (h11 : σ m11 = -m11) (h10 : m10 = -σ m01) {c : K} (hc : σ c = c) (hc0 : c ≠ 0) {s t s' t' : K}
    (hiso : Sf σ m00 m01 m10 m11 s t s t = 0) (hp : Sf σ m00 m01 m10 m11 s t s' t' = c) :
    ∃ s'' t'' : K, Sf σ m00 m01 m10 m11 s t s'' t'' = c ∧
      Sf σ m00 m01 m10 m11 s'' t'' s'' t'' = 0 := by
  have hinv := hσ.invol
  have hskew := Sf_skew σ hinv h00 h11 h10
  have hee : σ (Sf σ m00 m01 m10 m11 s' t' s' t') = -Sf σ m00 m01 m10 m11 s' t' s' t' := by
    have := hskew s' t' s' t'
    linear_combination this
  have hpq : Sf σ m00 m01 m10 m11 s' t' s t = -c := by rw [hskew, hp, hc]
  set e := Sf σ m00 m01 m10 m11 s' t' s' t' with he
  set τ : K := e / (2 * c) with hτ
  have hστ : σ τ = -τ := by
    rw [hτ]
    simp only [map_div₀, map_mul, hee, hc, map_ofNat]
    ring
  refine ⟨s' + τ * s, t' + τ * t, ?_, ?_⟩
  · have : Sf σ m00 m01 m10 m11 s t (s' + τ * s) (t' + τ * t) =
        Sf σ m00 m01 m10 m11 s t s' t' + τ * Sf σ m00 m01 m10 m11 s t s t := by
      simp only [Sf]
      ring
    rw [this, hiso, hp]
    ring
  · have : Sf σ m00 m01 m10 m11 (s' + τ * s) (t' + τ * t) (s' + τ * s) (t' + τ * t) =
        Sf σ m00 m01 m10 m11 s' t' s' t' + τ * Sf σ m00 m01 m10 m11 s' t' s t +
          σ τ * Sf σ m00 m01 m10 m11 s t s' t' + σ τ * τ * Sf σ m00 m01 m10 m11 s t s t := by
      simp only [Sf, map_add, map_mul]
      ring
    rw [this, hiso, hpq, hp, hστ, hτ]
    field_simp
    ring

theorem Sf_pair (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) ≠ 0) {m00 m01 m10 m11 : K} (h00 : σ m00 = -m00)
    (h11 : σ m11 = -m11) (h10 : m10 = -σ m01) (hdet : m00 * m11 - m01 * m10 ≠ 0) {c : K} (hc : σ c = c)
    (hc0 : c ≠ 0) :
    ∃ s t s' t' : K, Sf σ m00 m01 m10 m11 s t s t = 0 ∧ Sf σ m00 m01 m10 m11 s' t' s' t' = 0 ∧
      Sf σ m00 m01 m10 m11 s t s' t' = c := by
  obtain ⟨s, t, hst, hiso⟩ := Sf_iso σ hσ h00 h11 h10 hdet
  obtain ⟨s', t', hp⟩ := Sf_partner σ hdet hst c
  obtain ⟨s'', t'', h1, h2'⟩ := Sf_fix σ hσ h2 h00 h11 h10 hc hc0 hiso hp
  exact ⟨s, t, s'', t'', hiso, h2', h1⟩

end TwoByTwo

section Quat

variable (σ : K ≃+* K) {x y : Matrix (Fin 4) (Fin 4) K}

@[expose] def colsM (c0 c1 c2 c3 : Fin 4 → K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j => ![c0, c1, c2, c3] j i

@[expose] def quatU (x y : Matrix (Fin 4) (Fin 4) K) (u : Fin 4 → K) : Matrix (Fin 4) (Fin 4) K :=
  colsM u (-(x *ᵥ u)) (-(y *ᵥ u)) (-(y *ᵥ (x *ᵥ u)))

theorem mul_colsM (M : Matrix (Fin 4) (Fin 4) K) (c0 c1 c2 c3 : Fin 4 → K) :
    M * colsM c0 c1 c2 c3 = colsM (M *ᵥ c0) (M *ᵥ c1) (M *ᵥ c2) (M *ᵥ c3) := by
  ext i j
  fin_cases j <;> rfl

theorem colsM_mul_xi (c0 c1 c2 c3 : Fin 4 → K) :
    colsM c0 c1 c2 c3 * (xi : Matrix (Fin 4) (Fin 4) K) = colsM (-c1) c0 (-c3) c2 := by
  ext i j
  fin_cases j <;> simp [colsM, Matrix.mul_apply, Fin.sum_univ_four, xi]

theorem colsM_mul_q2Y (c0 c1 c2 c3 : Fin 4 → K) :
    colsM c0 c1 c2 c3 * (GenLocU4Q2.q2Y : Matrix (Fin 4) (Fin 4) K) = colsM (-c2) c3 c0 (-c1) := by
  ext i j
  fin_cases j <;> simp [colsM, Matrix.mul_apply, Fin.sum_univ_four, GenLocU4Q2.q2Y]

theorem herm_mulVec_unitary {A : Matrix (Fin 4) (Fin 4) K} (hA : (A.map σ)ᵀ * A = 1) (p q : Fin 4 → K) :
    herm σ (A *ᵥ p) (A *ᵥ q) = herm σ p q := by
  rw [herm_mulVec]
  show herm σ p (((A.map σ)ᵀ * A) *ᵥ q) = _
  rw [hA, Matrix.one_mulVec]

theorem mulVec_sq {A : Matrix (Fin 4) (Fin 4) K} (hA : A * A = -1) (p : Fin 4 → K) : A *ᵥ (A *ᵥ p) = -p := by
  rw [Matrix.mulVec_mulVec, hA, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem mulVec_anti (hxy : x * y = -(y * x)) (p : Fin 4 → K) : x *ᵥ (y *ᵥ p) = -(y *ᵥ (x *ᵥ p)) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hxy]
  simp [Matrix.neg_mulVec]

theorem unitary_of_cols (hinv : ∀ c, σ (σ c) = c) (c0 c1 c2 c3 : Fin 4 → K) (h00 : herm σ c0 c0 = 1)
    (h11 : herm σ c1 c1 = 1) (h22 : herm σ c2 c2 = 1) (h33 : herm σ c3 c3 = 1) (h01 : herm σ c0 c1 = 0)
    (h02 : herm σ c0 c2 = 0) (h03 : herm σ c0 c3 = 0) (h12 : herm σ c1 c2 = 0) (h13 : herm σ c1 c3 = 0)
    (h23 : herm σ c2 c3 = 0) :
    ((colsM c0 c1 c2 c3).map σ)ᵀ * colsM c0 c1 c2 c3 = 1 := by
  have s01 := herm_eq_zero_comm σ hinv h01
  have s02 := herm_eq_zero_comm σ hinv h02
  have s03 := herm_eq_zero_comm σ hinv h03
  have s12 := herm_eq_zero_comm σ hinv h12
  have s13 := herm_eq_zero_comm σ hinv h13
  have s23 := herm_eq_zero_comm σ hinv h23
  have key : ∀ j k : Fin 4, (((colsM c0 c1 c2 c3).map σ)ᵀ * colsM c0 c1 c2 c3) j k =
      herm σ (![c0, c1, c2, c3] j) (![c0, c1, c2, c3] k) := fun j k => rfl
  ext j k
  rw [key]
  fin_cases j <;> fin_cases k <;> simp [h00, h11, h22, h33, h01, h02, h03, h12, h13, h23,
    s01, s02, s03, s12, s13, s23]

theorem quatU_unitary (hinv : ∀ c, σ (σ c) = c) (hxs : (x.map σ)ᵀ * x = 1) (hys : (y.map σ)ᵀ * y = 1)
    (hx2 : x * x = -1) (hxy : x * y = -(y * x)) {u : Fin 4 → K}
    (h1 : herm σ u u = 1) (h2 : herm σ u (x *ᵥ u) = 0) (h3 : herm σ u (y *ᵥ u) = 0)
    (h4 : herm σ u (x *ᵥ (y *ᵥ u)) = 0) : ((quatU x y u).map σ)ᵀ * quatU x y u = 1 := by
  have hxu := herm_mulVec_unitary σ hxs
  have hyu := herm_mulVec_unitary σ hys
  have xx := mulVec_sq hx2
  have yx : y *ᵥ (x *ᵥ u) = -(x *ᵥ (y *ᵥ u)) := by rw [mulVec_anti hxy u, neg_neg]
  refine unitary_of_cols σ hinv _ _ _ _ h1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [herm_neg_left, herm_neg_right, neg_neg, hxu, h1]
  · rw [herm_neg_left, herm_neg_right, neg_neg, hyu, h1]
  · rw [herm_neg_left, herm_neg_right, neg_neg, hyu, hxu, h1]
  · rw [herm_neg_right, h2, neg_zero]
  · rw [herm_neg_right, h3, neg_zero]
  · rw [yx, neg_neg]
    exact h4
  · have : -(y *ᵥ u) = x *ᵥ (x *ᵥ (y *ᵥ u)) := by rw [xx]
    rw [this, herm_neg_left, hxu, h4, neg_zero]
  · have : -(y *ᵥ (x *ᵥ u)) = x *ᵥ (y *ᵥ u) := by rw [yx, neg_neg]
    rw [this, herm_neg_left, hxu, h3, neg_zero]
  · rw [herm_neg_left, herm_neg_right, neg_neg, hyu, h2]

theorem x_mul_quatU (hx2 : x * x = -1) (hxy : x * y = -(y * x)) (u : Fin 4 → K) :
    x * quatU x y u = quatU x y u * (xi : Matrix (Fin 4) (Fin 4) K) := by
  have xx := mulVec_sq hx2
  have xy := mulVec_anti hxy
  have c1 : x *ᵥ -(x *ᵥ u) = u := by rw [Matrix.mulVec_neg, xx, neg_neg]
  have c2 : x *ᵥ -(y *ᵥ u) = -(-(y *ᵥ (x *ᵥ u))) := by rw [Matrix.mulVec_neg, xy u]
  have c3 : x *ᵥ -(y *ᵥ (x *ᵥ u)) = -(y *ᵥ u) := by
    rw [Matrix.mulVec_neg, xy (x *ᵥ u), xx, Matrix.mulVec_neg, neg_neg]
  unfold quatU
  rw [mul_colsM, colsM_mul_xi, c1, c2, c3]
  simp only [neg_neg]

theorem y_mul_quatU (hy2 : y * y = -1) (u : Fin 4 → K) :
    y * quatU x y u = quatU x y u * (GenLocU4Q2.q2Y : Matrix (Fin 4) (Fin 4) K) := by
  have yy := mulVec_sq hy2
  have d2 : y *ᵥ -(y *ᵥ u) = u := by rw [Matrix.mulVec_neg, yy, neg_neg]
  have d3 : y *ᵥ -(y *ᵥ (x *ᵥ u)) = x *ᵥ u := by rw [Matrix.mulVec_neg, yy, neg_neg]
  unfold quatU
  rw [mul_colsM, colsM_mul_q2Y, Matrix.mulVec_neg, d2, d3]
  simp only [neg_neg]

theorem quatFrame (hinv : ∀ c, σ (σ c) = c) (hxs : (x.map σ)ᵀ * x = 1) (hys : (y.map σ)ᵀ * y = 1)
    (hx2 : x * x = -1) (hy2 : y * y = -1) (hxy : x * y = -(y * x)) {u : Fin 4 → K}
    (h1 : herm σ u u = 1) (h2 : herm σ u (x *ᵥ u) = 0) (h3 : herm σ u (y *ᵥ u) = 0)
    (h4 : herm σ u (x *ᵥ (y *ᵥ u)) = 0) :
    ∃ U : Matrix (Fin 4) (Fin 4) K, (U.map σ)ᵀ * U = 1 ∧ x * U = U * (xi : Matrix (Fin 4) (Fin 4) K) ∧
      y * U = U * (GenLocU4Q2.q2Y : Matrix (Fin 4) (Fin 4) K) :=
  ⟨quatU x y u, quatU_unitary σ hinv hxs hys hx2 hxy h1 h2 h3 h4, x_mul_quatU hx2 hxy u, y_mul_quatU hy2 u⟩

end Quat

section Pair

variable (σ : K ≃+* K) {x y : Matrix (Fin 4) (Fin 4) K}

theorem herm_y_adj (hys : (y.map σ)ᵀ * y = 1) (hy2 : y * y = -1) (p q : Fin 4 → K) :
    herm σ p (y *ᵥ q) = -herm σ (y *ᵥ p) q := by
  have := herm_mulVec_unitary σ hys p (y *ᵥ q)
  rw [mulVec_sq hy2 q, herm_neg_right] at this
  exact this.symm

theorem herm_eig_zero (h2 : (2 : K) ≠ 0) (hxs : (x.map σ)ᵀ * x = 1) {ι : K} (hι : ι * ι = -1) (hσι : σ ι = ι)
    {p q : Fin 4 → K} (hp : x *ᵥ p = ι • p) (hq : x *ᵥ q = ι • q) : herm σ p q = 0 := by
  have := herm_mulVec_unitary σ hxs p q
  rw [hp, hq, herm_smul_left, herm_smul_right, hσι] at this
  have h : (2 : K) * herm σ p q = 0 := by linear_combination (-1 : K) * this + herm σ p q * hι
  exact (mul_eq_zero.1 h).resolve_left h2

theorem quat_of_pair (hinv : ∀ c, σ (σ c) = c) (h2 : (2 : K) ≠ 0) (hxs : (x.map σ)ᵀ * x = 1)
    (hys : (y.map σ)ᵀ * y = 1) (hy2 : y * y = -1) (hxy : x * y = -(y * x)) {ι : K} (hι : ι * ι = -1)
    (hσι : σ ι = ι) {a a' : Fin 4 → K} (hxa : x *ᵥ a = ι • a) (hxa' : x *ᵥ a' = ι • a')
    (b00 : herm σ a (y *ᵥ a) = 0) (b11 : herm σ a' (y *ᵥ a') = 0) (b01 : herm σ a (y *ᵥ a') = 2⁻¹) :
    herm σ (a + y *ᵥ a') (a + y *ᵥ a') = 1 ∧ herm σ (a + y *ᵥ a') (x *ᵥ (a + y *ᵥ a')) = 0 ∧
      herm σ (a + y *ᵥ a') (y *ᵥ (a + y *ᵥ a')) = 0 ∧
      herm σ (a + y *ᵥ a') (x *ᵥ (y *ᵥ (a + y *ᵥ a'))) = 0 := by
  have hyy := mulVec_sq hy2
  have hyu := herm_mulVec_unitary σ hys
  have A1 : herm σ a a = 0 := herm_eig_zero σ h2 hxs hι hσι hxa hxa
  have A2 : herm σ a' a' = 0 := herm_eig_zero σ h2 hxs hι hσι hxa' hxa'
  have A3 : herm σ a a' = 0 := herm_eig_zero σ h2 hxs hι hσι hxa hxa'
  have A4 : herm σ a' a = 0 := herm_eig_zero σ h2 hxs hι hσι hxa' hxa
  have F3 := herm_y_adj σ hys hy2
  have C1 : herm σ (y *ᵥ a') a = 2⁻¹ := by rw [herm_conj σ hinv a (y *ᵥ a'), b01, map_inv₀, map_ofNat]
  have C2 : herm σ (y *ᵥ a') (y *ᵥ a') = 0 := by rw [hyu]; exact A2
  have C3 : herm σ (y *ᵥ a') (y *ᵥ a) = 0 := by rw [hyu]; exact A4
  have C4 : herm σ (y *ᵥ a') a' = 0 := by
    have := F3 a' a'
    rw [b11] at this
    linear_combination this
  have hxya' : x *ᵥ (y *ᵥ a') = -(ι • (y *ᵥ a')) := by
    rw [mulVec_anti hxy, hxa', Matrix.mulVec_smul]
  have hxya : x *ᵥ (y *ᵥ a) = -(ι • (y *ᵥ a)) := by
    rw [mulVec_anti hxy, hxa, Matrix.mulVec_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [herm_add_left, herm_add_right, A1, b01, C1, C2]
    linear_combination mul_inv_cancel₀ h2
  · rw [Matrix.mulVec_add, hxa, hxya']
    simp only [herm_add_left, herm_add_right, herm_neg_right, herm_smul_right, A1, b01, C1, C2]
    ring
  · rw [Matrix.mulVec_add, hyy]
    simp only [herm_add_left, herm_add_right, herm_neg_right, b00, C3, A3, C4]
    ring
  · rw [Matrix.mulVec_add, hyy, Matrix.mulVec_add, Matrix.mulVec_neg, hxya, hxa']
    simp only [herm_add_left, herm_add_right, herm_neg_right, herm_smul_right, b00, C3, A3, C4]
    ring

end Pair

section Xi

variable (σ : K ≃+* K) {y : Matrix (Fin 4) (Fin 4) K}

@[expose] def aV (ι s t : K) : Fin 4 → K := ![s, ι * s, t, ι * t]

theorem xi_mulVec_aV {ι : K} (hι : ι * ι = -1) (s t : K) :
    (xi : Matrix (Fin 4) (Fin 4) K) *ᵥ aV ι s t = ι • aV ι s t := by
  funext i
  fin_cases i <;> simp [xi, aV, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
    first | ring1 | linear_combination (-s) * hι | linear_combination (-t) * hι

theorem aV_expand (ι s t : K) : aV ι s t = s • aV ι 1 0 + t • aV ι 0 1 := by
  funext i
  fin_cases i <;> simp [aV] <;> ring

theorem herm_aV_y (y : Matrix (Fin 4) (Fin 4) K) (ι s t s' t' : K) :
    herm σ (aV ι s t) (y *ᵥ aV ι s' t') =
      Sf σ (herm σ (aV ι 1 0) (y *ᵥ aV ι 1 0)) (herm σ (aV ι 1 0) (y *ᵥ aV ι 0 1))
        (herm σ (aV ι 0 1) (y *ᵥ aV ι 1 0)) (herm σ (aV ι 0 1) (y *ᵥ aV ι 0 1)) s t s' t' := by
  have e1 := aV_expand ι s t
  have e2 := aV_expand ι s' t'
  calc herm σ (aV ι s t) (y *ᵥ aV ι s' t')
      = herm σ (s • aV ι 1 0 + t • aV ι 0 1) (y *ᵥ (s' • aV ι 1 0 + t' • aV ι 0 1)) := by rw [← e1, ← e2]
    _ = _ := by
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, herm_add_left, herm_add_right, herm_smul_left,
        herm_smul_right, Sf]
      ring

theorem y_aV_shape {ι : K} (hι : ι * ι = -1) (hanti : (xi : Matrix (Fin 4) (Fin 4) K) * y = -(y * xi)) (s t : K) :
    (y *ᵥ aV ι s t) 1 = -ι * (y *ᵥ aV ι s t) 0 ∧ (y *ᵥ aV ι s t) 3 = -ι * (y *ᵥ aV ι s t) 2 := by
  have h := mulVec_anti hanti (aV ι s t)
  rw [xi_mulVec_aV hι, Matrix.mulVec_smul] at h
  generalize y *ᵥ aV ι s t = z at h ⊢
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  simp [xi, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at h0 h2
  exact ⟨by linear_combination h0, by linear_combination h2⟩

theorem aV_ker (h2 : (2 : K) ≠ 0) (hy2 : y * y = -1) {ι : K} (hι : ι * ι = -1) (hσι : σ ι = ι)
    (hanti : (xi : Matrix (Fin 4) (Fin 4) K) * y = -(y * xi)) {s' t' : K}
    (k1 : herm σ (aV ι 1 0) (y *ᵥ aV ι s' t') = 0) (k2 : herm σ (aV ι 0 1) (y *ᵥ aV ι s' t') = 0) :
    s' = 0 ∧ t' = 0 := by
  obtain ⟨z1, z3⟩ := y_aV_shape hι hanti s' t'
  set z := y *ᵥ aV ι s' t' with hz
  simp [herm, aV, Fin.sum_univ_four, hσι] at k1 k2
  have e0 : z 0 = 0 := by
    have : (2 : K) * z 0 = 0 := by linear_combination k1 + (z 0) * hι - ι * z1
    exact (mul_eq_zero.1 this).resolve_left h2
  have e2 : z 2 = 0 := by
    have : (2 : K) * z 2 = 0 := by linear_combination k2 + (z 2) * hι - ι * z3
    exact (mul_eq_zero.1 this).resolve_left h2
  have e1 : z 1 = 0 := by rw [z1, e0]; ring
  have e3 : z 3 = 0 := by rw [z3, e2]; ring
  have hzz : z = 0 := by
    funext i
    fin_cases i <;> simp [e0, e1, e2, e3]
  have hp : aV ι s' t' = 0 := by
    have := mulVec_sq hy2 (aV ι s' t')
    rw [← hz, hzz, Matrix.mulVec_zero] at this
    simpa using this.symm
  have p0 := congrFun hp 0
  have p2 := congrFun hp 2
  exact ⟨by simpa [aV] using p0, by simpa [aV] using p2⟩

theorem exists_kernel2 {m00 m01 m10 m11 : K} (hdet : m00 * m11 - m01 * m10 = 0) :
    ∃ s t : K, (s ≠ 0 ∨ t ≠ 0) ∧ m00 * s + m01 * t = 0 ∧ m10 * s + m11 * t = 0 := by
  by_cases hA : m00 = 0 ∧ m01 = 0
  · obtain ⟨h0, h1⟩ := hA
    by_cases hB : m10 = 0 ∧ m11 = 0
    · obtain ⟨h2, h3⟩ := hB
      exact ⟨1, 0, Or.inl one_ne_zero, by simp [h0, h1], by simp [h2, h3]⟩
    · refine ⟨m11, -m10, ?_, by simp [h0, h1], by ring⟩
      by_contra hcon
      push Not at hcon
      exact hB ⟨neg_eq_zero.1 hcon.2, hcon.1⟩
  · refine ⟨m01, -m00, ?_, by ring, by linear_combination -hdet⟩
    by_contra hcon
    push Not at hcon
    exact hA ⟨neg_eq_zero.1 hcon.2, hcon.1⟩

theorem exists_pair_xi (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) ≠ 0) (hys : (y.map σ)ᵀ * y = 1)
    (hy2 : y * y = -1) (hanti : (xi : Matrix (Fin 4) (Fin 4) K) * y = -(y * xi)) {ι : K} (hι : ι * ι = -1)
    (hσι : σ ι = ι) :
    ∃ a a' : Fin 4 → K, (xi : Matrix (Fin 4) (Fin 4) K) *ᵥ a = ι • a ∧
      (xi : Matrix (Fin 4) (Fin 4) K) *ᵥ a' = ι • a' ∧ herm σ a (y *ᵥ a) = 0 ∧ herm σ a' (y *ᵥ a') = 0 ∧
      herm σ a (y *ᵥ a') = 2⁻¹ := by
  have hinv := hσ.invol
  have skew : ∀ p q : Fin 4 → K, herm σ p (y *ᵥ q) = -σ (herm σ q (y *ᵥ p)) := by
    intro p q
    rw [herm_y_adj σ hys hy2 p q, herm_conj σ hinv q (y *ᵥ p)]
  set m00 := herm σ (aV ι 1 0) (y *ᵥ aV ι 1 0) with hm00
  set m01 := herm σ (aV ι 1 0) (y *ᵥ aV ι 0 1) with hm01
  set m10 := herm σ (aV ι 0 1) (y *ᵥ aV ι 1 0) with hm10
  set m11 := herm σ (aV ι 0 1) (y *ᵥ aV ι 0 1) with hm11
  have h00 : σ m00 = -m00 := by
    have := skew (aV ι 1 0) (aV ι 1 0)
    linear_combination this
  have h11 : σ m11 = -m11 := by
    have := skew (aV ι 0 1) (aV ι 0 1)
    linear_combination this
  have h10 : m10 = -σ m01 := skew (aV ι 0 1) (aV ι 1 0)
  have hdet : m00 * m11 - m01 * m10 ≠ 0 := by
    intro hd
    obtain ⟨s', t', hne, k1, k2⟩ := exists_kernel2 hd
    have e1 := herm_aV_y σ y ι 1 0 s' t'
    have e2 := herm_aV_y σ y ι 0 1 s' t'
    simp only [Sf, map_one, map_zero, one_mul, zero_mul, add_zero, zero_add] at e1 e2
    obtain ⟨hs, ht⟩ := aV_ker σ h2 hy2 hι hσι hanti (by rw [e1]; exact k1) (by rw [e2]; exact k2)
    rcases hne with h | h
    · exact h hs
    · exact h ht
  obtain ⟨s, t, s', t', hs1, hs2, hs3⟩ :=
    Sf_pair σ hσ h2 h00 h11 h10 hdet (c := 2⁻¹) (by rw [map_inv₀, map_ofNat]) (inv_ne_zero h2)
  refine ⟨aV ι s t, aV ι s' t', xi_mulVec_aV hι s t, xi_mulVec_aV hι s' t', ?_, ?_, ?_⟩
  · rw [herm_aV_y]
    exact hs1
  · rw [herm_aV_y]
    exact hs2
  · rw [herm_aV_y]
    exact hs3

end Xi

section Assembly

variable (σ : K ≃+* K)

theorem exists_frame_xi (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) ≠ 0) {y : Matrix (Fin 4) (Fin 4) K}
    (hys : (y.map σ)ᵀ * y = 1) (hy2 : y * y = -1) (hanti : (xi : Matrix (Fin 4) (Fin 4) K) * y = -(y * xi))
    {ι : K} (hι : ι * ι = -1) (hσι : σ ι = ι) :
    ∃ U : Matrix (Fin 4) (Fin 4) K, (U.map σ)ᵀ * U = 1 ∧
      (xi : Matrix (Fin 4) (Fin 4) K) * U = U * (xi : Matrix (Fin 4) (Fin 4) K) ∧
      y * U = U * (GenLocU4Q2.q2Y : Matrix (Fin 4) (Fin 4) K) := by
  have hinv := hσ.invol
  obtain ⟨a, a', hxa, hxa', b00, b11, b01⟩ := exists_pair_xi σ hσ h2 hys hy2 hanti hι hσι
  have hxs : ((xi : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ * xi = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [xi, Matrix.mul_apply, Fin.sum_univ_four]
  have hx2 : (xi : Matrix (Fin 4) (Fin 4) K) * xi = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [xi, Matrix.mul_apply, Fin.sum_univ_four]
  obtain ⟨c1, c2, c3, c4⟩ := quat_of_pair σ hinv h2 hxs hys hy2 hanti hι hσι hxa hxa' b00 b11 b01
  exact quatFrame σ hinv hxs hys hx2 hy2 hanti c1 c2 c3 c4

theorem conj_props (hinv : ∀ c, σ (σ c) = c) {U₀ x y y₁ : Matrix (Fin 4) (Fin 4) K}
    (hU : conjTr σ U₀ * U₀ = 1) (hxU : x * U₀ = U₀ * (xi : Matrix (Fin 4) (Fin 4) K))
    (hys : conjTr σ y * y = 1) (hy2 : y * y = -1) (hxy : x * y = -(y * x))
    (hy₁ : y₁ = conjTr σ U₀ * y * U₀) :
    conjTr σ y₁ * y₁ = 1 ∧ y₁ * y₁ = -1 ∧ (xi : Matrix (Fin 4) (Fin 4) K) * y₁ = -(y₁ * xi) ∧
      y * U₀ = U₀ * y₁ := by
  have hUA : U₀ * conjTr σ U₀ = 1 := mul_eq_one_comm.1 hU
  have hcc : conjTr σ (conjTr σ U₀) = U₀ := by
    ext i j
    simp [conjTr, hinv]
  have hxi : (xi : Matrix (Fin 4) (Fin 4) K) = conjTr σ U₀ * x * U₀ := by
    rw [Matrix.mul_assoc, hxU, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hstar : conjTr σ y₁ = conjTr σ U₀ * (conjTr σ y * U₀) := by
    rw [hy₁, conjTr_mul, conjTr_mul, hcc]
  have hyU : y * U₀ = U₀ * y₁ := by
    rw [hy₁, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUA, Matrix.one_mul]
  refine ⟨?_, ?_, ?_, hyU⟩
  · rw [hstar, hy₁]
    calc conjTr σ U₀ * (conjTr σ y * U₀) * (conjTr σ U₀ * y * U₀)
        = conjTr σ U₀ * (conjTr σ y * (U₀ * conjTr σ U₀) * y) * U₀ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUA, Matrix.mul_one, hys, Matrix.mul_one, hU]
  · rw [hy₁]
    calc conjTr σ U₀ * y * U₀ * (conjTr σ U₀ * y * U₀)
        = conjTr σ U₀ * (y * (U₀ * conjTr σ U₀) * y) * U₀ := by simp only [Matrix.mul_assoc]
      _ = -1 := by rw [hUA, Matrix.mul_one, hy2, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, hU]
  · rw [hxi, hy₁]
    calc conjTr σ U₀ * x * U₀ * (conjTr σ U₀ * y * U₀)
        = conjTr σ U₀ * (x * (U₀ * conjTr σ U₀) * y) * U₀ := by simp only [Matrix.mul_assoc]
      _ = -(conjTr σ U₀ * y * U₀ * (conjTr σ U₀ * x * U₀)) := by
          rw [hUA, Matrix.mul_one, hxy]
          simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]
          rw [← Matrix.mul_assoc U₀ (conjTr σ U₀), hUA, Matrix.one_mul]

end Assembly

end GenLocU4Q2Frame

namespace GenLocU4Q2

theorem exists_q2_frame {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    {x y : Matrix (Fin 4) (Fin 4) K} (hxU : IsUnitaryU (p ^ f) x) (hyU : IsUnitaryU (p ^ f) y)
    (hx : x * x = -1) (hy : y * y = -1) (hxy : x * y = -(y * x)) :
    ∃ U : Matrix (Fin 4) (Fin 4) K, IsUnitaryU (p ^ f) U ∧ x * U = U * xi ∧ y * U = U * q2Y := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_sq hK
  have hσ := isUnitaryInvolution_unitaryInvolution (K := K) (p := p) (f := f) hK
  have hinv := hσ.invol
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rwa [ringChar.eq K p])
  have hf : (fun x : K => x ^ (p ^ f)) = ⇑(unitaryInvolution K p f) :=
    funext fun x => (unitaryInvolution_apply K p f x).symm
  obtain ⟨ι, hι⟩ : ∃ ι : K, ι * ι = -1 := by
    have := Fintype.ofFinite K
    have h4 : Fintype.card K % 4 ≠ 3 := by
      rw [← Nat.card_eq_fintype_card, hK, Nat.pow_mod, hq]
      norm_num
    obtain ⟨r, hr⟩ := FiniteField.isSquare_neg_one_iff.2 h4
    exact ⟨r, hr.symm⟩
  have hιq : ι ^ (p ^ f) = ι := by
    obtain ⟨k, hk⟩ : ∃ k, p ^ f = 4 * k + 1 := ⟨p ^ f / 4, by omega⟩
    rw [hk, pow_succ, pow_mul]
    have h4 : ι ^ 4 = 1 := by linear_combination (ι * ι - 1) * hι
    rw [h4, one_pow, one_mul]
  have hσι : unitaryInvolution K p f ι = ι := by rw [unitaryInvolution_apply]; exact hιq
  have hxs : conjTr (unitaryInvolution K p f) x * x = 1 := by
    have := hxU
    unfold IsUnitaryU at this
    rw [hf] at this
    exact this
  have hys : conjTr (unitaryInvolution K p f) y * y = 1 := by
    have := hyU
    unfold IsUnitaryU at this
    rw [hf] at this
    exact this
  obtain ⟨U₀, hU₀, hxU₀⟩ := GenLocU4OutFrExt.exists_ext_frame hp hp2 hK hq hxU hx
  have hU₀' : conjTr (unitaryInvolution K p f) U₀ * U₀ = 1 := by
    unfold IsUnitaryU at hU₀
    rw [hf] at hU₀
    exact hU₀
  obtain ⟨h1, h2', h3, h4⟩ := GenLocU4Q2Frame.conj_props (unitaryInvolution K p f) hinv hU₀' hxU₀ hys hy hxy
    (y₁ := conjTr (unitaryInvolution K p f) U₀ * y * U₀) rfl
  obtain ⟨U₁, hU₁, hξ, hyU₁⟩ := GenLocU4Q2Frame.exists_frame_xi (unitaryInvolution K p f) hσ h2 h1 h2' h3 hι hσι
  refine ⟨U₀ * U₁, ?_, ?_, ?_⟩
  · unfold IsUnitaryU
    rw [hf]
    show conjTr (unitaryInvolution K p f) (U₀ * U₁) * (U₀ * U₁) = 1
    rw [conjTr_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (conjTr (unitaryInvolution K p f) U₀) U₀, hU₀',
      Matrix.one_mul]
    exact hU₁
  · rw [← Matrix.mul_assoc, hxU₀, Matrix.mul_assoc, hξ, ← Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc, h4, Matrix.mul_assoc, hyU₁, ← Matrix.mul_assoc]

end GenLocU4Q2

end CFSG.GH74.Generic.BProg.B2
