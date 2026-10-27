module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4QNsq
public import CFSG.GH74.Generic.BProg.B2.GenLocL4QSplitBasis

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.ComponentClassification Module

namespace GenLocL4Q

variable {F : Type} [Field F]

theorem exists_kernel_vec {c m ν l : F} (hc0 : c ≠ 0) (hm : m ≠ 0) (hl : l ≠ 0) (hlν : l * l * c = ν)
    {x y z : Matrix (Fin 4) (Fin 4) F} (hx : x * x = c • 1) (hy : y * y = m • 1) (hz : z * z = ν • 1)
    (hxy : x * y = -(y * x)) (hxz : x * z = z * x) (hyz : y * z = z * y) (h2 : (2 : F) ≠ 0) :
    ∃ v : Fin 4 → F, v ≠ 0 ∧ z *ᵥ v = l • (x *ᵥ v) := by
  by_contra hcon
  have hcon' : ∀ v : Fin 4 → F, v ≠ 0 → z *ᵥ v ≠ l • (x *ᵥ v) := fun v hv h => hcon ⟨v, hv, h⟩
  have hprod : (z - l • x) * (z + l • x) = 0 := by
    have e : (z - l • x) * (z + l • x) = z * z - (l * l) • (x * x) + l • (z * x - x * z) := by
      simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub]
      abel
    rw [e, hz, hx, hxz, sub_self, smul_zero, add_zero, smul_smul, hlν]
    simp
  have hall : ∀ u : Fin 4 → F, (z + l • x) *ᵥ u = 0 := by
    intro u
    by_contra hne
    apply hcon' ((z + l • x) *ᵥ u) hne
    have h0 : (z - l • x) *ᵥ ((z + l • x) *ᵥ u) = 0 := by
      rw [Matrix.mulVec_mulVec, hprod, Matrix.zero_mulVec]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec] at h0
    exact sub_eq_zero.1 h0
  have h0 := eq_zero_of_mulVec_eq_zero' hall
  have hzx : z = -(l • x) := eq_neg_of_add_eq_zero_left h0
  have h3 : l • (y * x) = l • (x * y) := by
    have := hyz
    rw [hzx] at this
    simpa [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, smul_mul_assoc] using this
  have h4 : x * y = y * x := (smul_right_injective _ hl h3).symm
  have h5 : (2 : F) • (x * y) = 0 := by
    have h6 : x * y + y * x = 0 := add_eq_zero_iff_eq_neg.2 hxy
    rw [← h4] at h6
    rwa [← two_smul F] at h6
  have h7 : x * y = 0 := (smul_eq_zero.1 h5).resolve_left h2
  have h8 : c • y = 0 := by
    calc c • y = (c • (1 : Matrix (Fin 4) (Fin 4) F)) * y := by simp
      _ = (x * x) * y := by rw [hx]
      _ = x * (x * y) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [h7, mul_zero]
  have hy0 : y = 0 := (smul_eq_zero.1 h8).resolve_left hc0
  have h9 : m • (1 : Matrix (Fin 4) (Fin 4) F) = 0 := by rw [← hy, hy0, mul_zero]
  exact hm ((smul_eq_zero.1 h9).resolve_right one_ne_zero)

theorem intertwine_of_vectors {c m l : F} {x y z : Matrix (Fin 4) (Fin 4) F} {w0 w1 w2 w3 : Fin 4 → F}
    (hx0 : x *ᵥ w0 = w1) (hx1 : x *ᵥ w1 = c • w0) (hx2 : x *ᵥ w2 = w3) (hx3 : x *ᵥ w3 = c • w2)
    (hy0 : y *ᵥ w0 = w2) (hy1 : y *ᵥ w1 = -w3) (hy2 : y *ᵥ w2 = m • w0) (hy3 : y *ᵥ w3 = -(m • w1))
    (hz0 : z *ᵥ w0 = l • w1) (hz1 : z *ᵥ w1 = (l * c) • w0) (hz2 : z *ᵥ w2 = -(l • w3))
    (hz3 : z *ᵥ w3 = -((l * c) • w2)) :
    let R : Matrix (Fin 4) (Fin 4) F := Matrix.of fun i j => (![w0, w1, w2, w3] j) i
    x * R = R * Xr c ∧ y * R = R * Yr m ∧ z * R = R * (l • Z0 c) := by
  intro R
  have hMR : ∀ (M : Matrix (Fin 4) (Fin 4) F) (i j : Fin 4),
      (M * R) i j = (M *ᵥ (![w0, w1, w2, w3] j)) i := by
    intro M i j
    simp [R, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hRN : ∀ (N : Matrix (Fin 4) (Fin 4) F) (i j : Fin 4),
      (R * N) i j = ∑ k, (![w0, w1, w2, w3] k) i * N k j := by
    intro N i j
    simp [R, Matrix.mul_apply]
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    rw [hMR, hRN]
    fin_cases j
    · simp [Fin.sum_univ_four, Xr, hx0]
    · simp [Fin.sum_univ_four, Xr, hx1, mul_comm]
    · simp [Fin.sum_univ_four, Xr, hx2]
    · simp [Fin.sum_univ_four, Xr, hx3, mul_comm]
  · ext i j
    rw [hMR, hRN]
    fin_cases j
    · simp [Fin.sum_univ_four, Yr, hy0]
    · simp [Fin.sum_univ_four, Yr, hy1]
    · simp [Fin.sum_univ_four, Yr, hy2, mul_comm]
    · simp [Fin.sum_univ_four, Yr, hy3, mul_comm]
  · ext i j
    rw [hMR, hRN]
    fin_cases j
    · simp [Fin.sum_univ_four, Z0, hz0]; ring
    · simp [Fin.sum_univ_four, Z0, hz1, mul_comm]
    · simp [Fin.sum_univ_four, Z0, hz2]; ring
    · simp [Fin.sum_univ_four, Z0, hz3, mul_comm]

theorem nsq_basis (hF : ringChar F ≠ 2) {c m ν l : F} (hc : ¬ IsSquare c) (hm : m ≠ 0) (hl : l ≠ 0)
    (hlν : l * l * c = ν) {x y z : Matrix (Fin 4) (Fin 4) F} (hx : x * x = c • 1) (hy : y * y = m • 1)
    (hz : z * z = ν • 1) (hxy : x * y = -(y * x)) (hxz : x * z = z * x) (hyz : y * z = z * y) :
    ∃ R : Matrix (Fin 4) (Fin 4) F, IsUnit R ∧ x * R = R * Xr c ∧ y * R = R * Yr m ∧
      z * R = R * (l • Z0 c) := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hc0 : c ≠ 0 := ne_zero_of_not_isSquare hc
  obtain ⟨v, hv0, hzv⟩ := exists_kernel_vec hc0 hm hl hlν hx hy hz hxy hxz hyz h2
  have hxmul : ∀ u : Fin 4 → F, x *ᵥ (x *ᵥ u) = c • u := fun u => by
    rw [Matrix.mulVec_mulVec, hx, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hymul : ∀ u : Fin 4 → F, y *ᵥ (y *ᵥ u) = m • u := fun u => by
    rw [Matrix.mulVec_mulVec, hy, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hyx : ∀ u : Fin 4 → F, y *ᵥ (x *ᵥ u) = -(x *ᵥ (y *ᵥ u)) := fun u => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.neg_mulVec]
    congr 1
    have : y * x = -(x * y) := by rw [hxy]; simp
    exact this
  have hxz' : ∀ u : Fin 4 → F, z *ᵥ (x *ᵥ u) = x *ᵥ (z *ᵥ u) := fun u => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hxz]
  have hyz' : ∀ u : Fin 4 → F, z *ᵥ (y *ᵥ u) = y *ᵥ (z *ᵥ u) := fun u => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hyz]
  have hyv0 : y *ᵥ v ≠ 0 := by
    intro h
    apply hv0
    have h1 := hymul v
    rw [h, Matrix.mulVec_zero] at h1
    have h2' : m • v = 0 := h1.symm
    exact (smul_eq_zero.1 h2').resolve_left hm
  have hz1 : z *ᵥ (x *ᵥ v) = l • (c • v) := by rw [hxz', hzv, Matrix.mulVec_smul, hxmul]
  have hz2 : z *ᵥ (y *ᵥ v) = -(l • (x *ᵥ (y *ᵥ v))) := by
    rw [hyz', hzv, Matrix.mulVec_smul, hyx, smul_neg]
  have hz3 : z *ᵥ (x *ᵥ (y *ᵥ v)) = -(l • (c • (y *ᵥ v))) := by
    rw [hxz', hyz', hzv, Matrix.mulVec_smul, Matrix.mulVec_smul, hyx, Matrix.mulVec_neg, hxmul]
    simp
  let R : Matrix (Fin 4) (Fin 4) F := Matrix.of fun i j => (![v, x *ᵥ v, y *ᵥ v, x *ᵥ (y *ᵥ v)] j) i
  have hR : ∀ g : Fin 4 → F, R *ᵥ g =
      g 0 • v + g 1 • (x *ᵥ v) + g 2 • (y *ᵥ v) + g 3 • (x *ᵥ (y *ᵥ v)) := by
    intro g
    ext i
    simp [R, Matrix.mulVec, dotProduct, Fin.sum_univ_four, mul_comm]
  have hRinj : Function.Injective R.mulVec := by
    have hinj : Function.Injective (Matrix.mulVecLin R) := by
      rw [injective_iff_map_eq_zero]
      intro g hg
      have hg' : R *ᵥ g = 0 := hg
      rw [hR] at hg'
      have hN : ∀ u : Fin 4 → F, (z - l • x) *ᵥ u = z *ᵥ u - l • (x *ᵥ u) := fun u => by
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec]
      have hNv : (z - l • x) *ᵥ v = 0 := by rw [hN, hzv, sub_self]
      have hNxv : (z - l • x) *ᵥ (x *ᵥ v) = 0 := by rw [hN, hz1, hxmul]; module
      have hNyv : (z - l • x) *ᵥ (y *ᵥ v) = (-(2 * l)) • (x *ᵥ (y *ᵥ v)) := by
        rw [hN, hz2]; module
      have hNxyv : (z - l • x) *ᵥ (x *ᵥ (y *ᵥ v)) = (-(2 * l * c)) • (y *ᵥ v) := by
        rw [hN, hz3, hxmul]; module
      have h1 := congrArg (fun w => (z - l • x) *ᵥ w) hg'
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hNv, hNxv, hNyv, hNxyv, Matrix.mulVec_zero,
        smul_zero, zero_add] at h1
      have h1' : (g 3 * (-(2 * l * c))) • (y *ᵥ v) + (g 2 * (-(2 * l))) • (x *ᵥ (y *ᵥ v)) = 0 := by
        rw [← h1]; module
      obtain ⟨k3, k2⟩ := pair_indep hc hx hyv0 _ _ h1'
      have g3z : g 3 = 0 := by
        have : g 3 * (-(2 * l * c)) = 0 := k3
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · exact absurd (by linear_combination (-1 : F) * h : 2 * l * c = 0)
            (mul_ne_zero (mul_ne_zero h2 hl) hc0)
      have g2z : g 2 = 0 := by
        have : g 2 * (-(2 * l)) = 0 := k2
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · exact absurd (by linear_combination (-1 : F) * h : 2 * l = 0) (mul_ne_zero h2 hl)
      rw [g3z, g2z, zero_smul, zero_smul, add_zero, add_zero] at hg'
      obtain ⟨k0, k1⟩ := pair_indep hc hx hv0 _ _ hg'
      ext i
      fin_cases i <;> simp [k0, k1, g2z, g3z]
    exact hinj
  have hRunit : IsUnit R := Matrix.mulVec_injective_iff_isUnit.1 hRinj
  have hy3 : y *ᵥ (x *ᵥ (y *ᵥ v)) = -(m • (x *ᵥ v)) := by
    rw [hyx, hymul, Matrix.mulVec_smul]
  have hrel := intertwine_of_vectors (c := c) (m := m) (l := l) (x := x) (y := y) (z := z)
    (w0 := v) (w1 := x *ᵥ v) (w2 := y *ᵥ v) (w3 := x *ᵥ (y *ᵥ v)) rfl (hxmul v) rfl (hxmul (y *ᵥ v))
    rfl (hyx v) (hymul v) hy3 hzv (by rw [hz1, mul_smul]) hz2 (by rw [hz3, mul_smul])
  exact ⟨R, hRunit, hrel.1, hrel.2.1, hrel.2.2⟩

theorem inter_mul_gen {R a b A B : Matrix (Fin 4) (Fin 4) F} (ha : a * R = R * A) (hb : b * R = R * B) :
    (a * b) * R = R * (A * B) := by
  rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]

theorem comm_smul_gen (l : F) (g K : Matrix (Fin 4) (Fin 4) F) (h : g * K = K * g) :
    g * (l • K) = (l • K) * g := by
  rw [Matrix.mul_smul, smul_mul_assoc, h]

theorem top_of_rank3_nsq [Finite F] (hF : ringChar F ≠ 2) (hF4 : Nat.card F % 4 = 3) (h7 : 7 ≤ Nat.card F)
    {c m ν : F} (hc : ¬ IsSquare c) (hν : ¬ IsSquare ν) (hm : m ≠ 0)
    {x y z : Matrix (Fin 4) (Fin 4) F} (hx : x * x = c • 1) (hy : y * y = m • 1) (hz : z * z = ν • 1)
    (hxy : x * y = -(y * x)) (hxz : x * z = z * x) (hyz : y * z = z * y)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F))
    (H1 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * x = x * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * y = y * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H2 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * x = x * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (y * z) = (y * z) * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H3 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * y = y * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (x * z) = (x * z) * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H4 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * (x * y) = (x * y) * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (x * z) = (x * z) * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H5 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * x = x * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * z = z * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ) :
    Γ = ⊤ := by
  classical
  have := Fintype.ofFinite F
  have hc0 : c ≠ 0 := ne_zero_of_not_isSquare hc
  have hν0 : ν ≠ 0 := ne_zero_of_not_isSquare hν
  obtain ⟨r, hr⟩ := isSquare_mul_of_not hc hν
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hc0 hν0 (by rw [hr]; ring)
  have hl : r / c ≠ 0 := div_ne_zero hr0 hc0
  have hlν : (r / c) * (r / c) * c = ν := by
    field_simp
    linear_combination (-1 : F) * hr
  obtain ⟨R, hRu, hxR, hyR, hzR⟩ := nsq_basis hF hc hm hl hlν hx hy hz hxy hxz hyz
  have hRu' : (hRu.unit : Matrix (Fin 4) (Fin 4) F) = R := hRu.unit_spec
  have hyzR : (y * z) * R = R * ((r / c) • (Yr m * Z0 c)) := by
    rw [inter_mul_gen hyR hzR, Matrix.mul_smul]
  have hxzR : (x * z) * R = R * ((r / c) • (Xr c * Z0 c)) := by
    rw [inter_mul_gen hxR hzR, Matrix.mul_smul]
  have hxyR : (x * y) * R = R * (Xr c * Yr m) := inter_mul_gen hxR hyR
  apply top_of_conj hRu
  refine top_of_nsq_model hF hF4 h7 hc hm _ ?_ ?_ ?_ ?_ ?_
  · intro g hg1 hg2
    exact H1 _ (slConj_commute (by rw [hRu']; exact hxR) g hg1)
      (slConj_commute (by rw [hRu']; exact hyR) g hg2)
  · intro g hg1 hg2
    exact H2 _ (slConj_commute (by rw [hRu']; exact hxR) g hg1)
      (slConj_commute (by rw [hRu']; exact hyzR) g (comm_smul_gen _ _ _ hg2))
  · intro g hg1 hg2
    exact H3 _ (slConj_commute (by rw [hRu']; exact hyR) g hg1)
      (slConj_commute (by rw [hRu']; exact hxzR) g (comm_smul_gen _ _ _ hg2))
  · intro g hg1 hg2
    exact H4 _ (slConj_commute (by rw [hRu']; exact hxyR) g hg1)
      (slConj_commute (by rw [hRu']; exact hxzR) g (comm_smul_gen _ _ _ hg2))
  · intro g hg1 hg2
    exact H5 _ (slConj_commute (by rw [hRu']; exact hxR) g hg1)
      (slConj_commute (by rw [hRu']; exact hzR) g (comm_smul_gen _ _ _ hg2))

end GenLocL4Q

end CFSG.GH74.Generic.BProg.B2
