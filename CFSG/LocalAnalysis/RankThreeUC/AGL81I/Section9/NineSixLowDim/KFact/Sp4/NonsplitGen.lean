module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Sp4.Defs
public import CFSG.RankThree.SubgroupLists.SymplecticTransvections

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix CFSG.RankThree.SubgroupLists

section Pair

variable {F : Type} [Field F]

@[simp] private theorem spIdx_inl (i : Fin 2) : spIdx (.inl i) = (i, 0) := rfl

@[simp] private theorem spIdx_inr (i : Fin 2) : spIdx (.inr i) = (i, 1) := rfl

private theorem spPairMatrix_mul (s t s' t' : Matrix (Fin 2) (Fin 2) F) :
    spPairMatrix s t * spPairMatrix s' t' = spPairMatrix (s * s') (t * t') := by
  ext x y
  rcases x with i | i <;> rcases y with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [spPairMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

private theorem eq_one_of_spPairMatrix_eq_one {s t : Matrix (Fin 2) (Fin 2) F}
    (h : spPairMatrix s t = 1) : s = 1 ∧ t = 1 := by
  have e : ∀ x y, spPairMatrix s t x y = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) x y :=
    fun x y => by rw [h]
  refine ⟨?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j
  · simpa [spPairMatrix] using e (.inl 0) (.inl 0)
  · simpa [spPairMatrix] using e (.inl 0) (.inr 0)
  · simpa [spPairMatrix] using e (.inr 0) (.inl 0)
  · simpa [spPairMatrix] using e (.inr 0) (.inr 0)
  · simpa [spPairMatrix] using e (.inl 1) (.inl 1)
  · simpa [spPairMatrix] using e (.inl 1) (.inr 1)
  · simpa [spPairMatrix] using e (.inr 1) (.inl 1)
  · simpa [spPairMatrix] using e (.inr 1) (.inr 1)

private theorem spPair_mem {g : GL (Fin 2 ⊕ Fin 2) F} {s t : Matrix (Fin 2) (Fin 2) F}
    (hg : (g : Matrix _ _ F) = spPairMatrix s t) (hs : s.det = 1) (ht : t.det = 1) :
    g ∈ CFSG.Open.StatedSp 2 F := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff, hg]
  rw [det_fin_two] at hs ht
  ext x y
  rcases x with i | i <;> rcases y with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [spPairMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination hs | linear_combination ht | linear_combination -hs |
      linear_combination -ht

private theorem spPairMatrix_one_left_mulVec (t : Matrix (Fin 2) (Fin 2) F)
    {v : Fin 2 ⊕ Fin 2 → F} (h1 : v (.inl 1) = 0) (h2 : v (.inr 1) = 0) :
    spPairMatrix 1 t *ᵥ v = v := by
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [spPairMatrix, mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, h1, h2,
      Matrix.one_apply]

private theorem spPairMatrix_one_right_mulVec (s : Matrix (Fin 2) (Fin 2) F)
    {v : Fin 2 ⊕ Fin 2 → F} (h1 : v (.inl 0) = 0) (h2 : v (.inr 0) = 0) :
    spPairMatrix s 1 *ᵥ v = v := by
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [spPairMatrix, mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, h1, h2,
      Matrix.one_apply]

end Pair

section Unipotent

variable {F : Type} [Field F]

private def nDisc (s : Matrix (Fin 2) (Fin 2) F) : F := (s 0 0 - s 1 1) ^ 2 + 4 * (s 0 1 * s 1 0)

private def nDelta (s : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  !![s 0 0 - s 1 1, 2 * s 0 1; 2 * s 1 0, s 1 1 - s 0 0]

private def nOff (s : Matrix (Fin 2) (Fin 2) F) (α β : F) : Matrix (Fin 2) (Fin 2) F :=
  !![α * (s 0 0 - s 1 1) + β * nDisc s, 2 * α * s 0 1;
    2 * α * s 1 0, α * (s 1 1 - s 0 0) + β * nDisc s]

private def nMat (s : Matrix (Fin 2) (Fin 2) F) (α β : F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.of fun x y =>
    ![![nDelta s, nOff s α β], ![nOff s α (-β), -nDelta s]] (spIdx x).1 (spIdx y).1 (spIdx x).2
      (spIdx y).2

private theorem nMat_mul_self {s : Matrix (Fin 2) (Fin 2) F} {α β : F}
    (hn : α ^ 2 - nDisc s * β ^ 2 = -1) : nMat s α β * nMat s α β = 0 := by
  simp only [nDisc] at hn
  ext x y
  rcases x with i | i <;> rcases y with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [nMat, nDelta, nOff, nDisc, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination ((s 0 0 - s 1 1) ^ 2 + 4 * (s 0 1 * s 1 0)) * hn

private theorem nMat_lie (s : Matrix (Fin 2) (Fin 2) F) (α β : F) :
    (nMat s α β)ᵀ * fromBlocks 0 1 (-1) 0 = -(fromBlocks 0 1 (-1) 0 * nMat s α β) := by
  ext x y
  rcases x with i | i <;> rcases y with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [nMat, nDelta, nOff, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] <;> ring1

private theorem nMat_comm (s : Matrix (Fin 2) (Fin 2) F) (α β : F) :
    nMat s α β * spPairMatrix s s = spPairMatrix s s * nMat s α β := by
  ext x y
  rcases x with i | i <;> rcases y with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [nMat, nDelta, nOff, spPairMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two] <;> ring1

private theorem exists_gl_one_add {N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hN : N * N = 0) : ∃ R : GL (Fin 2 ⊕ Fin 2) F, (R : Matrix _ _ F) = 1 + N :=
  ⟨⟨1 + N, 1 - N,
    by rw [mul_sub, mul_one, add_mul, one_mul, hN, add_zero, add_sub_cancel_right],
    by rw [sub_mul, one_mul, mul_add, mul_one, hN, add_zero, add_sub_cancel_right]⟩, rfl⟩

private theorem one_add_mem_sp {R : GL (Fin 2 ⊕ Fin 2) F}
    {N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hR : (R : Matrix _ _ F) = 1 + N)
    (hL : Nᵀ * fromBlocks 0 1 (-1) 0 = -(fromBlocks 0 1 (-1) 0 * N)) (hN : N * N = 0) :
    R ∈ CFSG.Open.StatedSp 2 F := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff, hR,
    transpose_add, transpose_one, add_mul, one_mul, mul_add, mul_one, add_mul, hL, neg_mul,
    mul_assoc, hN, mul_zero, neg_zero, add_zero]
  abel

private theorem one_add_pow {N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (hN : N * N = 0)
    (k : ℕ) : (1 + N) ^ k = 1 + (k : F) • N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hN, smul_zero, add_zero,
      Nat.cast_succ, add_smul, one_smul]
    abel

end Unipotent

section Orbit

variable {F : Type} [Field F] {G : Subgroup (GL (Fin 2 ⊕ Fin 2) F)}

private def vec4 (x₀ y₀ x₁ y₁ : F) : Fin 2 ⊕ Fin 2 → F := Sum.elim ![x₀, x₁] ![y₀, y₁]

omit [Field F] in
private theorem eq_vec4 (v : Fin 2 ⊕ Fin 2 → F) :
    v = vec4 (v (.inl 0)) (v (.inr 0)) (v (.inl 1)) (v (.inr 1)) := by
  funext x
  rcases x with i | i <;> fin_cases i <;> rfl

private theorem spTrans_vec4_mulVec (a b c d : F) (k x₀ y₀ x₁ y₁ : F) :
    (spTrans (vec4 a b c d) k : Matrix _ _ F) *ᵥ vec4 x₀ y₀ x₁ y₁ =
      vec4 (x₀ + k * (x₀ * b - y₀ * a + x₁ * d - y₁ * c) * a)
        (y₀ + k * (x₀ * b - y₀ * a + x₁ * d - y₁ * c) * b)
        (x₁ + k * (x₀ * b - y₀ * a + x₁ * d - y₁ * c) * c)
        (y₁ + k * (x₀ * b - y₀ * a + x₁ * d - y₁ * c) * d) := by
  rw [spTrans_mulVec, spForm_apply]
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp only [vec4, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Sum.elim_inl, Sum.elim_inr,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta,
      Fin.mk_one] <;> ring

private theorem spTrans_e₀_mulVec (k x₀ y₀ x₁ y₁ : F) :
    (spTrans (vec4 1 0 0 0) k : Matrix _ _ F) *ᵥ vec4 x₀ y₀ x₁ y₁ =
      vec4 (x₀ - k * y₀) y₀ x₁ y₁ := by
  rw [spTrans_vec4_mulVec]; congr 1 <;> ring

private theorem spTrans_f₀_mulVec (k x₀ y₀ x₁ y₁ : F) :
    (spTrans (vec4 0 1 0 0) k : Matrix _ _ F) *ᵥ vec4 x₀ y₀ x₁ y₁ =
      vec4 x₀ (y₀ + k * x₀) x₁ y₁ := by
  rw [spTrans_vec4_mulVec]; congr 1 <;> ring

private theorem spTrans_e₁_mulVec (k x₀ y₀ x₁ y₁ : F) :
    (spTrans (vec4 0 0 1 0) k : Matrix _ _ F) *ᵥ vec4 x₀ y₀ x₁ y₁ =
      vec4 x₀ y₀ (x₁ - k * y₁) y₁ := by
  rw [spTrans_vec4_mulVec]; congr 1 <;> ring

private theorem spTrans_f₁_mulVec (k x₀ y₀ x₁ y₁ : F) :
    (spTrans (vec4 0 0 0 1) k : Matrix _ _ F) *ᵥ vec4 x₀ y₀ x₁ y₁ =
      vec4 x₀ y₀ x₁ (y₁ + k * x₁) := by
  rw [spTrans_vec4_mulVec]; congr 1 <;> ring

private theorem spTrans_mulVec_mem (hG : G ≤ CFSG.Open.StatedSp 2 F) {g : GL (Fin 2 ⊕ Fin 2) F}
    (hg : g ∈ G) {v : Fin 2 ⊕ Fin 2 → F} (hv : ∀ c, spTrans v c ∈ G) (c : F) :
    spTrans ((g : Matrix _ _ F) *ᵥ v) c ∈ G := by
  rw [← conj_spTrans (hG hg)]
  exact G.mul_mem (G.mul_mem hg (hv c)) (G.inv_mem hg)

private theorem plane_reach {Q : F → F → Prop} (h₁ : ∀ a b a', b ≠ 0 → Q a b → Q a' b)
    (h₂ : ∀ a b b', a ≠ 0 → Q a b → Q a b') {a b : F} (hab : a ≠ 0 ∨ b ≠ 0) (hQ : Q a b)
    {x y : F} (hxy : x ≠ 0 ∨ y ≠ 0) : Q x y := by
  have h11 : Q 1 1 := by
    rcases hab with ha | hb
    · exact h₁ _ _ _ one_ne_zero (h₂ a b 1 ha hQ)
    · exact h₂ _ _ _ one_ne_zero (h₁ a b 1 hb hQ)
  rcases hxy with hx | hy
  · exact h₂ x 1 y hx (h₁ 1 1 x one_ne_zero h11)
  · exact h₁ 1 y x hy (h₂ 1 1 y one_ne_zero h11)

private theorem reach_plane0 (hG : G ≤ CFSG.Open.StatedSp 2 F)
    (he : ∀ c, spTrans (vec4 1 0 0 0) c ∈ G) (hf : ∀ c, spTrans (vec4 0 1 0 0) c ∈ G)
    {x₁ y₁ a b : F} (hab : a ≠ 0 ∨ b ≠ 0) (hr : ∀ c, spTrans (vec4 a b x₁ y₁) c ∈ G)
    {x y : F} (hxy : x ≠ 0 ∨ y ≠ 0) : ∀ c, spTrans (vec4 x y x₁ y₁) c ∈ G := by
  refine plane_reach (Q := fun a b => ∀ c, spTrans (vec4 a b x₁ y₁) c ∈ G) ?_ ?_ hab hr hxy
  · intro a b a' hb h
    have := spTrans_mulVec_mem hG (he ((a - a') / b)) h
    rwa [spTrans_e₀_mulVec, show a - (a - a') / b * b = a' by field_simp; ring] at this
  · intro a b b' ha h
    have := spTrans_mulVec_mem hG (hf ((b' - b) / a)) h
    rwa [spTrans_f₀_mulVec, show b + (b' - b) / a * a = b' by field_simp; ring] at this

private theorem reach_plane1 (hG : G ≤ CFSG.Open.StatedSp 2 F)
    (he : ∀ c, spTrans (vec4 0 0 1 0) c ∈ G) (hf : ∀ c, spTrans (vec4 0 0 0 1) c ∈ G)
    {x₀ y₀ a b : F} (hab : a ≠ 0 ∨ b ≠ 0) (hr : ∀ c, spTrans (vec4 x₀ y₀ a b) c ∈ G)
    {x y : F} (hxy : x ≠ 0 ∨ y ≠ 0) : ∀ c, spTrans (vec4 x₀ y₀ x y) c ∈ G := by
  refine plane_reach (Q := fun a b => ∀ c, spTrans (vec4 x₀ y₀ a b) c ∈ G) ?_ ?_ hab hr hxy
  · intro a b a' hb h
    have := spTrans_mulVec_mem hG (he ((a - a') / b)) h
    rwa [spTrans_e₁_mulVec, show a - (a - a') / b * b = a' by field_simp; ring] at this
  · intro a b b' ha h
    have := spTrans_mulVec_mem hG (hf ((b' - b) / a)) h
    rwa [spTrans_f₁_mulVec, show b + (b' - b) / a * a = b' by field_simp; ring] at this

private theorem spTrans_mem_of_mixed (hG : G ≤ CFSG.Open.StatedSp 2 F)
    (h₀ : ∀ v : Fin 2 ⊕ Fin 2 → F, v (.inl 1) = 0 → v (.inr 1) = 0 → ∀ c, spTrans v c ∈ G)
    (h₁ : ∀ v : Fin 2 ⊕ Fin 2 → F, v (.inl 0) = 0 → v (.inr 0) = 0 → ∀ c, spTrans v c ∈ G)
    {r : Fin 2 ⊕ Fin 2 → F} (hr : ∀ c, spTrans r c ∈ G) (hr₀ : r (.inl 0) ≠ 0 ∨ r (.inr 0) ≠ 0)
    (hr₁ : r (.inl 1) ≠ 0 ∨ r (.inr 1) ≠ 0) (v : Fin 2 ⊕ Fin 2 → F) (c : F) :
    spTrans v c ∈ G := by
  by_cases hv₁ : v (.inl 1) = 0 ∧ v (.inr 1) = 0
  · exact h₀ v hv₁.1 hv₁.2 c
  by_cases hv₀ : v (.inl 0) = 0 ∧ v (.inr 0) = 0
  · exact h₁ v hv₀.1 hv₀.2 c
  rw [not_and_or] at hv₀ hv₁
  rw [eq_vec4 r] at hr
  rw [eq_vec4 v]
  refine reach_plane1 hG (h₁ _ rfl rfl) (h₁ _ rfl rfl) hr₁ ?_ hv₁ c
  exact reach_plane0 hG (h₀ _ rfl rfl) (h₀ _ rfl rfl) hr₀ hr hv₀

end Orbit

section Mixed

variable {F : Type} [Field F]

private theorem exists_mixed_col {s : Matrix (Fin 2) (Fin 2) F} {α β : F} (h2 : (2 : F) ≠ 0)
    (hΔ : nDisc s ≠ 0) (hn : α ^ 2 - nDisc s * β ^ 2 = -1) :
    ∃ j : Fin 2 ⊕ Fin 2, (j = .inl 0 ∨ j = .inr 0) ∧
      ((1 + nMat s α β) (.inl 0) j ≠ 0 ∨ (1 + nMat s α β) (.inr 0) j ≠ 0) ∧
      ((1 + nMat s α β) (.inl 1) j ≠ 0 ∨ (1 + nMat s α β) (.inr 1) j ≠ 0) := by
  simp only [nDisc] at hΔ hn
  by_cases h : (1 + nMat s α β) (.inl 0) (.inl 0) ≠ 0 ∨ (1 + nMat s α β) (.inr 0) (.inl 0) ≠ 0
  · refine ⟨.inl 0, .inl rfl, h, ?_⟩
    by_contra hc
    push Not at hc
    simp [nMat, nOff, nDisc, -mul_eq_zero] at hc
    exact hΔ (by linear_combination (α * (s 1 1 - s 0 0) + -β * ((s 0 0 - s 1 1) ^ 2 +
      4 * (s 0 1 * s 1 0))) * hc.1 - 2 * α * s 0 1 * hc.2 +
      ((s 0 0 - s 1 1) ^ 2 + 4 * (s 0 1 * s 1 0)) * hn)
  · refine ⟨.inr 0, .inr rfl, ?_, ?_⟩
    · push Not at h
      simp [nMat, nDelta] at h ⊢
      right
      intro h'
      exact h2 (by linear_combination h.1 + h')
    · by_contra hc
      push Not at hc
      simp [nMat, nOff, nDisc, -mul_eq_zero] at hc
      exact hΔ (by linear_combination (α * (s 0 0 - s 1 1) + -β * ((s 0 0 - s 1 1) ^ 2 +
        4 * (s 0 1 * s 1 0))) * hc.2 - 2 * α * s 1 0 * hc.1 +
        ((s 0 0 - s 1 1) ^ 2 + 4 * (s 0 1 * s 1 0)) * hn)

end Mixed

section ZModQ

variable {q : ℕ} [Fact q.Prime]

private theorem two_ne_zero_zmod (hq2 : q ≠ 2) : (2 : ZMod q) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
  exact hq2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1
    ((ZMod.natCast_eq_zero_iff 2 q).1 h'))

private theorem exists_sq_sub_mul_sq {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K % 2 = 1) {D : K} (hD : D ≠ 0) : ∃ α β : K, α ^ 2 - D * β ^ 2 = -1 := by
  open Polynomial in
  obtain ⟨a, b, h⟩ := FiniteField.exists_root_sum_quadratic (f := X ^ 2 + C 1)
    (g := C (-D) * X ^ 2) (degree_X_pow_add_C two_pos _) (degree_C_mul_X_pow 2 (neg_ne_zero.2 hD))
    hK
  refine ⟨a, b, ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X] at h
  linear_combination h

private theorem spTrans_pow_q (v : Fin 2 ⊕ Fin 2 → ZMod q) (c : ZMod q) : spTrans v c ^ q = 1 := by
  rw [spTrans_npow, ZMod.natCast_self, zero_mul, spTrans_zero]

private theorem not_dvd_orderOf_of_pow_q {p : ℕ} (hp : p.Prime) (hpq : p ≠ q) {M : Type*}
    [Monoid M] {x : M} (hx : x ^ q = 1) : ¬ p ∣ orderOf x := fun h =>
  hpq ((Nat.prime_dvd_prime_iff_eq hp Fact.out).1 (h.trans (orderOf_dvd_of_pow_eq_one hx)))

private theorem spTrans_mem_fixSetSp {p : ℕ} (hp : p.Prime) (hpq : p ≠ q)
    {E : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q))} {h : GL (Fin 2 ⊕ Fin 2) (ZMod q)} (hE : h ∈ E)
    (h1 : h ≠ 1) (hSp : h ∈ CFSG.Open.StatedSp 2 (ZMod q)) {v : Fin 2 ⊕ Fin 2 → ZMod q}
    (hv : (h : Matrix _ _ (ZMod q)) *ᵥ v = v) (c : ZMod q) : spTrans v c ∈ fixSetSp p E := by
  refine ⟨spTrans_mem_statedSp v c, not_dvd_orderOf_of_pow_q hp hpq (spTrans_pow_q v c), h, hE, h1,
    ?_⟩
  have := conj_spTrans hSp v c
  rw [hv] at this
  exact mul_inv_eq_iff_eq_mul.1 this

private theorem sq_eq_trace_smul_sub_one' {K : Type} [Field K] {M : Matrix (Fin 2) (Fin 2) K}
    (hdet : M.det = 1) : M ^ 2 = M.trace • M - 1 := by
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
    first | ring1 | linear_combination -hdet

private theorem pow_eq_of_trace' {K : Type} [Field K] {M : Matrix (Fin 2) (Fin 2) K}
    (hdet : M.det = 1) {ε : K} (hε : ε ^ 2 = 1) (htr : M.trace = 2 * ε) (k : ℕ) :
    M ^ (k + 1) = (((k + 1 : ℕ) : K) * ε ^ k) • M - ((k : K) * ε ^ (k + 1)) • 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsq := sq_eq_trace_smul_sub_one' hdet
    rw [htr] at hsq
    rw [pow_succ, ih, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, ← sq, hsq]
    have hε3 : ε ^ (k + 2) = ε ^ k := by rw [pow_add, hε, mul_one]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Nat.cast_add, Nat.cast_one]
    rw [show k + 1 + 1 = k + 2 by ring, hε3, pow_succ ε k]
    ring

private theorem nDisc_ne_zero {K : Type} [Field K] [CharP K q] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ≠ q) {s₀ : GL (Fin 2) K} (hdet : (s₀ : Matrix (Fin 2) (Fin 2) K).det = 1)
    (hord : orderOf s₀ = p) : nDisc (s₀ : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
  set M := (s₀ : Matrix (Fin 2) (Fin 2) K)
  intro h0
  have hfac : (M.trace - 2) * (M.trace + 2) = 0 := by
    have hd := hdet
    rw [Matrix.det_fin_two] at hd
    simp only [nDisc] at h0
    rw [Matrix.trace_fin_two]
    linear_combination h0 + 4 * hd
  obtain ⟨ε, hε, htr⟩ : ∃ ε : K, ε ^ 2 = 1 ∧ M.trace = 2 * ε := by
    rcases mul_eq_zero.1 hfac with h | h
    · exact ⟨1, by ring, by linear_combination h⟩
    · exact ⟨-1, by ring, by linear_combination h⟩
  have hq1 : 1 ≤ q := (Fact.out : q.Prime).one_lt.le
  have hpow := pow_eq_of_trace' hdet hε htr (q - 1)
  rw [Nat.sub_add_cancel hq1, CharP.cast_eq_zero K q, zero_mul, zero_smul, zero_sub,
    Nat.cast_sub hq1, CharP.cast_eq_zero K q, Nat.cast_one, zero_sub, neg_one_mul, neg_smul,
    neg_neg] at hpow
  have h2q : s₀ ^ (2 * q) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_mul', hpow, smul_pow, one_pow, ← pow_mul, mul_comm q 2,
      pow_mul, hε, one_pow, one_smul, Units.val_one]
  rcases (Nat.Prime.dvd_mul hp).1 (hord ▸ orderOf_dvd_of_pow_eq_one h2q) with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  · exact hpq ((Nat.prime_dvd_prime_iff_eq hp Fact.out).1 h)

private theorem exists_unipotent_mixed (hq2 : q ≠ 2) {p : ℕ} (hp : p.Prime) (hpq : p ≠ q)
    {E : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q))} {g : GL (Fin 2 ⊕ Fin 2) (ZMod q)} (hgE : g ∈ E)
    (hg1 : g ≠ 1) {s : Matrix (Fin 2) (Fin 2) (ZMod q)}
    (hg : (g : Matrix _ _ (ZMod q)) = spPairMatrix s s) (hΔ : nDisc s ≠ 0) :
    ∃ R ∈ fixSetSp p E, ∃ j : Fin 2 ⊕ Fin 2, (j = .inl 0 ∨ j = .inr 0) ∧
      ((R : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod q)) (.inl 0) j ≠ 0 ∨
        (R : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod q)) (.inr 0) j ≠ 0) ∧
      ((R : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod q)) (.inl 1) j ≠ 0 ∨
        (R : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod q)) (.inr 1) j ≠ 0) := by
  have hK : Fintype.card (ZMod q) % 2 = 1 := by
    rw [ZMod.card]
    exact (Nat.Prime.eq_two_or_odd Fact.out).resolve_left hq2
  obtain ⟨α, β, hn⟩ := exists_sq_sub_mul_sq hK hΔ
  have hN := nMat_mul_self hn
  obtain ⟨R, hR⟩ := exists_gl_one_add hN
  have hRq : R ^ q = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, hR, one_add_pow hN, ZMod.natCast_self, zero_smul, add_zero,
      Units.val_one])
  have hcomm : g * R = R * g := Units.ext (by
    rw [Units.val_mul, Units.val_mul, hg, hR, mul_add, add_mul, mul_one, one_mul, nMat_comm])
  obtain ⟨j, hj, h0, h1⟩ := exists_mixed_col (two_ne_zero_zmod hq2) hΔ hn
  refine ⟨R, ⟨one_add_mem_sp hR (nMat_lie _ _ _) hN, not_dvd_orderOf_of_pow_q hp hpq hRq, g, hgE,
    hg1, hcomm⟩, j, hj, ?_, ?_⟩ <;> rw [hR] <;> assumption

end ZModQ

theorem closure_fixSetSp_of_spPair {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ≠ q) (_hdvd : p ∣ q + 1) {E : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q))}
    {s₀ : GL (Fin 2) (ZMod q)} (hdet : (s₀ : Matrix (Fin 2) (Fin 2) (ZMod q)).det = 1)
    (hord : orderOf s₀ = p)
    (h₀ : ∃ g ∈ E,
      (g : Matrix _ _ (ZMod q)) = spPairMatrix (s₀ : Matrix (Fin 2) (Fin 2) (ZMod q)) 1)
    (h₁ : ∃ g ∈ E,
      (g : Matrix _ _ (ZMod q)) = spPairMatrix 1 (s₀ : Matrix (Fin 2) (Fin 2) (ZMod q))) :
    Subgroup.closure (fixSetSp p E) = CFSG.Open.StatedSp 2 (ZMod q) := by
  obtain ⟨g₀, hg₀E, hg₀⟩ := h₀
  obtain ⟨g₁, hg₁E, hg₁⟩ := h₁
  set s := (s₀ : Matrix (Fin 2) (Fin 2) (ZMod q)) with hs
  have hs1 : s ≠ 1 := fun h => by
    have h' : s₀ = 1 := Units.ext h
    rw [h', orderOf_one] at hord
    exact hp.one_lt.ne hord
  have hG : Subgroup.closure (fixSetSp p E) ≤ CFSG.Open.StatedSp 2 (ZMod q) :=
    (Subgroup.closure_le _).2 fun x hx => hx.1
  have hU₀ : ∀ v : Fin 2 ⊕ Fin 2 → ZMod q, v (.inl 1) = 0 → v (.inr 1) = 0 →
      ∀ c, spTrans v c ∈ Subgroup.closure (fixSetSp p E) := fun v h1 h2 c =>
    Subgroup.subset_closure (spTrans_mem_fixSetSp hp hpq hg₁E
      (fun h => hs1 (eq_one_of_spPairMatrix_eq_one (by rw [← hg₁, h, Units.val_one])).2)
      (spPair_mem hg₁ det_one hdet) (by rw [hg₁]; exact spPairMatrix_one_left_mulVec _ h1 h2) c)
  have hU₁ : ∀ v : Fin 2 ⊕ Fin 2 → ZMod q, v (.inl 0) = 0 → v (.inr 0) = 0 →
      ∀ c, spTrans v c ∈ Subgroup.closure (fixSetSp p E) := fun v h1 h2 c =>
    Subgroup.subset_closure (spTrans_mem_fixSetSp hp hpq hg₀E
      (fun h => hs1 (eq_one_of_spPairMatrix_eq_one (by rw [← hg₀, h, Units.val_one])).1)
      (spPair_mem hg₀ hdet det_one) (by rw [hg₀]; exact spPairMatrix_one_right_mulVec _ h1 h2) c)
  have hg : ((g₀ * g₁ : GL _ (ZMod q)) : Matrix _ _ (ZMod q)) = spPairMatrix s s := by
    rw [Units.val_mul, hg₀, hg₁, spPairMatrix_mul, mul_one, one_mul]
  obtain ⟨R, hRE, j, hj, hr₀, hr₁⟩ := exists_unipotent_mixed hq2 hp hpq (E.mul_mem hg₀E hg₁E)
    (fun h => hs1 (eq_one_of_spPairMatrix_eq_one (by rw [← hg, h, Units.val_one])).1) hg
    (nDisc_ne_zero hp hp2 hpq hdet hord)
  have hj₁ : (Pi.single j 1 : Fin 2 ⊕ Fin 2 → ZMod q) (.inl 1) = 0 ∧
      (Pi.single j 1 : Fin 2 ⊕ Fin 2 → ZMod q) (.inr 1) = 0 := by
    rcases hj with rfl | rfl <;> simp
  have hr := spTrans_mulVec_mem hG (Subgroup.subset_closure hRE) (hU₀ _ hj₁.1 hj₁.2)
  refine le_antisymm hG ?_
  rw [statedSp_eq_closure_spTrans, Subgroup.closure_le]
  rintro _ ⟨a, c, rfl⟩
  exact spTrans_mem_of_mixed hG hU₀ hU₁ hr (by simpa [Matrix.mulVec_single] using hr₀)
    (by simpa [Matrix.mulVec_single] using hr₁) a c

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
