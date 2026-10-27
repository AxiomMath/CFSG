module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import Mathlib.LinearAlgebra.Matrix.IsDiag

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

open Matrix CFSG.LocalAnalysis.ComponentInitial

section Norm

variable {G : Type*} [Group G]

@[expose] def triNorm (s : G →* G) (m : G) : G := m * s m * s (s m)

theorem triNorm_one (s : G →* G) : triNorm s 1 = 1 := by
  simp [triNorm]

theorem triNorm_fixed [IsMulCommutative G] (s : G →* G) (hs3 : ∀ x, s (s (s x)) = x) (m : G) :
    s (triNorm s m) = triNorm s m := by
  simp only [triNorm, map_mul, hs3]
  ac_rfl

theorem norm_identity [IsMulCommutative G] (s t p r : G →* G) (hst : ∀ x, s (t x) = t (s x))
    (ht3 : ∀ x, t (t (t x)) = x) (hp : ∀ x, p x = s (t x)) (hr : ∀ x, r x = s (t (t x)))
    (m : G) :
    triNorm s m * triNorm t m * triNorm p m * triNorm r m = m ^ 3 * triNorm s (triNorm t m) := by
  simp only [triNorm, hp, hr]
  have e1 : s (t (s (t m))) = s (s (t (t m))) := by rw [hst (t m)]
  have e2 : s (t (t (s (t (t m))))) = s (s (t m)) := by
    rw [← hst (t (t m)), ht3, ← hst m]
  rw [e1, e2]
  simp only [map_mul, pow_three]
  ac_rfl

@[expose] def conjOn (A : Subgroup G) (w : G) (hw : ∀ x ∈ A, w * x * w⁻¹ ∈ A) : A →* A where
  toFun x := ⟨w * x * w⁻¹, hw x x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjOn_apply (A : Subgroup G) (w : G) (hw : ∀ x ∈ A, w * x * w⁻¹ ∈ A) (x : A) :
    ((conjOn A w hw x : A) : G) = w * x * w⁻¹ :=
  rfl

end Norm

section Diagonal

variable {K : Type} [Field K] {n : ℕ}

theorem mul_diag_apply {t e : Matrix (Fin n) (Fin n) K} (he : e.IsDiag) (i j : Fin n) :
    (t * e) i j = t i j * e j j := by
  conv_lhs => rw [← he.diagonal_diag]
  rw [mul_diagonal]
  rfl

theorem diag_mul_apply {t e : Matrix (Fin n) (Fin n) K} (he : e.IsDiag) (i j : Fin n) :
    (e * t) i j = e i i * t i j := by
  conv_lhs => rw [← he.diagonal_diag]
  rw [diagonal_mul]
  rfl

theorem isDiag_pow {x : Matrix (Fin n) (Fin n) K} (hx : x.IsDiag) (a : ℕ) : (x ^ a).IsDiag := by
  rw [← hx.diagonal_diag, diagonal_pow]
  exact isDiag_diagonal _

theorem pow_apply_diag {x : Matrix (Fin n) (Fin n) K} (hx : x.IsDiag) (a : ℕ) (i : Fin n) :
    (x ^ a) i i = x i i ^ a := by
  conv_lhs => rw [← hx.diagonal_diag]
  rw [diagonal_pow, diagonal_apply_eq]
  rfl

theorem mul_apply_diag {x y : Matrix (Fin n) (Fin n) K} (hx : x.IsDiag) (i : Fin n) :
    (x * y) i i = x i i * y i i :=
  diag_mul_apply hx i i

theorem isDiag_commute {x y : Matrix (Fin n) (Fin n) K} (hx : x.IsDiag) (hy : y.IsDiag) :
    x * y = y * x := by
  rw [← hx.diagonal_diag, ← hy.diagonal_diag, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem diag_ne_zero {d : GL (Fin n) K} (hd : (d : Matrix (Fin n) (Fin n) K).IsDiag) (i : Fin n) :
    (d : Matrix (Fin n) (Fin n) K) i i ≠ 0 := by
  intro h0
  have h1 : ((d : Matrix (Fin n) (Fin n) K) *
      ((d⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i i = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_apply_eq]
  rw [diag_mul_apply hd, h0, zero_mul] at h1
  exact zero_ne_one h1

theorem apply_eq_zero_of_commute {t e : Matrix (Fin n) (Fin n) K} (he : e.IsDiag)
    (hte : t * e = e * t) {i j : Fin n} (hij : e i i ≠ e j j) : t i j = 0 := by
  have h1 := congrFun (congrFun hte i) j
  rw [mul_diag_apply he, diag_mul_apply he] at h1
  have h2 : t i j * (e j j - e i i) = 0 := by rw [mul_sub, h1]; ring
  rcases mul_eq_zero.1 h2 with h | h
  · exact h
  · exact absurd (sub_eq_zero.1 h).symm hij

theorem eq_of_pow_eq_of_cube {y z : K} (hy : y ^ 3 = 1) (hz : z ^ 3 = 1) {a : ℕ} (ha : ¬3 ∣ a)
    (hyz : y ^ a = z ^ a) : y = z := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  have h1 : (y * z⁻¹) ^ 3 = 1 := by rw [mul_pow, inv_pow, hy, hz, inv_one, mul_one]
  have h2 : (y * z⁻¹) ^ a = 1 := by
    rw [mul_pow, inv_pow, hyz, mul_inv_cancel₀ (pow_ne_zero a hz0)]
  have hcop : Nat.Coprime a 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ha).symm
  have h3 := (pow_gcd_eq_one (a := y * z⁻¹) (m := a) (n := 3)).2 ⟨h2, h1⟩
  rw [hcop, pow_one] at h3
  exact (mul_inv_eq_one₀ hz0).1 h3

end Diagonal

variable {ℓ f : ℕ} {K : Type} [Field K] {n : ℕ}

structure IsFullDiag (D : Subgroup (GL (Fin n) K)) : Prop where
  diag : ∀ d ∈ D, (d : Matrix (Fin n) (Fin n) K).IsDiag
  cube : ∀ d ∈ D, d ^ 3 = 1
  sep : ∀ i j : Fin n, i ≠ j → ∃ d ∈ D,
    (d : Matrix (Fin n) (Fin n) K) i i ≠ (d : Matrix (Fin n) (Fin n) K) j j
  three : ∀ i j l : Fin n, i ≠ j → i ≠ l → j ≠ l → ∃ d ∈ D,
    (d : Matrix (Fin n) (Fin n) K) i i ≠ (d : Matrix (Fin n) (Fin n) K) l l ∧
      (d : Matrix (Fin n) (Fin n) K) j j = (d : Matrix (Fin n) (Fin n) K) l l

theorem eq_one_of_norm_eq_one (h : UnitaryFieldData ℓ f K) {k : ℕ} (hq : ℓ ^ f + 1 = 3 ^ k)
    {c : K} (hc : c * h.bar c = 1) {m : ℕ} (hm : Nat.Coprime 3 m) (hcm : c ^ m = 1) : c = 1 := by
  have h1 : c ^ (3 ^ k) = 1 := by
    rw [← hq, pow_succ, ← h.bar_apply, mul_comm, hc]
  have h2 : Nat.Coprime m (3 ^ k) := Nat.Coprime.pow_right k hm.symm
  have h3 := (pow_gcd_eq_one (a := c) (m := m) (n := 3 ^ k)).2 ⟨hcm, h1⟩
  rwa [h2, pow_one] at h3

theorem eq_one_of_isDiag (h : UnitaryFieldData ℓ f K) {k : ℕ} (hq : ℓ ^ f + 1 = 3 ^ k)
    {T : Matrix (Fin n) (Fin n) K} (hT : T.IsDiag) (hU : (T.map h.bar)ᵀ * T = 1) {m : ℕ}
    (hm : Nat.Coprime 3 m) (hTm : T ^ m = 1) : T = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [one_apply_eq]
    have h1 : h.bar (T i i) * T i i = 1 := by
      have h2 := congrFun (congrFun hU i) i
      rwa [mul_apply, Finset.sum_eq_single i, transpose_apply, map_apply, one_apply_eq] at h2
      · intro k _ hk
        rw [transpose_apply, map_apply, hT hk, map_zero, zero_mul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    have h3 := congrFun (congrFun hTm i) i
    rw [pow_apply_diag hT, one_apply_eq] at h3
    exact eq_one_of_norm_eq_one h hq (by rw [mul_comm]; exact h1) hm h3
  · rw [one_apply_ne hij]
    exact hT hij

theorem block_offDiag (h : UnitaryFieldData ℓ f K) {T X : Matrix (Fin n) (Fin n) K}
    (hX : X.IsDiag) {i j : Fin n} (hij : i ≠ j)
    (hsupp : ∀ k, k ≠ i ∧ k ≠ j → T i k = 0 ∧ T k i = 0) (hxi : X i i ≠ 0) (hxj : X j j ≠ 0)
    (hxij : X i i ≠ X j j) (hc : T * (X * T * X ^ 2) = X * T * X ^ 2 * T)
    (hU : (T.map h.bar)ᵀ * T = 1) (hU' : T * (T.map h.bar)ᵀ = 1) : T i j = 0 ∧ T j i = 0 := by
  have hent : ∀ a b, (X * T * X ^ 2) a b = X a a * T a b * X b b ^ 2 := fun a b => by
    rw [mul_diag_apply (isDiag_pow hX 2), diag_mul_apply hX, pow_apply_diag hX]
  have e1 := congrFun (congrFun hc i) i
  rw [mul_apply, mul_apply] at e1
  simp only [hent] at e1
  have s1 : ∑ k, T i k * (X k k * T k i * X i i ^ 2) =
      T i i * (X i i * T i i * X i i ^ 2) + T i j * (X j j * T j i * X i i ^ 2) :=
    Fintype.sum_eq_add i j hij fun k hk => by rw [(hsupp k hk).1, zero_mul]
  have s2 : ∑ k, X i i * T i k * X k k ^ 2 * T k i =
      X i i * T i i * X i i ^ 2 * T i i + X i i * T i j * X j j ^ 2 * T j i :=
    Fintype.sum_eq_add i j hij fun k hk => by rw [(hsupp k hk).2, mul_zero]
  rw [s1, s2] at e1
  have key : T i j * T j i * (X i i * X j j * (X i i - X j j)) = 0 := by linear_combination e1
  have hprod : T i j * T j i = 0 :=
    (mul_eq_zero.1 key).resolve_right (mul_ne_zero (mul_ne_zero hxi hxj) (sub_ne_zero.2 hxij))
  have u1 := congrFun (congrFun hU i) i
  rw [mul_apply, one_apply_eq] at u1
  simp only [transpose_apply, map_apply] at u1
  have u1' : ∑ k, h.bar (T k i) * T k i = h.bar (T i i) * T i i + h.bar (T j i) * T j i :=
    Fintype.sum_eq_add i j hij fun k hk => by rw [(hsupp k hk).2, mul_zero]
  rw [u1'] at u1
  have u2 := congrFun (congrFun hU' i) i
  rw [mul_apply, one_apply_eq] at u2
  simp only [transpose_apply, map_apply] at u2
  have u2' : ∑ k, T i k * h.bar (T i k) = T i i * h.bar (T i i) + T i j * h.bar (T i j) :=
    Fintype.sum_eq_add i j hij fun k hk => by rw [(hsupp k hk).1, zero_mul]
  rw [u2'] at u2
  have hbar0 : ∀ c : K, h.bar c * c = 0 → c = 0 := fun c hc0 => by
    rcases mul_eq_zero.1 hc0 with h0 | h0
    · exact (map_eq_zero h.bar).1 h0
    · exact h0
  rcases mul_eq_zero.1 hprod with h0 | h0
  · refine ⟨h0, hbar0 _ ?_⟩
    rw [h0, map_zero, mul_zero, add_zero] at u2
    linear_combination u1 - u2
  · refine ⟨hbar0 _ ?_, h0⟩
    rw [h0, map_zero, mul_zero, add_zero] at u1
    linear_combination u2 - u1

theorem eq_one_of_block (h : UnitaryFieldData ℓ f K) {k : ℕ} (hq : ℓ ^ f + 1 = 3 ^ k)
    {D E : Subgroup (GL (Fin n) K)} (hD : IsFullDiag D) (hED : E ≤ D) {d₀ : GL (Fin n) K}
    (hd₀ : d₀ ∈ D) (hdec : ∀ d ∈ D, ∃ a : ℕ, ∃ e ∈ E, d = d₀ ^ a * e) {t : GL (Fin n) K}
    (htE : ∀ e ∈ E, t * e = e * t) (htt : t * (d₀ * t * d₀⁻¹) = d₀ * t * d₀⁻¹ * t)
    (htU : ((t : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * t = 1) {m : ℕ}
    (hm : Nat.Coprime 3 m) (htm : t ^ m = 1) : t = 1 := by
  have hd0 := hD.diag d₀ hd₀
  have hcube : ∀ d ∈ D, ∀ i, (d : Matrix (Fin n) (Fin n) K) i i ^ 3 = 1 := by
    intro d hd i
    have h1 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i i)
      (hD.cube d hd)
    simp only [Units.val_pow_eq_pow_val, Units.val_one, one_apply_eq] at h1
    rwa [pow_apply_diag (hD.diag d hd)] at h1
  have he0 : ∀ e ∈ E, ∀ i, (e : Matrix (Fin n) (Fin n) K) i i ≠ 0 := fun e he =>
    diag_ne_zero (hD.diag e (hED he))
  have hdec' : ∀ d ∈ D, ∃ a : ℕ, ∃ e ∈ E, ∀ i, (d : Matrix (Fin n) (Fin n) K) i i =
      (d₀ : Matrix (Fin n) (Fin n) K) i i ^ a * (e : Matrix (Fin n) (Fin n) K) i i := by
    intro d hd
    obtain ⟨a, e, he, rfl⟩ := hdec d hd
    refine ⟨a, e, he, fun i => ?_⟩
    rw [Units.val_mul, Units.val_pow_eq_pow_val, mul_apply_diag (isDiag_pow hd0 a),
      pow_apply_diag hd0]
  have ha : ∀ i j, (∃ e ∈ E, (e : Matrix (Fin n) (Fin n) K) i i ≠
      (e : Matrix (Fin n) (Fin n) K) j j) → (t : Matrix (Fin n) (Fin n) K) i j = 0 := by
    rintro i j ⟨e, he, hne⟩
    refine apply_eq_zero_of_commute (hD.diag e (hED he)) ?_ hne
    rw [← Units.val_mul, ← Units.val_mul, htE e he]
  have hb : ∀ i j l, i ≠ j → i ≠ l → j ≠ l →
      (∀ e ∈ E, (e : Matrix (Fin n) (Fin n) K) i i = (e : Matrix (Fin n) (Fin n) K) l l) →
      (∀ e ∈ E, (e : Matrix (Fin n) (Fin n) K) j j = (e : Matrix (Fin n) (Fin n) K) l l) →
      False := by
    intro i j l hij hil hjl hi hj
    obtain ⟨d, hd, hd1, hd2⟩ := hD.three i j l hij hil hjl
    obtain ⟨d', hd', hd'1⟩ := hD.sep j l hjl
    obtain ⟨a, e, he, hae⟩ := hdec' d hd
    obtain ⟨b, e', he', hbe'⟩ := hdec' d' hd'
    have h1 : (d₀ : Matrix (Fin n) (Fin n) K) i i ^ a ≠ (d₀ : Matrix (Fin n) (Fin n) K) l l ^ a :=
      fun hh => hd1 (by rw [hae i, hae l, hi e he, hh])
    have h2 : (d₀ : Matrix (Fin n) (Fin n) K) j j ^ a =
        (d₀ : Matrix (Fin n) (Fin n) K) l l ^ a := by
      have h3 := hd2
      rw [hae j, hae l, hj e he] at h3
      exact mul_right_cancel₀ (he0 e he l) h3
    have h3 : ¬3 ∣ a := by
      rintro ⟨c, rfl⟩
      exact h1 (by rw [pow_mul, pow_mul, hcube d₀ hd₀ i, hcube d₀ hd₀ l])
    have h4 := eq_of_pow_eq_of_cube (hcube d₀ hd₀ j) (hcube d₀ hd₀ l) h3 h2
    exact hd'1 (by rw [hbe' j, hbe' l, hj e' he', h4])
  have hc : ∀ i j, i ≠ j →
      (∀ e ∈ E, (e : Matrix (Fin n) (Fin n) K) i i = (e : Matrix (Fin n) (Fin n) K) j j) →
      (d₀ : Matrix (Fin n) (Fin n) K) i i ≠ (d₀ : Matrix (Fin n) (Fin n) K) j j := by
    intro i j hij hR hx
    obtain ⟨d, hd, hdne⟩ := hD.sep i j hij
    obtain ⟨a, e, he, hae⟩ := hdec' d hd
    exact hdne (by rw [hae i, hae j, hR e he, hx])
  have hinv : d₀⁻¹ = d₀ ^ 2 := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', hD.cube d₀ hd₀]
  have hcomm : (t : Matrix (Fin n) (Fin n) K) * ((d₀ : Matrix (Fin n) (Fin n) K) * t *
      (d₀ : Matrix (Fin n) (Fin n) K) ^ 2) = (d₀ : Matrix (Fin n) (Fin n) K) * t *
      (d₀ : Matrix (Fin n) (Fin n) K) ^ 2 * t := by
    rw [hinv] at htt
    have h1 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) htt
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using h1
  have hU' : (t : Matrix (Fin n) (Fin n) K) * ((t : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ = 1 := by
    have h1 : ((t : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ =
        ((t⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← Matrix.mul_one ((t : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ, ← Units.val_one,
        ← mul_inv_cancel t, Units.val_mul, ← Matrix.mul_assoc, htU, Matrix.one_mul]
    rw [h1, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hoff : ∀ i j, i ≠ j → (t : Matrix (Fin n) (Fin n) K) i j = 0 := by
    intro i j hij
    by_cases hR : ∀ e ∈ E, (e : Matrix (Fin n) (Fin n) K) i i = (e : Matrix (Fin n) (Fin n) K) j j
    · refine (block_offDiag h hd0 hij (fun k hk => ?_) (diag_ne_zero hd0 i) (diag_ne_zero hd0 j)
        (hc i j hij hR) hcomm htU hU').1
      have hk' : ∃ e ∈ E, (e : Matrix (Fin n) (Fin n) K) i i ≠
          (e : Matrix (Fin n) (Fin n) K) k k := by
        by_contra hcon
        push Not at hcon
        exact hb j k i (Ne.symm hk.2) hij.symm hk.1 (fun e he => (hR e he).symm)
          (fun e he => (hcon e he).symm)
      obtain ⟨e, he, hne⟩ := hk'
      exact ⟨ha i k ⟨e, he, hne⟩, ha k i ⟨e, he, Ne.symm hne⟩⟩
    · push Not at hR
      exact ha i j hR
  apply Units.ext
  rw [Units.val_one]
  refine eq_one_of_isDiag h hq (fun i j hij => hoff i j hij) htU hm ?_
  rw [← Units.val_pow_eq_pow_val, htm, Units.val_one]

theorem eq_bot_of_full (h : UnitaryFieldData ℓ f K) {k : ℕ} (hq : ℓ ^ f + 1 = 3 ^ k)
    {D : Subgroup (GL (Fin n) K)} (hD : IsFullDiag D) {A : Subgroup (GL (Fin n) K)}
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAD : ∀ d ∈ D, ∀ x ∈ A, d * x * d⁻¹ ∈ A)
    (hAU : ∀ x ∈ A, ((x : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * x = 1)
    (hA3 : ∀ x ∈ A, Nat.Coprime 3 (orderOf x)) : A = ⊥ := by
  haveI : Finite K := h.finite
  haveI : Finite (Matrix (Fin n) (Fin n) K) := inferInstanceAs (Finite (Fin n → Fin n → K))
  haveI : Finite (GL (Fin n) K) :=
    Finite.of_injective (Units.val : GL (Fin n) K → Matrix (Fin n) (Fin n) K)
      fun _ _ hab => Units.ext hab
  haveI : IsMulCommutative A := IsMulCommutative.of_comm fun x y => Subtype.ext (hAc x x.2 y y.2)
  rcases A.bot_or_exists_ne_one with hA | ⟨t₀, ht₀A, ht₀1⟩
  · exact hA
  exfalso
  obtain ⟨t, ⟨htA, ht1⟩, hmax⟩ := Set.exists_max_image {x : GL (Fin n) K | x ∈ A ∧ x ≠ 1}
    (fun x => Nat.card (D ⊓ Subgroup.centralizer {x} : Subgroup (GL (Fin n) K)))
    (Set.toFinite _) ⟨t₀, ht₀A, ht₀1⟩
  set E : Subgroup (GL (Fin n) K) := D ⊓ Subgroup.centralizer {t} with hE
  have hmemE : ∀ {e}, e ∈ E ↔ e ∈ D ∧ e * t = t * e := fun {e} => by
    rw [hE, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have hDc : ∀ d ∈ D, ∀ d' ∈ D, d * d' = d' * d := fun d hd d' hd' =>
    Units.ext (by
      rw [Units.val_mul, Units.val_mul]
      exact isDiag_commute (hD.diag d hd) (hD.diag d' hd'))
  have hC : ∀ x ∈ A, (∀ e ∈ E, x * e = e * x) → ∀ w ∈ D, w ∉ E → x * w = w * x → x = 1 := by
    intro x hxA hxE w hwD hwE hxw
    by_contra hx1
    have hle : E ≤ D ⊓ Subgroup.centralizer {x} := fun e he =>
      Subgroup.mem_inf.2 ⟨(hmemE.1 he).1, Subgroup.mem_centralizer_singleton_iff.2 (hxE e he).symm⟩
    have heq := Subgroup.eq_of_le_of_card_ge hle (hmax x ⟨hxA, hx1⟩)
    have hw : w ∈ D ⊓ Subgroup.centralizer {x} :=
      Subgroup.mem_inf.2 ⟨hwD, Subgroup.mem_centralizer_singleton_iff.2 hxw.symm⟩
    rw [← heq] at hw
    exact hwE hw
  by_cases hcyc : ∃ d₀ ∈ D, ∀ d ∈ D, ∃ a : ℕ, ∃ e ∈ E, d = d₀ ^ a * e
  ·
    obtain ⟨d₀, hd₀, hdec⟩ := hcyc
    exact ht1 (eq_one_of_block h hq hD inf_le_left hd₀ hdec (fun e he => (hmemE.1 he).2.symm)
      (hAc t htA _ (hAD d₀ hd₀ t htA)) (hAU t htA) (hA3 t htA) (pow_orderOf_eq_one t))
  push Not at hcyc
  obtain ⟨u, huD, hu⟩ := hcyc 1 D.one_mem
  obtain ⟨v, hvD, hv⟩ := hcyc u huD
  have hu3 : u ^ 3 = 1 := hD.cube u huD
  have huv : u * v = v * u := hDc u huD v hvD
  have huE : u ∉ E := fun h1 => hu 0 u h1 (by rw [pow_zero, one_mul])
  have hvE : v ∉ E := fun h1 => hv 0 v h1 (by rw [pow_zero, one_mul])
  have hvuE : v * u ∉ E := fun h1 => hv 2 (v * u) h1 (by
    rw [← huv, ← mul_assoc, show u ^ 2 * u = 1 by rw [← pow_succ]; exact hu3, one_mul])
  have hvu2E : v * u ^ 2 ∉ E := fun h1 => hv 1 (v * u ^ 2) h1 (by
    rw [pow_one, ← mul_assoc, huv, mul_assoc, show u * u ^ 2 = 1 by rw [← pow_succ']; exact hu3,
      mul_one])
  have hN : ∀ w (hw : w ∈ D), w ∉ E → triNorm (conjOn A w (hAD w hw)) ⟨t, htA⟩ = 1 := by
    intro w hw hwE
    have hw1 : w * w * w = 1 := by rw [← pow_three']; exact hD.cube w hw
    have hw3 : ∀ x, conjOn A w (hAD w hw) (conjOn A w (hAD w hw) (conjOn A w (hAD w hw) x)) =
        x := fun x => Subtype.ext (by
      simp only [conjOn_apply]
      calc w * (w * (w * (x : GL (Fin n) K) * w⁻¹) * w⁻¹) * w⁻¹ =
            w * w * w * x * (w * w * w)⁻¹ := by group
        _ = x := by rw [hw1, one_mul, inv_one, mul_one])
    have hP1 : ∀ e ∈ E, Commute ((⟨t, htA⟩ : A) : GL (Fin n) K) e := fun e he =>
      (hmemE.1 he).2.symm
    have hPc : ∀ x : A, (∀ e ∈ E, Commute (x : GL (Fin n) K) e) →
        ∀ e ∈ E, Commute ((conjOn A w (hAD w hw) x : A) : GL (Fin n) K) e := by
      intro x hx e he
      have hwe : Commute w e := hDc w hw e (hmemE.1 he).1
      rw [conjOn_apply]
      exact ((hwe.mul_left (hx e he)).mul_left hwe.inv_left)
    have hPm : ∀ x y : A, (∀ e ∈ E, Commute (x : GL (Fin n) K) e) →
        (∀ e ∈ E, Commute (y : GL (Fin n) K) e) → ∀ e ∈ E, Commute ((x * y : A) : GL (Fin n) K) e :=
      fun x y hx hy e he => (hx e he).mul_left (hy e he)
    set y := triNorm (conjOn A w (hAD w hw)) ⟨t, htA⟩ with hy
    have hyE : ∀ e ∈ E, Commute (y : GL (Fin n) K) e :=
      hPm _ _ (hPm _ _ hP1 (hPc _ hP1)) (hPc _ (hPc _ hP1))
    have hfix := triNorm_fixed (conjOn A w (hAD w hw)) hw3 ⟨t, htA⟩
    rw [← hy] at hfix
    have hfix' : w * (y : GL (Fin n) K) * w⁻¹ = y := by
      rw [← conjOn_apply A w (hAD w hw), hfix]
    have hyw : (y : GL (Fin n) K) * w = w * y := (mul_inv_eq_iff_eq_mul.1 hfix').symm
    exact Subtype.ext (hC y y.2 (fun e he => hyE e he) w hw hwE hyw)
  have hid := norm_identity (conjOn A v (hAD v hvD)) (conjOn A u (hAD u huD))
    (conjOn A (v * u) (hAD _ (D.mul_mem hvD huD)))
    (conjOn A (v * u ^ 2) (hAD _ (D.mul_mem hvD (D.pow_mem huD 2))))
    (fun x => Subtype.ext (by
      simp only [conjOn_apply]
      calc v * (u * (x : GL (Fin n) K) * u⁻¹) * v⁻¹ = v * u * x * (v * u)⁻¹ := by group
        _ = u * v * x * (u * v)⁻¹ := by rw [huv]
        _ = u * (v * x * v⁻¹) * u⁻¹ := by group))
    (fun x => Subtype.ext (by
      simp only [conjOn_apply]
      calc u * (u * (u * (x : GL (Fin n) K) * u⁻¹) * u⁻¹) * u⁻¹ =
            u * u * u * x * (u * u * u)⁻¹ := by group
        _ = x := by rw [show u * u * u = 1 by rw [← pow_three']; exact hu3, one_mul, inv_one,
              mul_one]))
    (fun x => Subtype.ext (by simp only [conjOn_apply]; group))
    (fun x => Subtype.ext (by simp only [conjOn_apply, pow_two]; group)) ⟨t, htA⟩
  rw [hN v hvD hvE, hN u huD huE, hN (v * u) (D.mul_mem hvD huD) hvuE,
    hN (v * u ^ 2) (D.mul_mem hvD (D.pow_mem huD 2)) hvu2E, triNorm_one] at hid
  have ht3 : t ^ 3 = 1 := by
    have h1 := congrArg Subtype.val hid
    simp only [mul_one, OneMemClass.coe_one, SubgroupClass.coe_pow] at h1
    exact h1.symm
  exact ht1 (orderOf_eq_one_iff.1
    (Nat.Coprime.eq_one_of_dvd (hA3 t htA).symm (orderOf_dvd_of_pow_eq_one ht3)))

end CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

end
