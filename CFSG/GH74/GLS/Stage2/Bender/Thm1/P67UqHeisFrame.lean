module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UqBase
import CFSG.GH74.GLS.Stage2.OddAut.HeisFrameN
import CFSG.GH74.GLS.Stage2.OddAut.HeisPairR

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.GH74.GLS.Stage2.OddAut

section Gram

variable {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem uqf_rel {s g d : K} (hg : g ≠ 0) (hsgd : s * g * d = g) : s * d = 1 := by
  apply mul_right_cancel₀ hg
  linear_combination hsgd

theorem uqf_gram_eq {x B : Matrix (Fin n) (Fin n) K} (hx : (x.map h.bar)ᵀ * x = 1)
    {d : Fin n → K} (hxB : x * B = B * Matrix.diagonal d) (i j : Fin n) :
    h.bar (d i) * ((B.map h.bar)ᵀ * B) i j * d j = ((B.map h.bar)ᵀ * B) i j := by
  have h1 := CFSG.ClassicalGroups.UnitaryFlag.conjTranspose_mul_mul h 1 x B
  have h2 := CFSG.ClassicalGroups.UnitaryFlag.conjTranspose_mul_mul h 1 B (Matrix.diagonal d)
  simp only [Matrix.mul_one] at h1 h2
  rw [hx, Matrix.mul_one, hxB] at h1
  have h3 := h2.symm.trans h1
  have hdm : ((Matrix.diagonal d).map h.bar)ᵀ = Matrix.diagonal (fun m => h.bar (d m)) := by
    rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose]
  rw [hdm] at h3
  have h4 := congrFun (congrFun h3 i) j
  rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at h4

theorem uqf_gram_row (B : GL (Fin n) K) (i : Fin n) :
    ∃ j, (((B : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      (B : Matrix (Fin n) (Fin n) K)) i j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hdet := Matrix.det_eq_zero_of_row_eq_zero i hcon
  rw [Matrix.det_mul, Matrix.det_transpose] at hdet
  have hB : (B : Matrix (Fin n) (Fin n) K).det ≠ 0 := GeneralLinearGroup.det_ne_zero B
  have e : ((B : Matrix (Fin n) (Fin n) K).map h.bar).det =
      h.bar (B : Matrix (Fin n) (Fin n) K).det := (RingHom.map_det h.bar _).symm
  rw [e] at hdet
  exact mul_ne_zero ((map_ne_zero h.bar).mpr hB) hB hdet

theorem uqf_gram_herm (B : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    h.bar (((B.map h.bar)ᵀ * B) i j) = ((B.map h.bar)ᵀ * B) j i := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    h.bar_bar]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem uqf_exists_scale (G : Matrix (Fin n) (Fin n) K) (hdiag : ∀ i j, i ≠ j → G i j = 0)
    (hrow : ∀ i, ∃ j, G i j ≠ 0) (hherm : ∀ i, h.bar (G i i) = G i i) :
    ∃ c : Fin n → K, (∀ i, c i ≠ 0) ∧
      ∀ i j, h.bar (c i) * G i j * c j = (1 : Matrix (Fin n) (Fin n) K) i j := by
  have hGii : ∀ i, G i i ≠ 0 := by
    intro i
    obtain ⟨j, hj⟩ := hrow i
    rcases eq_or_ne i j with hij | hij
    · subst hij; exact hj
    · exact absurd (hdiag i j hij) hj
  have hex : ∀ i, ∃ c : K, h.bar c * c = (G i i)⁻¹ := by
    intro i
    have : Fact p.Prime := ⟨h.prime⟩
    have := h.charP
    have := h.finite
    have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, pow_mul']
    have hfix : CFSG.LieType.BorelTits.unitaryInvolution K p f (G i i)⁻¹ = (G i i)⁻¹ := by
      rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← h.bar_apply, map_inv₀, hherm]
    obtain ⟨c, hc⟩ := CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hK hfix
      (inv_ne_zero (hGii i))
    refine ⟨c, ?_⟩
    rw [h.bar_apply, ← CFSG.LieType.BorelTits.unitaryInvolution_apply K p f c]
    exact hc
  choose c hc using hex
  refine ⟨c, fun i hci => ?_, fun i j => ?_⟩
  · have := hc i
    rw [hci, map_zero, zero_mul] at this
    exact inv_ne_zero (hGii i) this.symm
  · rcases eq_or_ne i j with hij | hij
    · subst hij
      rw [Matrix.one_apply_eq, mul_right_comm, hc i, inv_mul_cancel₀ (hGii i)]
    · rw [Matrix.one_apply_ne hij, hdiag i j hij, mul_zero, zero_mul]

theorem uqf_eig_scale {x B : Matrix (Fin n) (Fin n) K} {d : Fin n → K} (c : Fin n → K)
    (hxB : x * B = B * Matrix.diagonal d) :
    x * (B * Matrix.diagonal c) = (B * Matrix.diagonal c) * Matrix.diagonal d := by
  have hcomm : Matrix.diagonal d * Matrix.diagonal c = Matrix.diagonal c * Matrix.diagonal d := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun i => mul_comm _ _)
  rw [← Matrix.mul_assoc, hxB, Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc]

theorem uq_orthonormal_distinct {x B : GL (Fin n) K} (hx : x ∈ UqU h n) {m : Fin n → K}
    (hmi : Function.Injective m) (hmn : ∀ i, h.bar (m i) * m i = 1)
    (hB : (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * Matrix.diagonal m) :
    ∃ E : UqU h n, (x : Matrix (Fin n) (Fin n) K) *
        ((E : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((E : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Matrix.diagonal m := by
  have hxu : ((x : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (x : Matrix (Fin n) (Fin n) K) = 1 := by
    have := mem_primeFormUnitary.mp hx
    rwa [Units.val_one, Matrix.mul_one] at this
  have hrow := uqf_gram_row h B
  have hoff : ∀ i j, i ≠ j →
      (((B : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (B : Matrix (Fin n) (Fin n) K)) i j = 0 := by
    intro i j hij
    by_contra hne
    have h1 := uqf_rel hne (uqf_gram_eq h hxu hB i j)
    have hmi0 : h.bar (m i) ≠ 0 := by
      intro h0
      have := hmn i
      rw [h0, zero_mul] at this
      exact zero_ne_one this
    have : m j = m i := mul_left_cancel₀ hmi0 (h1.trans (hmn i).symm)
    exact hij (hmi this).symm
  obtain ⟨c, hc0, hc⟩ := uqf_exists_scale h _ hoff hrow fun i => uqf_gram_herm h _ i i
  have hEdet : ((B : Matrix (Fin n) (Fin n) K) * Matrix.diagonal c).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (GeneralLinearGroup.det_ne_zero B)
      (Finset.prod_ne_zero_iff.mpr fun i _ => hc0 i)
  have hE : ((GeneralLinearGroup.mkOfDetNeZero _ hEdet : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * Matrix.diagonal c := rfl
  refine ⟨⟨GeneralLinearGroup.mkOfDetNeZero _ hEdet, ?_⟩, ?_⟩
  · rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one, hE]
    have h1 := CFSG.ClassicalGroups.UnitaryFlag.conjTranspose_mul_mul h 1
      (B : Matrix (Fin n) (Fin n) K) (Matrix.diagonal c)
    simp only [Matrix.mul_one] at h1
    rw [h1]
    ext i j
    have hdm : ((Matrix.diagonal c).map h.bar)ᵀ = Matrix.diagonal (fun m => h.bar (c m)) := by
      rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose]
    rw [hdm, Matrix.mul_diagonal, Matrix.diagonal_mul]
    exact hc i j
  · show (x : Matrix (Fin n) (Fin n) K) *
      ((GeneralLinearGroup.mkOfDetNeZero _ hEdet : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = _
    rw [hE]
    exact uqf_eig_scale c hB

end Gram

section Pair

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem uq_exists_pow_pair {r : ℕ} (hr : r.Prime) (hr2 : Odd r) (a b : GL (Fin n) K)
    (ua ub u : Kˣ)
    (ha : a ^ r = GeneralLinearGroup.scalar (Fin n) ua)
    (hb : b ^ r = GeneralLinearGroup.scalar (Fin n) ub)
    (hab : a * b = GeneralLinearGroup.scalar (Fin n) u * (b * a)) (hu : u ≠ 1) (hur : u ^ r = 1) :
    ∃ (i j : ℕ) (γ : Kˣ) (y : GL (Fin n) K) (ξ : Kˣ),
      (GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a ^ i * b ^ j)) ^ r = 1 ∧
      (GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a ^ i * b ^ j)) * y =
        GeneralLinearGroup.scalar (Fin n) ξ *
          (y * (GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a ^ i * b ^ j))) ∧
      ξ ≠ 1 ∧ (i ≠ 0 ∨ j ≠ 0) ∧ (y = a ∨ y = b) := by
  have hcent : ∀ (w : Kˣ) (g : GL (Fin n) K), Commute g (GeneralLinearGroup.scalar (Fin n) w) :=
    fun w g => (scalar_commute_n w g).symm
  obtain ⟨i, j, γ, hi, hj, hij, hγ⟩ := exists_exponents_pow hr ua ub
  have hcube : (a ^ i * b ^ j) ^ r = GeneralLinearGroup.scalar (Fin n) (γ ^ r) := by
    have hc : ∀ g : GL (Fin n) K, Commute g (GeneralLinearGroup.scalar (Fin n) u ^ (i * j)) :=
      fun g => (hcent u g).pow_right _
    have hxy := pow_mul_pow_comm_central (fun g => hcent u g) hab i j
    have hc3 : (GeneralLinearGroup.scalar (Fin n) u ^ (i * j)) ^ r = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ← map_pow, hur, map_one, one_pow]
    rw [pow_odd_mul_central hc hxy hr2 hc3, ← pow_mul, ← pow_mul, mul_comm i r, mul_comm j r,
      pow_mul, pow_mul, ha, hb, ← map_pow, ← map_pow, ← map_mul, ← hγ]
  have hcubex : (GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a ^ i * b ^ j)) ^ r = 1 := by
    rw [(scalar_commute_n γ⁻¹ _).mul_pow, hcube, ← map_pow, ← map_mul, inv_pow, inv_mul_cancel,
      map_one]
  have hmv : ∀ (w : Kˣ) (g h : GL (Fin n) K),
      g * (GeneralLinearGroup.scalar (Fin n) w * h) =
        GeneralLinearGroup.scalar (Fin n) w * (g * h) :=
    fun w g h => by rw [← mul_assoc, (scalar_commute_n w g).symm.eq, mul_assoc]
  by_cases hj0 : j = 0
  · have hi0 : i ≠ 0 := by rcases hij with h | h; exact h; exact absurd hj0 h
    subst hj0
    have h1 : a ^ i * b = GeneralLinearGroup.scalar (Fin n) u ^ i * (b * a ^ i) := by
      have := pow_mul_pow_comm_central (fun g => hcent u g) hab i 1
      simpa using this
    refine ⟨i, 0, γ, b, u ^ i, hcubex, ?_, pow_ne_one_of_lt_prime hr hu hur hi hi0, Or.inl hi0,
      Or.inr rfl⟩
    rw [pow_zero, mul_one]
    have e : GeneralLinearGroup.scalar (Fin n) γ⁻¹ * GeneralLinearGroup.scalar (Fin n) u ^ i =
        GeneralLinearGroup.scalar (Fin n) (u ^ i) * GeneralLinearGroup.scalar (Fin n) γ⁻¹ := by
      rw [← map_pow, ← map_mul, ← map_mul, mul_comm]
    calc GeneralLinearGroup.scalar (Fin n) γ⁻¹ * a ^ i * b
        = GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a ^ i * b) := mul_assoc _ _ _
      _ = GeneralLinearGroup.scalar (Fin n) γ⁻¹ *
            (GeneralLinearGroup.scalar (Fin n) u ^ i * (b * a ^ i)) := by rw [h1]
      _ = (GeneralLinearGroup.scalar (Fin n) γ⁻¹ * GeneralLinearGroup.scalar (Fin n) u ^ i) *
            (b * a ^ i) := by rw [mul_assoc]
      _ = (GeneralLinearGroup.scalar (Fin n) (u ^ i) * GeneralLinearGroup.scalar (Fin n) γ⁻¹) *
            (b * a ^ i) := by rw [e]
      _ = GeneralLinearGroup.scalar (Fin n) (u ^ i) *
            (GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (b * a ^ i)) := by rw [mul_assoc]
      _ = GeneralLinearGroup.scalar (Fin n) (u ^ i) *
            (b * (GeneralLinearGroup.scalar (Fin n) γ⁻¹ * a ^ i)) := by
          rw [← hmv γ⁻¹ b (a ^ i)]
  · have hj3 : j ≠ 0 := hj0
    have hbj : b ^ j * a = GeneralLinearGroup.scalar (Fin n) ((u ^ j)⁻¹) * (a * b ^ j) := by
      have := mul_pow_comm_central (fun g => hcent u g) hab j
      rw [this, map_inv, map_pow, inv_mul_cancel_left]
    refine ⟨i, j, γ, a, (u ^ j)⁻¹, hcubex, ?_, ?_, Or.inr hj3, Or.inl rfl⟩
    · have hai : ∀ w : GL (Fin n) K, a ^ i * (a * w) = a * (a ^ i * w) := fun w => by
        rw [← mul_assoc, ← mul_assoc, ← pow_succ, ← pow_succ']
      have e : GeneralLinearGroup.scalar (Fin n) γ⁻¹ *
          GeneralLinearGroup.scalar (Fin n) ((u ^ j)⁻¹) =
            GeneralLinearGroup.scalar (Fin n) ((u ^ j)⁻¹) *
              GeneralLinearGroup.scalar (Fin n) γ⁻¹ := by
        rw [← map_mul, ← map_mul, mul_comm]
      calc GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a ^ i * b ^ j) * a
          = GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a ^ i * (b ^ j * a)) := by
            simp only [mul_assoc]
        _ = GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a ^ i *
              (GeneralLinearGroup.scalar (Fin n) ((u ^ j)⁻¹) * (a * b ^ j))) := by rw [hbj]
        _ = GeneralLinearGroup.scalar (Fin n) γ⁻¹ *
              (GeneralLinearGroup.scalar (Fin n) ((u ^ j)⁻¹) * (a ^ i * (a * b ^ j))) := by
            rw [hmv]
        _ = (GeneralLinearGroup.scalar (Fin n) γ⁻¹ *
              GeneralLinearGroup.scalar (Fin n) ((u ^ j)⁻¹)) *
              (a ^ i * (a * b ^ j)) := by rw [mul_assoc]
        _ = (GeneralLinearGroup.scalar (Fin n) ((u ^ j)⁻¹) *
              GeneralLinearGroup.scalar (Fin n) γ⁻¹) *
              (a ^ i * (a * b ^ j)) := by rw [e]
        _ = GeneralLinearGroup.scalar (Fin n) ((u ^ j)⁻¹) *
              (GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a ^ i * (a * b ^ j))) := by rw [mul_assoc]
        _ = GeneralLinearGroup.scalar (Fin n) ((u ^ j)⁻¹) *
              (GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a * (a ^ i * b ^ j))) := by rw [hai]
        _ = GeneralLinearGroup.scalar (Fin n) ((u ^ j)⁻¹) *
              (a * (GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a ^ i * b ^ j))) := by
            rw [← hmv γ⁻¹ a (a ^ i * b ^ j)]
    · exact inv_ne_one.mpr (pow_ne_one_of_lt_prime hr hu hur hj hj3)

end Pair

section Norm

variable {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem uq_norm_of_pow_eq_one {r : ℕ} (hrq : r ∣ p ^ f + 1) {z : K} (hz : z ^ r = 1) :
    h.bar z * z = 1 := by
  obtain ⟨k, hk⟩ := hrq
  rw [h.bar_apply, ← pow_succ, hk, pow_mul, hz, one_pow]

theorem uq_norm_of_pow (hn : 0 < n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {w : GL (Fin n) K}
    (hw : w ∈ UqU h n) {γ : Kˣ} (hγ : w ^ r = GeneralLinearGroup.scalar (Fin n) (γ ^ r))
    (hrq : r ∣ p ^ f + 1) : h.bar (γ : K) * γ = 1 := by
  have hm : (GeneralLinearGroup.scalar (Fin n) (γ ^ r) : GL (Fin n) K) ∈ UqU h n := by
    rw [← hγ]; exact pow_mem hw r
  have h1 := (uq_scalar_mem_iff h hn (γ ^ r)).1 hm
  set g : K := h.bar (γ : K) * γ with hg
  have hg0 : g ≠ 0 := mul_ne_zero ((map_ne_zero h.bar).mpr γ.ne_zero) γ.ne_zero
  have hgr : g ^ r = 1 := by
    rw [hg, mul_pow, ← map_pow]
    simpa using h1
  have hbg : h.bar g = g := by
    rw [hg, map_mul, h.bar_bar, mul_comm]
  have hgq : g ^ (p ^ f) = g := by rw [← h.bar_apply]; exact hbg
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hgq1 : g ^ (p ^ f - 1) = 1 := by
    have : g ^ (p ^ f - 1) * g = g := by
      rw [← pow_succ, Nat.sub_add_cancel hq1, hgq]
    exact mul_right_cancel₀ hg0 (by rw [this, one_mul])
  have hcop : Nat.Coprime r (p ^ f - 1) := by
    refine (Nat.Prime.coprime_iff_not_dvd hr).2 fun hd => ?_
    have h2 : r ∣ 2 := (Nat.dvd_add_right hd).1 (by rwa [show p ^ f - 1 + 2 = p ^ f + 1 by omega])
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
  have := (pow_gcd_eq_one (a := g)).2 ⟨hgr, hgq1⟩
  rwa [hcop, pow_one] at this

end Norm

section Eigen

variable {K : Type} [Field K] {n : ℕ}

theorem uqf_eig_pow_one {x B : Matrix (Fin n) (Fin n) K} (hB : IsUnit B) {d : Fin n → K} {r : ℕ}
    (hx : x * B = B * Matrix.diagonal d) (hxr : x ^ r = 1) (i : Fin n) : d i ^ r = 1 := by
  have h1 := mul_pow_diag_n hx r
  rw [hxr, Matrix.one_mul] at h1
  have h2 : Matrix.diagonal (d ^ r) = 1 := by
    apply hB.mul_right_inj.mp
    rw [Matrix.mul_one]
    exact h1.symm
  have := congrFun (congrFun h2 i) i
  simpa using this

end Eigen

section Frame

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem uq_heis_frame {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ p ^ f + 1)
    {V : Subgroup (MulAut (UqT h r))} (hVe : ∀ v ∈ V, v ^ r = 1) (a b : UqU h r)
    (u : Kˣ) (hu : u ≠ 1)
    (ha : primeFormConjHom h ((1 : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) a ∈ V)
    (hb : primeFormConjHom h ((1 : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) b ∈ V)
    (hab : (a : GL (Fin r) K) * b =
      GeneralLinearGroup.scalar (Fin r) u * ((b : GL (Fin r) K) * a)) :
    ∃ (E x y : UqU h r) (ξ m0 : K),
      primeFormConjHom h ((1 : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) x ∈ V ∧
      primeFormConjHom h ((1 : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) y ∈ V ∧
      ξ ^ r = 1 ∧ ξ ≠ 1 ∧ h.bar ξ * ξ = 1 ∧ m0 ≠ 0 ∧ h.bar m0 * m0 = 1 ∧
      ((x : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *
        ((E : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) =
        ((E : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *
          Matrix.diagonal (fun i : Fin r => ξ ^ (i : ℕ) * m0) ∧
      ((x : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *
        ((y : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) =
        ξ • (((y : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *
          ((x : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)) := by
  classical
  have : Finite K := h.finite
  have hr0 : 0 < r := hr.pos
  have hr1 : 1 < r := hr.one_lt
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  set c := primeFormConjHom h ((1 : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)
  obtain ⟨ua, hua⟩ := (uq_conj_eq_one_iff h hr3 (a ^ r)).1 (by rw [map_pow]; exact hVe _ ha)
  obtain ⟨ub, hub⟩ := (uq_conj_eq_one_iff h hr3 (b ^ r)).1 (by rw [map_pow]; exact hVe _ hb)
  have hua' : (a : GL (Fin r) K) ^ r = GeneralLinearGroup.scalar (Fin r) ua := by
    simpa using hua
  have hub' : (b : GL (Fin r) K) ^ r = GeneralLinearGroup.scalar (Fin r) ub := by
    simpa using hub
  have hur : u ^ r = 1 := comm_scalar_pow_n_dim hab
  obtain ⟨i, j, γ, y, ξ, hxr, hxy, hξ1, -, hy⟩ :=
    uq_exists_pow_pair hr hrodd (a : GL (Fin r) K) (b : GL (Fin r) K) ua ub u hua' hub' hab hu hur
  have hwr : ((a : GL (Fin r) K) ^ i * (b : GL (Fin r) K) ^ j) ^ r =
      GeneralLinearGroup.scalar (Fin r) (γ ^ r) := by
    have h1 := hxr
    rw [(scalar_commute_n γ⁻¹ _).mul_pow, ← map_pow] at h1
    have h2 := eq_inv_of_mul_eq_one_right h1
    rw [h2, ← map_inv, inv_pow, inv_inv]
  have hwU : (a : GL (Fin r) K) ^ i * (b : GL (Fin r) K) ^ j ∈ UqU h r :=
    mul_mem (pow_mem a.2 i) (pow_mem b.2 j)
  have hγN : h.bar (γ : K) * γ = 1 := uq_norm_of_pow h hr0 hr hr2 hwU hwr hrq
  have hγ'N : h.bar ((γ⁻¹ : Kˣ) : K) * ((γ⁻¹ : Kˣ) : K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hγN, inv_one]
  have hsγ : (GeneralLinearGroup.scalar (Fin r) γ⁻¹ : GL (Fin r) K) ∈ UqU h r :=
    (uq_scalar_mem_iff h hr0 γ⁻¹).2 hγ'N
  set sγ : UqU h r := ⟨_, hsγ⟩
  set w : UqU h r := a ^ i * b ^ j with hwdef
  set x : UqU h r := sγ * w with hxdef
  have hxcoe : (x : GL (Fin r) K) = GeneralLinearGroup.scalar (Fin r) γ⁻¹ *
      ((a : GL (Fin r) K) ^ i * (b : GL (Fin r) K) ^ j) := rfl
  have hcsγ : c sγ = 1 := (uq_conj_eq_one_iff h hr3 sγ).2 ⟨γ⁻¹, rfl⟩
  have hcx : c x ∈ V := by
    rw [hxdef, map_mul, hcsγ, one_mul, hwdef, map_mul, map_pow, map_pow]
    exact V.mul_mem (V.pow_mem ha i) (V.pow_mem hb j)
  have hyU : y ∈ UqU h r := by
    rcases hy with h' | h'
    · rw [h']; exact a.2
    · rw [h']; exact b.2
  set y' : UqU h r := ⟨y, hyU⟩
  have hcy : c y' ∈ V := by
    have : y' = a ∨ y' = b := by
      rcases hy with h' | h'
      · exact Or.inl (Subtype.ext h')
      · exact Or.inr (Subtype.ext h')
    rcases this with h' | h'
    · rw [h']; exact ha
    · rw [h']; exact hb
  have hxy' : (x : GL (Fin r) K) * (y' : GL (Fin r) K) =
      GeneralLinearGroup.scalar (Fin r) ξ * ((y' : GL (Fin r) K) * (x : GL (Fin r) K)) := hxy
  have hξr : ξ ^ r = 1 := comm_scalar_pow_n_dim hxy'
  have hξ1' : (ξ : K) ≠ 1 := fun h1 => hξ1 (Units.ext h1)
  have hξr' : (ξ : K) ^ r = 1 := by rw [← Units.val_pow_eq_pow_val, hξr, Units.val_one]
  have hξN : h.bar (ξ : K) * ξ = 1 := uq_norm_of_pow_eq_one h hrq hξr'
  have hxrx : (x : GL (Fin r) K) ^ r = 1 := by rw [hxcoe]; exact hxr
  have hxr' : ((x : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) ^ r = 1 := by
    rw [← Units.val_pow_eq_pow_val, hxrx, Units.val_one]
  have hxym : ((x : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *
      ((y' : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = (ξ : K) •
      (((y' : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *
        ((x : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)) := by
    have := congrArg (fun g : GL (Fin r) K => (g : Matrix (Fin r) (Fin r) K)) hxy'
    simp only [Units.val_mul, coe_scalar_smul_n, Matrix.smul_mul, Matrix.one_mul] at this
    exact this
  have hξord : orderOf (ξ : K) = r := by
    have : Fact r.Prime := ⟨hr⟩
    exact orderOf_eq_prime hξr' hξ1'
  have hξprim : IsPrimitiveRoot (ξ : K) r := IsPrimitiveRoot.iff_orderOf.mpr hξord
  obtain ⟨B, lam, hBu, hlam0, hB⟩ := heis_frame_r hr1 (ξ : K) hξprim
    ((x : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)
    ((y' : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) hxr' (y' : GL (Fin r) K).isUnit hxym
  set Bg : GL (Fin r) K := hBu.unit
  have hBg' : ((x : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) * (Bg : Matrix (Fin r) (Fin r) K) =
      (Bg : Matrix (Fin r) (Fin r) K) *
        Matrix.diagonal (fun i : Fin r => (ξ : K) ^ (i : ℕ) * lam) :=
    hB
  have hlamr : lam ^ r = 1 := by
    have := uqf_eig_pow_one hBu hB hxr' ⟨0, hr0⟩
    simpa using this
  have hmn : ∀ i : Fin r, h.bar ((ξ : K) ^ (i : ℕ) * lam) * ((ξ : K) ^ (i : ℕ) * lam) = 1 := by
    intro i
    apply uq_norm_of_pow_eq_one h hrq
    rw [mul_pow, ← pow_mul, mul_comm (i : ℕ) r, pow_mul, hξr', one_pow, one_mul, hlamr]
  have hmi : Function.Injective (fun i : Fin r => (ξ : K) ^ (i : ℕ) * lam) := by
    intro i j hij
    have h1 : (ξ : K) ^ (i : ℕ) = (ξ : K) ^ (j : ℕ) := mul_right_cancel₀ hlam0 hij
    exact Fin.ext (hξprim.pow_inj i.2 j.2 h1)
  obtain ⟨E, hE⟩ := uq_orthonormal_distinct h x.2 hmi hmn hBg'
  exact ⟨E, x, y', (ξ : K), lam, hcx, hcy, hξr', hξ1', hξN, hlam0,
    uq_norm_of_pow_eq_one h hrq hlamr, hE, hxym⟩

end Frame

theorem uq5_heis_frame {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (h5 : 5 ∣ p ^ f + 1) {V : Subgroup (MulAut (UqT h 5))} (hVe : ∀ v ∈ V, v ^ 5 = 1)
    (a b : UqU h 5) (u : Kˣ) (hu : u ≠ 1)
    (ha : primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) a ∈ V)
    (hb : primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) b ∈ V)
    (hab : (a : GL (Fin 5) K) * b =
      GeneralLinearGroup.scalar (Fin 5) u * ((b : GL (Fin 5) K) * a)) :
    ∃ (E x y : UqU h 5) (ξ m0 : K),
      primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) x ∈ V ∧
      primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) y ∈ V ∧
      ξ ^ 5 = 1 ∧ ξ ≠ 1 ∧ h.bar ξ * ξ = 1 ∧ m0 ≠ 0 ∧ h.bar m0 * m0 = 1 ∧
      ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
        ((E : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        ((E : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
          Matrix.diagonal (fun i : Fin 5 => ξ ^ (i : ℕ) * m0) ∧
      ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
        ((y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        ξ • (((y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
          ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) :=
  uq_heis_frame h Nat.prime_five (by norm_num) h5 hVe a b u hu ha hb hab

end CFSG.GH74.GLS.Stage2.Bender.Thm1
