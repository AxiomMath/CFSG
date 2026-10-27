module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Frame
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Base
public import CFSG.GH74.GLS.Stage2.OddAut.HeisPair
public import CFSG.GH74.GLS.Stage2.OddAut.HeisFrame

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.GH74.GLS.Stage2.OddAut

section Distinct

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem u3_orthonormal_distinct {x B : GL (Fin 3) K} (hx : x ∈ U3U h) {m : Fin 3 → K}
    (hmi : Function.Injective m) (hmn : ∀ i, h.bar (m i) * m i = 1)
    (hB : (x : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) =
      (B : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal m) :
    ∃ E : U3U h, (x : Matrix (Fin 3) (Fin 3) K) * ((E : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((E : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal m := by
  have hxu : ((x : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (x : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have := mem_primeFormUnitary.mp hx
    rwa [Units.val_one, Matrix.mul_one] at this
  have hrow := u3f_gram_row h B
  have hoff : ∀ i j, i ≠ j →
      (((B : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (B : Matrix (Fin 3) (Fin 3) K)) i j = 0 := by
    intro i j hij
    by_contra hne
    have h1 := u3f_rel hne (u3f_gram_eq h hxu hB i j)
    have hmi0 : h.bar (m i) ≠ 0 := by
      intro h0
      have := hmn i
      rw [h0, zero_mul] at this
      exact zero_ne_one this
    have : m j = m i := mul_left_cancel₀ hmi0 (h1.trans (hmn i).symm)
    exact hij (hmi this).symm
  obtain ⟨c, hc0, hc⟩ := u3f_exists_scale h _ hoff hrow fun i => u3f_gram_herm h _ i i
  have hEdet : ((B : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal c).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (GeneralLinearGroup.det_ne_zero B)
      (Finset.prod_ne_zero_iff.mpr fun i _ => hc0 i)
  have hE : ((GeneralLinearGroup.mkOfDetNeZero _ hEdet : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = (B : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal c := rfl
  refine ⟨⟨GeneralLinearGroup.mkOfDetNeZero _ hEdet, ?_⟩, ?_⟩
  · rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one, hE]
    have h1 := CFSG.ClassicalGroups.UnitaryFlag.conjTranspose_mul_mul h 1
      (B : Matrix (Fin 3) (Fin 3) K) (Matrix.diagonal c)
    simp only [Matrix.mul_one] at h1
    rw [h1]
    ext i j
    have hdm : ((Matrix.diagonal c).map h.bar)ᵀ = Matrix.diagonal (fun m => h.bar (c m)) := by
      rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose]
    rw [hdm, Matrix.mul_diagonal, Matrix.diagonal_mul]
    exact hc i j
  · show (x : Matrix (Fin 3) (Fin 3) K) *
      ((GeneralLinearGroup.mkOfDetNeZero _ hEdet : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [hE]
    exact u3f_eig_scale c hB

end Distinct

section Pair

variable {K : Type} [Field K] [Finite K]

theorem u3_exists_cube_pair (a b : GL (Fin 3) K) (ua ub u : Kˣ)
    (ha : a ^ 3 = GeneralLinearGroup.scalar (Fin 3) ua)
    (hb : b ^ 3 = GeneralLinearGroup.scalar (Fin 3) ub)
    (hab : a * b = GeneralLinearGroup.scalar (Fin 3) u * (b * a)) (hu : u ≠ 1) :
    ∃ (i j : ℕ) (γ : Kˣ) (y : GL (Fin 3) K) (ξ : Kˣ),
      (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a ^ i * b ^ j)) ^ 3 = 1 ∧
      (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a ^ i * b ^ j)) * y =
        GeneralLinearGroup.scalar (Fin 3) ξ *
          (y * (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a ^ i * b ^ j))) ∧
      ξ ≠ 1 ∧ (i ≠ 0 ∨ j ≠ 0) ∧ (y = a ∨ y = b) := by
  have hu3 := comm_scalar_cube hab
  have hcent : ∀ (w : Kˣ) (g : GL (Fin 3) K), Commute g (GeneralLinearGroup.scalar (Fin 3) w) :=
    fun w g => (scalar_commute w g).symm
  obtain ⟨i, j, γ, hi, hj, hij, hγ⟩ := exists_exponents_pow Nat.prime_three ua ub
  have hcube : (a ^ i * b ^ j) ^ 3 = GeneralLinearGroup.scalar (Fin 3) (γ ^ 3) := by
    have hc : ∀ g : GL (Fin 3) K, Commute g (GeneralLinearGroup.scalar (Fin 3) u ^ (i * j)) :=
      fun g => (hcent u g).pow_right _
    have hxy := pow_mul_pow_comm_central (fun g => hcent u g) hab i j
    have hc3 : (GeneralLinearGroup.scalar (Fin 3) u ^ (i * j)) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ← map_pow, hu3, map_one, one_pow]
    rw [cube_mul_central hc hxy hc3, ← pow_mul, ← pow_mul, mul_comm i 3, mul_comm j 3, pow_mul,
      pow_mul, ha, hb, ← map_pow, ← map_pow, ← map_mul, ← hγ]
  have hcubex : (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a ^ i * b ^ j)) ^ 3 = 1 := by
    rw [(scalar_commute γ⁻¹ _).mul_pow, hcube, ← map_pow, ← map_mul, inv_pow, inv_mul_cancel,
      map_one]
  have hmv : ∀ (w : Kˣ) (g h : GL (Fin 3) K),
      g * (GeneralLinearGroup.scalar (Fin 3) w * h) =
        GeneralLinearGroup.scalar (Fin 3) w * (g * h) :=
    fun w g h => by rw [← mul_assoc, (scalar_commute w g).symm.eq, mul_assoc]
  by_cases hj0 : j = 0
  · have hi0 : i ≠ 0 := by rcases hij with h | h; exact h; exact absurd hj0 h
    subst hj0
    have h1 : a ^ i * b = GeneralLinearGroup.scalar (Fin 3) u ^ i * (b * a ^ i) := by
      have := pow_mul_pow_comm_central (fun g => hcent u g) hab i 1
      simpa using this
    refine ⟨i, 0, γ, b, u ^ i, hcubex, ?_, ne_one_of_pow_three hu hu3 hi hi0, Or.inl hi0,
      Or.inr rfl⟩
    rw [pow_zero, mul_one]
    have e : GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * GeneralLinearGroup.scalar (Fin 3) u ^ i =
        GeneralLinearGroup.scalar (Fin 3) (u ^ i) * GeneralLinearGroup.scalar (Fin 3) γ⁻¹ := by
      rw [← map_pow, ← map_mul, ← map_mul, mul_comm]
    calc GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * a ^ i * b
        = GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a ^ i * b) := mul_assoc _ _ _
      _ = GeneralLinearGroup.scalar (Fin 3) γ⁻¹ *
            (GeneralLinearGroup.scalar (Fin 3) u ^ i * (b * a ^ i)) := by rw [h1]
      _ = (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * GeneralLinearGroup.scalar (Fin 3) u ^ i) *
            (b * a ^ i) := by rw [mul_assoc]
      _ = (GeneralLinearGroup.scalar (Fin 3) (u ^ i) * GeneralLinearGroup.scalar (Fin 3) γ⁻¹) *
            (b * a ^ i) := by rw [e]
      _ = GeneralLinearGroup.scalar (Fin 3) (u ^ i) *
            (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (b * a ^ i)) := by rw [mul_assoc]
      _ = GeneralLinearGroup.scalar (Fin 3) (u ^ i) *
            (b * (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * a ^ i)) := by
          rw [← hmv γ⁻¹ b (a ^ i)]
  · have hj3 : j ≠ 0 := hj0
    have hbj : b ^ j * a = GeneralLinearGroup.scalar (Fin 3) ((u ^ j)⁻¹) * (a * b ^ j) := by
      have := mul_pow_comm_central (fun g => hcent u g) hab j
      rw [this, map_inv, map_pow, inv_mul_cancel_left]
    refine ⟨i, j, γ, a, (u ^ j)⁻¹, hcubex, ?_, ?_, Or.inr hj3, Or.inl rfl⟩
    · have hai : ∀ w : GL (Fin 3) K, a ^ i * (a * w) = a * (a ^ i * w) := fun w => by
        rw [← mul_assoc, ← mul_assoc, ← pow_succ, ← pow_succ']
      have e : GeneralLinearGroup.scalar (Fin 3) γ⁻¹ *
          GeneralLinearGroup.scalar (Fin 3) ((u ^ j)⁻¹) =
            GeneralLinearGroup.scalar (Fin 3) ((u ^ j)⁻¹) *
              GeneralLinearGroup.scalar (Fin 3) γ⁻¹ := by
        rw [← map_mul, ← map_mul, mul_comm]
      calc GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a ^ i * b ^ j) * a
          = GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a ^ i * (b ^ j * a)) := by
            simp only [mul_assoc]
        _ = GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a ^ i *
              (GeneralLinearGroup.scalar (Fin 3) ((u ^ j)⁻¹) * (a * b ^ j))) := by rw [hbj]
        _ = GeneralLinearGroup.scalar (Fin 3) γ⁻¹ *
              (GeneralLinearGroup.scalar (Fin 3) ((u ^ j)⁻¹) * (a ^ i * (a * b ^ j))) := by
            rw [hmv]
        _ = (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ *
              GeneralLinearGroup.scalar (Fin 3) ((u ^ j)⁻¹)) *
              (a ^ i * (a * b ^ j)) := by rw [mul_assoc]
        _ = (GeneralLinearGroup.scalar (Fin 3) ((u ^ j)⁻¹) *
              GeneralLinearGroup.scalar (Fin 3) γ⁻¹) *
              (a ^ i * (a * b ^ j)) := by rw [e]
        _ = GeneralLinearGroup.scalar (Fin 3) ((u ^ j)⁻¹) *
              (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a ^ i * (a * b ^ j))) := by rw [mul_assoc]
        _ = GeneralLinearGroup.scalar (Fin 3) ((u ^ j)⁻¹) *
              (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a * (a ^ i * b ^ j))) := by rw [hai]
        _ = GeneralLinearGroup.scalar (Fin 3) ((u ^ j)⁻¹) *
              (a * (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a ^ i * b ^ j))) := by
            rw [← hmv γ⁻¹ a (a ^ i * b ^ j)]
    · exact inv_ne_one.mpr (ne_one_of_pow_three hu hu3 hj hj3)

end Pair

section Scalars

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem u3_scalar_mem_iff (c : Kˣ) :
    (GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) ∈ U3U h ↔ h.bar (c : K) * c = 1 := by
  rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one, GeneralLinearGroup.coe_scalar]
  have e : ((Matrix.scalar (Fin 3) (c : K)).map h.bar)ᵀ * Matrix.scalar (Fin 3) (c : K) =
      Matrix.diagonal (fun _ : Fin 3 => h.bar (c : K) * c) := by
    simp only [Matrix.scalar_apply, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
  rw [e]
  constructor
  · intro h1
    have := congrFun (congrFun h1 0) 0
    simpa using this
  · intro h1
    rw [h1, Matrix.diagonal_one]

theorem u3_three_dvd {a b : GL (Fin 3) K} (ha : a ∈ U3U h) (hb : b ∈ U3U h) {u : Kˣ} (hu : u ≠ 1)
    (hu3 : u ^ 3 = 1)
    (hab : a * b = GeneralLinearGroup.scalar (Fin 3) u * (b * a)) : 3 ∣ p ^ f + 1 := by
  have hs : (GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) = a * b * a⁻¹ * b⁻¹ := by
    rw [hab]; group
  have hmem : (GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) ∈ U3U h := by
    rw [hs]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have h1 := (u3_scalar_mem_iff h u).1 hmem
  rw [h.bar_apply, ← pow_succ] at h1
  have h2 : u ^ (p ^ f + 1) = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h1)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one h2

theorem u3_norm_of_cube {w : GL (Fin 3) K} (hw : w ∈ U3U h) {γ : Kˣ}
    (hγ : w ^ 3 = GeneralLinearGroup.scalar (Fin 3) (γ ^ 3)) (h3 : 3 ∣ p ^ f + 1) :
    h.bar (γ : K) * γ = 1 := by
  have hm : (GeneralLinearGroup.scalar (Fin 3) (γ ^ 3) : GL (Fin 3) K) ∈ U3U h := by
    rw [← hγ]; exact pow_mem hw 3
  have h1 := (u3_scalar_mem_iff h (γ ^ 3)).1 hm
  set g : K := h.bar (γ : K) * γ with hg
  have hg0 : g ≠ 0 := mul_ne_zero ((map_ne_zero h.bar).mpr γ.ne_zero) γ.ne_zero
  have hg3 : g ^ 3 = 1 := by
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
  have hcop : Nat.Coprime 3 (p ^ f - 1) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
  have := (pow_gcd_eq_one (a := g)).2 ⟨hg3, hgq1⟩
  rwa [hcop, pow_one] at this

end Scalars

section Frame

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem u3_heis_frame {V : Subgroup (MulAut (U3T h))} (hVe : ∀ v ∈ V, v ^ 3 = 1) (a b : U3U h)
    (u : Kˣ) (hu : u ≠ 1)
    (ha : primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a ∈ V)
    (hb : primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) b ∈ V)
    (hab : (a : GL (Fin 3) K) * b =
      GeneralLinearGroup.scalar (Fin 3) u * ((b : GL (Fin 3) K) * a)) :
    ∃ (E x y : U3U h) (ξ m0 : K),
      primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) x ∈ V ∧
      primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) y ∈ V ∧
      ξ ^ 3 = 1 ∧ ξ ≠ 1 ∧ h.bar ξ * ξ = 1 ∧ m0 ≠ 0 ∧ h.bar m0 * m0 = 1 ∧
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((E : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = ((E : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          Matrix.diagonal (fun i : Fin 3 => ξ ^ (i : ℕ) * m0) ∧
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((y : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = ξ • (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  classical
  have : Finite K := h.finite
  set c := primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hc
  obtain ⟨ua, hua⟩ := (u3_conj_eq_one_iff h (a ^ 3)).1 (by rw [map_pow]; exact hVe _ ha)
  obtain ⟨ub, hub⟩ := (u3_conj_eq_one_iff h (b ^ 3)).1 (by rw [map_pow]; exact hVe _ hb)
  have hua' : (a : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) ua := by
    simpa using hua
  have hub' : (b : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) ub := by
    simpa using hub
  have hu3 : u ^ 3 = 1 := comm_scalar_cube hab
  have h3 : 3 ∣ p ^ f + 1 := u3_three_dvd h a.2 b.2 hu hu3 hab
  obtain ⟨i, j, γ, y, ξ, hx3, hxy, hξ1, -, hy⟩ :=
    u3_exists_cube_pair (a : GL (Fin 3) K) (b : GL (Fin 3) K) ua ub u hua' hub' hab hu
  have hw3 : ((a : GL (Fin 3) K) ^ i * (b : GL (Fin 3) K) ^ j) ^ 3 =
      GeneralLinearGroup.scalar (Fin 3) (γ ^ 3) := by
    have h1 := hx3
    rw [(scalar_commute γ⁻¹ _).mul_pow, ← map_pow] at h1
    have h2 := eq_inv_of_mul_eq_one_right h1
    rw [h2, ← map_inv, inv_pow, inv_inv]
  have hwU : (a : GL (Fin 3) K) ^ i * (b : GL (Fin 3) K) ^ j ∈ U3U h :=
    mul_mem (pow_mem a.2 i) (pow_mem b.2 j)
  have hγN : h.bar (γ : K) * γ = 1 := u3_norm_of_cube h hwU hw3 h3
  have hγ'N : h.bar ((γ⁻¹ : Kˣ) : K) * ((γ⁻¹ : Kˣ) : K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hγN, inv_one]
  have hsγ : (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ : GL (Fin 3) K) ∈ U3U h :=
    (u3_scalar_mem_iff h γ⁻¹).2 hγ'N
  set sγ : U3U h := ⟨_, hsγ⟩ with hsγdef
  set w : U3U h := a ^ i * b ^ j with hwdef
  set x : U3U h := sγ * w with hxdef
  have hxcoe : (x : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) γ⁻¹ *
      ((a : GL (Fin 3) K) ^ i * (b : GL (Fin 3) K) ^ j) := rfl
  have hcsγ : c sγ = 1 := (u3_conj_eq_one_iff h sγ).2 ⟨γ⁻¹, rfl⟩
  have hcx : c x ∈ V := by
    rw [hxdef, map_mul, hcsγ, one_mul, hwdef, map_mul, map_pow, map_pow]
    exact V.mul_mem (V.pow_mem ha i) (V.pow_mem hb j)
  have hyU : y ∈ U3U h := by
    rcases hy with h' | h'
    · rw [h']; exact a.2
    · rw [h']; exact b.2
  set y' : U3U h := ⟨y, hyU⟩ with hy'def
  have hcy : c y' ∈ V := by
    have : y' = a ∨ y' = b := by
      rcases hy with h' | h'
      · exact Or.inl (Subtype.ext h')
      · exact Or.inr (Subtype.ext h')
    rcases this with h' | h'
    · rw [h']; exact ha
    · rw [h']; exact hb
  have hxy' : (x : GL (Fin 3) K) * (y' : GL (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) ξ * ((y' : GL (Fin 3) K) * (x : GL (Fin 3) K)) := hxy
  have hξ3 : ξ ^ 3 = 1 := comm_scalar_cube hxy'
  have hξN : h.bar (ξ : K) * ξ = 1 := by
    have hs : (GeneralLinearGroup.scalar (Fin 3) ξ : GL (Fin 3) K) =
        (x : GL (Fin 3) K) * (y' : GL (Fin 3) K) * (x : GL (Fin 3) K)⁻¹ *
          (y' : GL (Fin 3) K)⁻¹ := by
      rw [hxy']; group
    refine (u3_scalar_mem_iff h ξ).1 ?_
    rw [hs]
    exact mul_mem (mul_mem (mul_mem x.2 y'.2) (inv_mem x.2)) (inv_mem y'.2)
  have hξ1' : (ξ : K) ≠ 1 := fun h1 => hξ1 (Units.ext h1)
  have hξ3' : (ξ : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hξ3, Units.val_one]
  have hξ0 : (ξ : K) ≠ 0 := ξ.ne_zero
  have hx3x : (x : GL (Fin 3) K) ^ 3 = 1 := by rw [hxcoe]; exact hx3
  have hx3' : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx3x, Units.val_one]
  have hxym : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((y' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (ξ : K) •
      (((y' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hxy'
    simp only [Units.val_mul, coe_scalar_smul, Matrix.smul_mul, Matrix.one_mul] at this
    exact this
  obtain ⟨B, lam, hBu, hlam0, hB⟩ := heis_frame (ξ : K) hξ1' hξ3'
    ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ((y' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    hx3' (y' : GL (Fin 3) K).isUnit hxym
  set Bg : GL (Fin 3) K := hBu.unit with hBg
  have hBgm : (Bg : Matrix (Fin 3) (Fin 3) K) = B := rfl
  have hBg' : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (Bg : Matrix (Fin 3) (Fin 3) K) =
      (Bg : Matrix (Fin 3) (Fin 3) K) *
        Matrix.diagonal (fun i : Fin 3 => (ξ : K) ^ (i : ℕ) * lam) :=
    hB
  have hlam3 : lam ^ 3 = 1 := by
    have := u3f_eig_pow (r := 3) (u := 1) hBg' (by rw [hx3x, map_one]) 0
    simpa using this
  have hcube : ∀ z : K, z ^ 3 = 1 → h.bar z * z = 1 := by
    intro z hz
    obtain ⟨k, hk⟩ := h3
    rw [h.bar_apply, ← pow_succ, hk, pow_mul, hz, one_pow]
  have hmn : ∀ i : Fin 3, h.bar ((ξ : K) ^ (i : ℕ) * lam) * ((ξ : K) ^ (i : ℕ) * lam) = 1 := by
    intro i
    apply hcube
    rw [mul_pow, ← pow_mul, mul_comm (i : ℕ) 3, pow_mul, hξ3', one_pow, one_mul, hlam3]
  have hξord : orderOf (ξ : K) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hξ3' hξ1'
  have hmi : Function.Injective (fun i : Fin 3 => (ξ : K) ^ (i : ℕ) * lam) := by
    intro i j hij
    have h1 : (ξ : K) ^ (i : ℕ) = (ξ : K) ^ (j : ℕ) := mul_right_cancel₀ hlam0 hij
    have h2 := pow_injOn_Iio_orderOf (x := (ξ : K)) (by rw [hξord]; exact i.2)
      (by rw [hξord]; exact j.2) h1
    exact Fin.ext h2
  obtain ⟨E, hE⟩ := u3_orthonormal_distinct h x.2 hmi hmn hBg'
  refine ⟨E, x, y', (ξ : K), lam, hcx, hcy, hξ3', hξ1', hξN, hlam0, ?_, hE, hxym⟩
  have := hmn 0
  simpa using this

end Frame

end CFSG.GH74.GLS.Stage2.Bender.Thm1
