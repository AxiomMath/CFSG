module

public import CFSG.HardMathSupport.Foote.SPLScalar.Field

public section

namespace CFSG.HardMathSupport.Foote.SPLScalar

open CFSG.Open

variable {K : Type} [Group K] {n : ℕ}

theorem isElemAbelian_range (ψ : Multiplicative (GaloisField 3 n) →* K) :
    IsElemAbelian 3 ψ.range := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨a, rfl⟩ := hx
    rw [← map_pow]
    have h3 : a ^ 3 = 1 := by
      have h : (3 : GaloisField 3 n) = 0 := by exact_mod_cast CharP.cast_eq_zero _ 3
      change Multiplicative.ofAdd (3 • Multiplicative.toAdd a) = Multiplicative.ofAdd 0
      rw [nsmul_eq_mul, Nat.cast_ofNat, h, zero_mul]
    rw [h3, map_one]

theorem eq_neg_one_of_sq_eq_one {F : Type*} [Field F] {x : F} (h2 : x ^ 2 = 1) (h1 : x ≠ 1) :
    x = -1 := by
  have h : (x - 1) * (x + 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) h1
  · exact eq_neg_of_add_eq_zero_left h

theorem two_mul_dvd {n e : ℕ} (he : e = 1 ∨ (e = 2 ∧ 3 ≤ n ∧ Even n)) : 2 * e ∣ 3 ^ n - 1 := by
  rcases he with rfl | ⟨rfl, -, ⟨j, rfl⟩⟩
  · have h : (3 : ℕ) ^ n % 2 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    omega
  · have h : (3 : ℕ) ^ (j + j) % 4 = 1 := by
      rw [← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    omega

theorem exists_scalar_of_torus [Finite K] {e : ℕ} (hn : 2 ≤ n)
    (he : e = 1 ∨ (e = 2 ∧ 3 ≤ n ∧ Even n)) (ψ : Multiplicative (GaloisField 3 n) →* K)
    (htor : ∀ μ : (GaloisField 3 n)ˣ, ∃ c : K, ∀ a, c * ψ a * c⁻¹ =
      ψ (Multiplicative.ofAdd ((μ : GaloisField 3 n) ^ e * Multiplicative.toAdd a))) :
    IsElemAbelian 3 ψ.range ∧ ∃ c ∈ Subgroup.normalizer (ψ.range : Set K),
      ∃ m lam : ℕ, 5 ≤ 2 * m ∧ ¬ 3 ∣ lam - 1 ∧ (∀ a ∈ ψ.range, c ^ m * a * (c ^ m)⁻¹ = a ^ lam) ∧
      ∀ k, 0 < k → k < m → ∀ F : Subgroup K, F ≤ ψ.range → F.relIndex ψ.range = 3 →
        c ^ k ∉ Subgroup.normalizer (F : Set K) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set GF := GaloisField 3 n with hGF
  have hcardGF : Nat.card GF = 3 ^ n := GaloisField.card 3 n (by omega)
  have hq9 : 9 ≤ 3 ^ n := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := GFˣ)
  have hordμ : orderOf μ = 3 ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hμ, Nat.card_units, hcardGF]
  obtain ⟨c, hc⟩ := htor μ
  have hck : ∀ k : ℕ, ∀ a, c ^ k * ψ a * (c ^ k)⁻¹ =
      ψ (Multiplicative.ofAdd (((μ ^ (e * k) : GFˣ) : GF) * Multiplicative.toAdd a)) := by
    intro k
    induction k with
    | zero =>
      intro a
      simp
    | succ k ih =>
      intro a
      have h1 : c ^ (k + 1) * ψ a * (c ^ (k + 1))⁻¹ = c ^ k * (c * ψ a * c⁻¹) * (c ^ k)⁻¹ := by
        group
      rw [h1, hc, ih]
      congr 2
      simp only [toAdd_ofAdd, Units.val_pow_eq_pow_val, ← mul_assoc, ← pow_add]
      ring_nf
  have hdvd := two_mul_dvd he
  have he0 : 0 < e := by rcases he with rfl | ⟨rfl, -⟩ <;> norm_num
  set m := (3 ^ n - 1) / (2 * e) with hm_def
  have hm : 2 * e * m = 3 ^ n - 1 := Nat.mul_div_cancel' hdvd
  have hm5 : 5 ≤ 2 * m := by
    rcases he with rfl | ⟨rfl, hn3, ⟨j, rfl⟩⟩
    · omega
    · have hj : 2 ≤ j := by omega
      have h81 : 81 ≤ 3 ^ (j + j) := by
        calc 81 = 3 ^ 4 := by norm_num
          _ ≤ 3 ^ (j + j) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have hμm : ((μ ^ (e * m) : GFˣ) : GF) = -1 := by
    apply eq_neg_one_of_sq_eq_one
    · rw [← Units.val_pow_eq_pow_val, ← pow_mul]
      have h : e * m * 2 = 3 ^ n - 1 := by rw [← hm]; ring
      rw [h, ← hordμ, pow_orderOf_eq_one, Units.val_one]
    · intro h1
      have h1' : μ ^ (e * m) = 1 := Units.val_eq_one.mp h1
      have h2 := orderOf_dvd_of_pow_eq_one h1'
      rw [hordμ] at h2
      have hpos : 0 < e * m := by
        apply Nat.mul_pos he0
        omega
      have hlt : e * m < 3 ^ n - 1 := by rw [← hm]; nlinarith
      exact absurd (Nat.le_of_dvd hpos h2) (by omega)
  refine ⟨isElemAbelian_range ψ, c, ?_, m, 2, hm5, by norm_num, ?_, ?_⟩
  ·
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, (hc a).symm⟩
    · rintro ⟨b, hb⟩
      refine ⟨Multiplicative.ofAdd ((((μ⁻¹ : GFˣ) : GF) ^ e) * Multiplicative.toAdd b), ?_⟩
      have h2 := hc (Multiplicative.ofAdd ((((μ⁻¹ : GFˣ) : GF) ^ e) * Multiplicative.toAdd b))
      have h3 : ((μ : GF) ^ e * Multiplicative.toAdd (Multiplicative.ofAdd
          ((((μ⁻¹ : GFˣ) : GF) ^ e) * Multiplicative.toAdd b))) = Multiplicative.toAdd b := by
        rw [toAdd_ofAdd, ← mul_assoc, ← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          one_pow, one_mul]
      rw [h3, ofAdd_toAdd, hb] at h2
      have h4 := congrArg (fun x => c⁻¹ * x * c) h2
      simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] at h4
      exact h4
  ·
    rintro _ ⟨a, rfl⟩
    rw [hck m a, hμm, neg_one_mul]
    have h3 : (ψ a) ^ 3 = 1 := (isElemAbelian_range ψ).2 _ ⟨a, rfl⟩
    have h5 : ψ (Multiplicative.ofAdd (-Multiplicative.toAdd a)) = (ψ a)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [h5, inv_eq_of_mul_eq_one_right]
    rw [← pow_succ', h3]
  ·
    intro k hk0 hkm F hFA hF3 hnorm
    set F' : Subgroup (Multiplicative GF) := F.comap ψ with hF'
    have hF'3 : F'.index = 3 := by rw [hF', Subgroup.index_comap]; exact hF3
    have hν0 : ((μ ^ (e * k) : GFˣ) : GF) ≠ 0 := Units.ne_zero _
    have hmul : ∀ x ∈ F', Multiplicative.ofAdd
        (((μ ^ (e * k) : GFˣ) : GF) * Multiplicative.toAdd x) ∈ F' := by
      intro x hx
      have hx' : ψ x ∈ F := hx
      have h1 := (Subgroup.mem_normalizer_iff.mp hnorm (ψ x)).mp hx'
      rw [hck k x] at h1
      exact h1
    rcases eq_one_or_eq_neg_one_of_mul_mem_mult hν0 hF'3 hmul with h1 | h1
    all_goals
      have h2 : (μ ^ (e * k)) ^ 2 = 1 := by
        apply Units.val_eq_one.mp
        rw [Units.val_pow_eq_pow_val, h1]
        norm_num
      rw [← pow_mul] at h2
      have h3 := orderOf_dvd_of_pow_eq_one h2
      rw [hordμ, ← hm] at h3
      have hpos : 0 < e * k * 2 := by positivity
      have hle := Nat.le_of_dvd hpos h3
      have hlt : e * k * 2 < 2 * e * m := by nlinarith
      omega

end CFSG.HardMathSupport.Foote.SPLScalar
