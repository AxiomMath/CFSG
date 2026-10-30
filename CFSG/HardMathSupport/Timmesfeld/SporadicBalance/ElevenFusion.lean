module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FixedFreeRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

@[expose] def lineActN (l : Bool) (v : ℕ × ℕ) : ℕ × ℕ :=
  if l then ((6 * v.1 + 4 * v.2) % 11, (3 * v.1 + 4 * v.2) % 11) else ((8 * v.2) % 11, (4 * v.1) % 11)

@[expose] def wordActN : List Bool → ℕ × ℕ → ℕ × ℕ
  | [], v => v
  | l :: w, v => wordActN w (lineActN l v)

@[expose] def transporters : List (List Bool) :=
  [[], [true], [false], [true, true], [true, false], [true, true, false], [true, false, true],
    [true, true, false, true, true], [true, false, true, false],
    [true, false, true, false, true, true], [true, false, true, false, true],
    [true, true, false, true]]

@[expose] def coveredN (a b : ℕ) : Bool :=
  transporters.any fun w => (List.range 11).any fun j =>
    (j * (wordActN w (1, 0)).1) % 11 == a && (j * (wordActN w (1, 0)).2) % 11 == b

theorem covered_all : (List.range 11).all (fun a => (List.range 11).all fun b =>
    (a == 0 && b == 0) || coveredN a b) = true := by
  decide

variable {G : Type*} [Group G]

section Action

variable {x y x₃ x₄ : G} (hx : x ^ 11 = 1) (hy : y ^ 11 = 1) (hxy : x * y = y * x)

@[expose] def eps (x y : G) (v : ℕ × ℕ) : G := x ^ v.1 * y ^ v.2

include hx hy in
theorem eps_mod (v : ℕ × ℕ) : eps x y v = eps x y (v.1 % 11, v.2 % 11) := by
  unfold eps
  rw [← pow_mod_orderOf, ← pow_mod_orderOf (x := y)]
  conv_rhs => rw [← pow_mod_orderOf, ← pow_mod_orderOf (x := y)]
  have h1 : orderOf x ∣ 11 := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf y ∣ 11 := orderOf_dvd_of_pow_eq_one hy
  rw [Nat.mod_mod_of_dvd _ h1, Nat.mod_mod_of_dvd _ h2]

include hxy in
theorem eps_mul_eps (u v : ℕ × ℕ) : eps x y u * eps x y v = eps x y (u.1 + v.1, u.2 + v.2) := by
  unfold eps
  have hc : Commute x y := hxy
  rw [pow_add, pow_add]
  calc x ^ u.1 * y ^ u.2 * (x ^ v.1 * y ^ v.2) = x ^ u.1 * (y ^ u.2 * x ^ v.1) * y ^ v.2 := by group
    _ = x ^ u.1 * (x ^ v.1 * y ^ u.2) * y ^ v.2 := by
        rw [((hc.pow_pow v.1 u.2).symm).eq]
    _ = x ^ u.1 * x ^ v.1 * (y ^ u.2 * y ^ v.2) := by group

include hxy in
theorem eps_pow (v : ℕ × ℕ) (k : ℕ) : eps x y v ^ k = eps x y (k * v.1, k * v.2) := by
  induction k with
  | zero => simp [eps]
  | succ k ih =>
    rw [pow_succ, ih, eps_mul_eps hxy]
    congr 1 <;> ring

end Action

@[expose] def letterG (x₃ x₄ : G) (l : Bool) : G := if l then x₃ else x₄

@[expose] def wordG (x₃ x₄ : G) : List Bool → G
  | [] => 1
  | l :: w => wordG x₃ x₄ w * letterG x₃ x₄ l

section Conj

variable {x y x₃ x₄ : G} (hx : x ^ 11 = 1) (hy : y ^ 11 = 1) (hxy : x * y = y * x)
  (h3x : x₃ * x * x₃⁻¹ = x ^ 6 * y ^ 3) (h3y : x₃ * y * x₃⁻¹ = x ^ 4 * y ^ 4)
  (h4x : x₄ * x * x₄⁻¹ = y ^ 4) (h4y : x₄ * y * x₄⁻¹ = x ^ 8)

theorem conj_eps (g : G) (v : ℕ × ℕ) :
    g * eps x y v * g⁻¹ = (g * x * g⁻¹) ^ v.1 * (g * y * g⁻¹) ^ v.2 := by
  unfold eps
  rw [← MulAut.conj_apply, map_mul, map_pow, map_pow, MulAut.conj_apply, MulAut.conj_apply]

include hx hy hxy h3x h3y h4x h4y in
theorem conj_letter_eps (l : Bool) (v : ℕ × ℕ) :
    letterG x₃ x₄ l * eps x y v * (letterG x₃ x₄ l)⁻¹ = eps x y (lineActN l v) := by
  rw [conj_eps]
  cases l
  · simp only [letterG, Bool.false_eq_true, ite_false, lineActN]
    rw [h4x, h4y]
    have e1 : (y ^ 4) ^ v.1 = eps x y (0, 4 * v.1) := by simp [eps, ← pow_mul, mul_comm]
    have e2 : (x ^ 8) ^ v.2 = eps x y (8 * v.2, 0) := by simp [eps, ← pow_mul, mul_comm]
    rw [e1, e2, eps_mul_eps hxy, eps_mod hx hy]
    simp
  · simp only [letterG, ite_true, lineActN]
    rw [h3x, h3y]
    have e1 : (x ^ 6 * y ^ 3) ^ v.1 = eps x y (6 * v.1, 3 * v.1) := by
      have := eps_pow hxy (6, 3) v.1
      simp only [eps] at this ⊢
      rw [this]; ring_nf
    have e2 : (x ^ 4 * y ^ 4) ^ v.2 = eps x y (4 * v.2, 4 * v.2) := by
      have := eps_pow hxy (4, 4) v.2
      simp only [eps] at this ⊢
      rw [this]; ring_nf
    rw [e1, e2, eps_mul_eps hxy, eps_mod hx hy]

include hx hy hxy h3x h3y h4x h4y in
theorem conj_word_eps (w : List Bool) (v : ℕ × ℕ) :
    wordG x₃ x₄ w * eps x y v * (wordG x₃ x₄ w)⁻¹ = eps x y (wordActN w v) := by
  induction w generalizing v with
  | nil => simp [wordG, wordActN]
  | cons l w ih =>
    rw [wordG, wordActN, ← ih]
    rw [← conj_letter_eps hx hy hxy h3x h3y h4x h4y l v]
    group

include hx hy hxy h3x h3y h4x h4y in
theorem exists_conj_pow_of_mem_lines {a b : ℕ} (ha : a < 11) (hb : b < 11) (hab : ¬(a = 0 ∧ b = 0)) :
    ∃ g : G, ∃ j : ℕ, eps x y (a, b) = g * x ^ j * g⁻¹ := by
  have h := covered_all
  rw [List.all_eq_true] at h
  have h1 := h a (List.mem_range.2 ha)
  rw [List.all_eq_true] at h1
  have h2 := h1 b (List.mem_range.2 hb)
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h2
  rcases h2 with h2 | h2
  · exact absurd h2 hab
  · unfold coveredN at h2
    rw [List.any_eq_true] at h2
    obtain ⟨w, -, hw⟩ := h2
    rw [List.any_eq_true] at hw
    obtain ⟨j, -, hj⟩ := hw
    simp only [Bool.and_eq_true, beq_iff_eq] at hj
    refine ⟨wordG x₃ x₄ w, j, ?_⟩
    have hxe : x = eps x y (1, 0) := by simp [eps]
    have : wordG x₃ x₄ w * x ^ j * (wordG x₃ x₄ w)⁻¹ = (wordG x₃ x₄ w * x * (wordG x₃ x₄ w)⁻¹) ^ j :=
      by rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
    rw [this]
    conv_rhs => rw [hxe]
    rw [conj_word_eps hx hy hxy h3x h3y h4x h4y, eps_pow hxy]
    conv_rhs => rw [eps_mod hx hy]
    simp only
    rw [hj.1, hj.2]

end Conj

section Sylow

variable {x y x₃ x₄ : G} (hx : x ^ 11 = 1) (hy : y ^ 11 = 1) (hxy : x * y = y * x)

@[expose] def epsSubgroup : Subgroup G where
  carrier := {g | ∃ v : ℕ × ℕ, g = eps x y v}
  mul_mem' := by
    rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨_, eps_mul_eps hxy u v⟩
  one_mem' := ⟨(0, 0), by simp [eps]⟩
  inv_mem' := by
    rintro _ ⟨v, rfl⟩
    refine ⟨(10 * v.1, 10 * v.2), ?_⟩
    apply inv_eq_of_mul_eq_one_right
    rw [eps_mul_eps hxy, eps_mod hx hy]
    have h1 : (v.1 + 10 * v.1) % 11 = 0 := by omega
    have h2 : (v.2 + 10 * v.2) % 11 = 0 := by omega
    simp only [h1, h2]
    simp [eps]

include hx hy in
theorem mem_epsSubgroup_iff {g : G} :
    g ∈ epsSubgroup hx hy hxy ↔ ∃ a < 11, ∃ b < 11, g = eps x y (a, b) := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v.1 % 11, Nat.mod_lt _ (by norm_num), v.2 % 11, Nat.mod_lt _ (by norm_num),
      eps_mod hx hy v⟩
  · rintro ⟨a, -, b, -, rfl⟩
    exact ⟨(a, b), rfl⟩

include hx hy in
theorem isPGroup_epsSubgroup : IsPGroup 11 (epsSubgroup hx hy hxy) := by
  rintro ⟨g, v, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  show eps x y v ^ 11 ^ 1 = 1
  rw [pow_one, eps_pow hxy, eps_mod hx hy]
  simp [eps]

include hx hy in
theorem card_epsSubgroup [Finite G] (hx1 : x ≠ 1) (hyx : ∀ k : ℕ, y ≠ x ^ k)
    (hcard : (Nat.card G).factorization 11 = 2) :
    Nat.card (epsSubgroup hx hy hxy) = 11 ^ 2 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨m, hm⟩ := (isPGroup_epsSubgroup hx hy hxy).exists_card_eq
  have hm2 : m ≤ 2 := by
    have h1 : 11 ^ m ∣ Nat.card G := hm ▸ Subgroup.card_subgroup_dvd_card _
    rw [← hcard]
    exact (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) Nat.card_pos.ne').1 h1
  have hxE : x ∈ epsSubgroup hx hy hxy := ⟨(1, 0), by simp [eps]⟩
  have hyE : y ∈ epsSubgroup hx hy hxy := ⟨(0, 1), by simp [eps]⟩
  have hle : Subgroup.zpowers x ≤ epsSubgroup hx hy hxy := by
    rw [Subgroup.zpowers_le]; exact hxE
  have hne : Subgroup.zpowers x ≠ epsSubgroup hx hy hxy := by
    classical
    intro h
    rw [← h] at hyE
    rw [mem_zpowers_iff_mem_range_orderOf, Finset.mem_image] at hyE
    obtain ⟨k, -, hk⟩ := hyE
    exact hyx k hk.symm
  have hlt := Subgroup.card_lt_of_lt (lt_of_le_of_ne hle hne)
  rw [Nat.card_zpowers, orderOf_eq_prime hx hx1, hm] at hlt
  have hm1 : 2 ≤ m := by
    by_contra hc
    push Not at hc
    interval_cases m <;> norm_num at hlt
  rw [hm, show m = 2 by omega]

include hx hy hxy in
theorem exists_conj_pow_of_eleven_lines [Finite G]
    (h3x : x₃ * x * x₃⁻¹ = x ^ 6 * y ^ 3) (h3y : x₃ * y * x₃⁻¹ = x ^ 4 * y ^ 4)
    (h4x : x₄ * x * x₄⁻¹ = y ^ 4) (h4y : x₄ * y * x₄⁻¹ = x ^ 8) (hx1 : x ≠ 1)
    (hcard : (Nat.card G).factorization 11 = 2) {s : G} (hs : orderOf s = 11) :
    ∃ g : G, ∃ k : ℕ, s = g * x ^ k * g⁻¹ := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hox : orderOf x = 11 := orderOf_eq_prime hx hx1
  have hyx : ∀ k : ℕ, y ≠ x ^ k := by
    intro k hk
    have h1 : x₄ * y * x₄⁻¹ = (x₄ * x * x₄⁻¹) ^ k := by
      rw [hk, ← MulAut.conj_apply, map_pow, MulAut.conj_apply]
    rw [h4y, h4x, hk, ← pow_mul, ← pow_mul] at h1
    have h2 := (pow_eq_pow_iff_modEq.1 h1)
    rw [hox] at h2
    have h3 : (8 : ℕ) % 11 = (k * (4 * k)) % 11 := h2
    have h4 : (k * (4 * k)) % 11 = (4 * ((k % 11) * (k % 11))) % 11 := by
      rw [show k * (4 * k) = 4 * (k * k) by ring, Nat.mul_mod, Nat.mul_mod k k]
      simp [Nat.mul_mod]
    rw [h4] at h3
    have hk11 : k % 11 < 11 := Nat.mod_lt _ (by norm_num)
    generalize k % 11 = r at h3 hk11
    interval_cases r <;> norm_num at h3
  set E := epsSubgroup hx hy hxy with hEdef
  have hEc := card_epsSubgroup hx hy hxy hx1 hyx hcard
  let P : Sylow 11 G := Sylow.ofCard E (by rw [hEc, hcard])
  have hsz : IsPGroup 11 (Subgroup.zpowers s) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨Q, hQ⟩ := hsz.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hsQ : s ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers s)
  rw [← hg, Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at hsQ
  obtain ⟨t, ht, hts⟩ := (Subgroup.mem_smul_pointwise_iff_exists s (MulAut.conj g) E).1 hsQ
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_epsSubgroup_iff hx hy hxy).1 ht
  have hab : ¬(a = 0 ∧ b = 0) := by
    rintro ⟨rfl, rfl⟩
    simp only [eps, pow_zero, mul_one, MulAut.smul_def, MulAut.conj_apply, mul_inv_cancel] at hts
    rw [← hts, orderOf_one] at hs
    norm_num at hs
  obtain ⟨h, j, hj⟩ := exists_conj_pow_of_mem_lines hx hy hxy h3x h3y h4x h4y ha hb hab
  refine ⟨g * h, j, ?_⟩
  rw [← hts, MulAut.smul_def, MulAut.conj_apply, hj]
  group

end Sylow

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
