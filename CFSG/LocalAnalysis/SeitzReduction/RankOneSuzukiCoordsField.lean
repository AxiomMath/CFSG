module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteLinearized

public section

namespace CFSG.SeitzReduction.RankOne.SzCoords

section Exponent

theorem eq_of_two_pow_add_two_pow {x y z : ℕ} (h : 2 ^ x + 2 ^ y = 2 ^ z) : x = y := by
  rcases Nat.lt_trichotomy x y with hxy | rfl | hxy
  · exfalso
    have h1 : 2 ^ x * (1 + 2 ^ (y - x)) = 2 ^ z := by
      rw [mul_add, mul_one, ← pow_add, Nat.add_sub_cancel' hxy.le, h]
    have hxz : x < z := by
      by_contra hzx
      push Not at hzx
      have : 2 ^ z ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hzx
      have : 0 < 2 ^ y := by positivity
      omega
    have h2 : 1 + 2 ^ (y - x) = 2 ^ (z - x) := by
      have h3 : 2 ^ z = 2 ^ x * 2 ^ (z - x) := by rw [← pow_add, Nat.add_sub_cancel' hxz.le]
      rw [h3] at h1
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
    have hev : 2 ∣ 2 ^ (z - x) := dvd_pow_self 2 (by omega)
    have hev' : 2 ∣ 2 ^ (y - x) := dvd_pow_self 2 (by omega)
    omega
  · rfl
  · exfalso
    have h1 : 2 ^ y * (1 + 2 ^ (x - y)) = 2 ^ z := by
      rw [mul_add, mul_one, ← pow_add, Nat.add_sub_cancel' hxy.le, add_comm, h]
    have hyz : y < z := by
      by_contra hzy
      push Not at hzy
      have : 2 ^ z ≤ 2 ^ y := Nat.pow_le_pow_right (by norm_num) hzy
      have : 0 < 2 ^ x := by positivity
      omega
    have h2 : 1 + 2 ^ (x - y) = 2 ^ (z - y) := by
      have h3 : 2 ^ z = 2 ^ y * 2 ^ (z - y) := by rw [← pow_add, Nat.add_sub_cancel' hyz.le]
      rw [h3] at h1
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
    have hev : 2 ∣ 2 ^ (z - y) := dvd_pow_self 2 (by omega)
    have hev' : 2 ∣ 2 ^ (x - y) := dvd_pow_self 2 (by omega)
    omega

theorem eq_succ_of_two_pow_add_self {x z : ℕ} (h : 2 ^ x + 2 ^ x = 2 ^ z) : z = x + 1 := by
  have h1 : 2 ^ (x + 1) = 2 ^ z := by rw [pow_succ]; omega
  exact (Nat.pow_right_injective le_rfl h1).symm

theorem sum_three_eq_one_add {i j k b : ℕ} (hb : 1 ≤ b)
    (h : 2 ^ i + 2 ^ j + 2 ^ k = 1 + 2 ^ b) :
    (i = 0 ∧ j = k) ∨ (j = 0 ∧ i = k ∧ b = i + 1) ∨ (k = 0 ∧ i = j ∧ b = i + 1) := by
  have hev : ∀ m, m ≠ 0 → 2 ∣ 2 ^ m := fun m hm => dvd_pow_self 2 hm
  have hb2 := hev b (by omega)
  by_cases hi : i = 0
  · subst hi
    refine Or.inl ⟨rfl, eq_of_two_pow_add_two_pow (z := b) (by rw [pow_zero] at h; omega)⟩
  by_cases hj : j = 0
  · subst hj
    have h1 : 2 ^ i + 2 ^ k = 2 ^ b := by rw [pow_zero] at h; omega
    have hik := eq_of_two_pow_add_two_pow h1
    subst hik
    exact Or.inr (Or.inl ⟨rfl, rfl, eq_succ_of_two_pow_add_self h1⟩)
  by_cases hk : k = 0
  · subst hk
    have h1 : 2 ^ i + 2 ^ j = 2 ^ b := by rw [pow_zero] at h; omega
    have hij := eq_of_two_pow_add_two_pow h1
    subst hij
    exact Or.inr (Or.inr ⟨rfl, rfl, eq_succ_of_two_pow_add_self h1⟩)
  exfalso
  have := hev i hi
  have := hev j hj
  have := hev k hk
  omega

theorem sum_three_eq_pow_add {i j k n b : ℕ} (hi : i < n) (hj : j < n) (hk : k < n)
    (h : 2 ^ i + 2 ^ j + 2 ^ k = 2 ^ n + 2 ^ b) :
    (i = n - 1 ∧ j = n - 1 ∧ k = b) ∨ (i = n - 1 ∧ k = n - 1 ∧ j = b) ∨
      (j = n - 1 ∧ k = n - 1 ∧ i = b) := by
  have hn : 1 ≤ n := by omega
  have hpow : ∀ m, m < n → 2 ^ m ≤ 2 ^ (n - 1) := fun m hm =>
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlt : ∀ m, m < n → m ≠ n - 1 → 2 * 2 ^ m ≤ 2 ^ (n - 1) := fun m hm hne => by
    rw [← pow_succ']
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hN : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  have hbpos : 0 < 2 ^ b := by positivity
  have hi' := hpow i hi
  have hj' := hpow j hj
  have hk' := hpow k hk
  by_cases hin : i = n - 1
  · by_cases hjn : j = n - 1
    · subst hin hjn
      left
      exact ⟨rfl, rfl, Nat.pow_right_injective le_rfl (show 2 ^ k = 2 ^ b by omega)⟩
    · by_cases hkn : k = n - 1
      · subst hin hkn
        exact Or.inr (Or.inl ⟨rfl, rfl, Nat.pow_right_injective le_rfl
          (show 2 ^ j = 2 ^ b by omega)⟩)
      · exfalso
        have := hlt j hj hjn
        have := hlt k hk hkn
        omega
  · by_cases hjn : j = n - 1
    · by_cases hkn : k = n - 1
      · subst hjn hkn
        exact Or.inr (Or.inr ⟨rfl, rfl, Nat.pow_right_injective le_rfl
          (show 2 ^ i = 2 ^ b by omega)⟩)
      · exfalso
        have := hlt i hi hin
        have := hlt k hk hkn
        omega
    · exfalso
      have := hlt i hi hin
      have := hlt j hj hjn
      omega

theorem exp_eq_of_dvd {a i j : ℕ} (ha : 1 ≤ a) (hi : i < 2 * a + 1) (hj : j < 2 * a + 1)
    (h : 2 ^ (2 * a + 1) - 1 ∣
      2 ^ i + (2 ^ (a + 1) + 1) * 2 ^ j + (2 ^ (2 * a + 1) - 2 - 2 ^ (a + 1))) :
    i = a ∧ j = a := by
  set n := 2 * a + 1 with hn
  set b := a + 1 with hbdef
  have hb1 : 1 ≤ b := by omega
  have hbn : b < n := by omega
  have h2b : 2 ^ b < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hbn
  have h4 : 4 ≤ 2 ^ b := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2b' : 2 * 2 ^ b ≤ 2 ^ n := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  set N := 2 ^ n - 1 with hNdef
  have hNn : 2 ^ n = N + 1 := by omega
  set k := (j + b) % n with hkdef
  have hkn : k < n := Nat.mod_lt _ (by omega)
  have hk' : (k = j + b ∧ j + b < n) ∨ (k = j + b - n ∧ n ≤ j + b) := by
    rcases Nat.lt_or_ge (j + b) n with hlt | hge
    · exact Or.inl ⟨Nat.mod_eq_of_lt hlt, hlt⟩
    · refine Or.inr ⟨?_, hge⟩
      rw [hkdef, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
  have hjk : j ≠ k := by omega
  have hjb : 2 ^ (j + b) = 2 ^ k + N * (2 ^ k * (if j + b < n then 0 else 1)) := by
    rcases hk' with ⟨hk1, hlt⟩ | ⟨hk1, hge⟩
    · rw [ite_eq_left_iff.mpr (fun h => absurd hlt h), mul_zero, mul_zero, add_zero, hk1]
    · rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)), mul_one,
        show j + b = k + n by omega, pow_add, hNn]
      ring
  set X := 2 ^ i + 2 ^ j + 2 ^ k with hX
  have hXpos : 3 ≤ X := by
    have := Nat.one_le_two_pow (n := i)
    have := Nat.one_le_two_pow (n := j)
    have := Nat.one_le_two_pow (n := k)
    omega
  have hXle : X ≤ 3 * 2 ^ (n - 1) := by
    have hpow : ∀ m, m < n → 2 ^ m ≤ 2 ^ (n - 1) := fun m hm =>
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have := hpow i hi
    have := hpow j hj
    have := hpow k hkn
    omega
  have hNhalf : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1
  have hdvd : N ∣ X + N - (1 + 2 ^ b) := by
    have e1 : 2 ^ i + (2 ^ b + 1) * 2 ^ j + (2 ^ n - 2 - 2 ^ b) =
        N * (2 ^ k * (if j + b < n then 0 else 1)) + (X + N - (1 + 2 ^ b)) := by
      have e2 : (2 ^ b + 1) * 2 ^ j = 2 ^ (j + b) + 2 ^ j := by rw [pow_add]; ring
      rw [e2, hjb, hX]
      omega
    rw [e1] at h
    exact (Nat.dvd_add_right (dvd_mul_right N _)).mp h
  obtain ⟨m, hm⟩ := hdvd
  have hm1 : 1 ≤ m := by
    have hpos : 0 < N * m := by omega
    exact Nat.pos_of_mul_pos_left hpos
  have hm2 : m ≤ 2 := by
    by_contra hm3
    push Not at hm3
    have : N * 3 ≤ N * m := Nat.mul_le_mul_left N hm3
    omega
  rcases (show m = 1 ∨ m = 2 by omega) with rfl | rfl
  ·
    have hXY : 2 ^ i + 2 ^ j + 2 ^ k = 1 + 2 ^ b := by omega
    rcases sum_three_eq_one_add hb1 hXY with ⟨-, hjk'⟩ | ⟨rfl, hik, hbi⟩ | ⟨hk0, hij, hbi⟩
    · exact absurd hjk' hjk
    · exfalso
      have hk : k = b := by rw [hkdef, Nat.zero_add, Nat.mod_eq_of_lt hbn]
      omega
    · exact ⟨by omega, by omega⟩
  ·
    exfalso
    have hXY : 2 ^ i + 2 ^ j + 2 ^ k = 2 ^ n + 2 ^ b := by omega
    rcases sum_three_eq_pow_add hi hj hkn hXY with ⟨-, hjn, hkb⟩ | ⟨hin, hkn', hjb'⟩ |
        ⟨hjn, hkn', -⟩
    ·
      have : k = a := by
        rw [hkdef, hjn, show n - 1 + b = a + 1 * n by omega, Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt (by omega)]
      omega
    ·
      have : k = 1 := by
        rw [hkdef, hjb', show b + b = 1 + 1 * n by omega, Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt (by omega)]
      omega
    · exact hjk (by omega)

end Exponent

section Equivariant

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type*} [Field K] [Fintype K]

omit [Fintype K] in
theorem linear_of_equivariant {f : K → K} {μ : K} (hf : ∀ w, f (μ * w) = μ * f w)
    (h0 : f 0 = 0) (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) (w : K) : f w = f 1 * w := by
  by_cases hw : w = 0
  · rw [hw, h0, mul_zero]
  obtain ⟨m, rfl⟩ := hμ w hw
  have : ∀ m : ℕ, f (μ ^ m) = μ ^ m * f 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', hf, ih, mul_assoc]
  rw [this, mul_comm]

theorem bilinear_of_equivariant [CharP K 2] {a : ℕ} (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (β : K →+ K →+ K) {κ : K}
    (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w)
    (hβ : ∀ u w, β (κ * u) (κ ^ (2 ^ (a + 1) + 1) * w) = κ ^ (2 ^ (a + 1) + 1) * β u w) :
    ∃ c : K, ∀ u w, β u w = c * (u * w) ^ 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set n := 2 * a + 1 with hn
  have hcard : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hK]
  obtain ⟨-, hb, -⟩ := finite_field_linearized_map_bases Nat.prime_two (by omega) hcard
  obtain ⟨c, hc, -⟩ := hb β
  have hlt : 2 ^ (n - 1) < Fintype.card K := by
    rw [hK]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hκ0 : κ ≠ 0 := by
    classical
    rintro rfl
    obtain ⟨w, hw0, hw1⟩ : ∃ w : K, w ≠ 0 ∧ w ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun w _ => by
        by_cases hw : w = 0
        · simp [hw]
        · simp [hcon w hw]
      have h1 := (Finset.card_le_card hsub).trans Finset.card_le_two
      rw [Finset.card_univ, hK] at h1
      have h2 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact absurd (h2.trans h1) (by norm_num)
    obtain ⟨m, hm⟩ := hκ w hw0
    rcases m with _ | m
    · exact hw1 (by rw [← hm, pow_zero])
    · exact hw0 (by rw [← hm, zero_pow (Nat.succ_ne_zero _)])
  have hcoef : ∀ i j : Fin n, c i j * κ ^ (2 ^ (i : ℕ) + (2 ^ (a + 1) + 1) * 2 ^ (j : ℕ)) =
      c i j * κ ^ (2 ^ (a + 1) + 1) := by
    have h := eq_zero_of_forall_sum_sum_mul_pow_eq_zero hlt
      (a := fun i j => c i j * κ ^ (2 ^ (i : ℕ) + (2 ^ (a + 1) + 1) * 2 ^ (j : ℕ)) -
        c i j * κ ^ (2 ^ (a + 1) + 1)) fun u w => by
        have h1 := hβ u w
        rw [hc, hc] at h1
        simp only [sub_mul, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        calc ∑ i, ∑ j, c i j * κ ^ (2 ^ (i : ℕ) + (2 ^ (a + 1) + 1) * 2 ^ (j : ℕ)) *
              (u ^ 2 ^ (i : ℕ) * w ^ 2 ^ (j : ℕ)) =
            ∑ i, ∑ j, c i j * ((κ * u) ^ 2 ^ (i : ℕ) *
              (κ ^ (2 ^ (a + 1) + 1) * w) ^ 2 ^ (j : ℕ)) := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
              rw [mul_pow, mul_pow, ← pow_mul, pow_add]
              ring
          _ = κ ^ (2 ^ (a + 1) + 1) * ∑ i, ∑ j, c i j * (u ^ 2 ^ (i : ℕ) * w ^ 2 ^ (j : ℕ)) :=
              h1
          _ = _ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
    intro i j
    exact sub_eq_zero.mp (congrFun (congrFun h i) j)
  have horder : orderOf κ = 2 ^ n - 1 := by
    have hu : IsUnit κ := Ne.isUnit hκ0
    have hgen : ∀ w : Kˣ, w ∈ Subgroup.zpowers hu.unit := by
      intro w
      obtain ⟨m, hm⟩ := hκ w w.ne_zero
      exact ⟨m, Units.ext (by simp [hm])⟩
    have h1 : orderOf hu.unit = Nat.card Kˣ :=
      (orderOf_eq_card_of_forall_mem_zpowers hgen)
    rw [Nat.card_units, hcard] at h1
    rw [← h1, ← orderOf_units, IsUnit.unit_spec]
  have hzero : ∀ i j : Fin n, ((i : ℕ) ≠ a ∨ (j : ℕ) ≠ a) → c i j = 0 := by
    intro i j hij
    by_contra hcij
    have h1 := mul_left_cancel₀ hcij (hcoef i j)
    have hq : κ ^ (2 ^ n - 1) = 1 := by rw [← horder]; exact pow_orderOf_eq_one κ
    have hE : κ ^ (2 ^ (i : ℕ) + (2 ^ (a + 1) + 1) * 2 ^ (j : ℕ) +
        (2 ^ n - 2 - 2 ^ (a + 1))) = 1 := by
      have h2 : 2 * 2 ^ (a + 1) ≤ 2 ^ n := by
        rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : 2 ≤ 2 ^ (a + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have e : 2 ^ (a + 1) + 1 + (2 ^ n - 2 - 2 ^ (a + 1)) = 2 ^ n - 1 := by
        generalize 2 ^ (a + 1) = T at h2 h3 ⊢
        generalize 2 ^ n = N at h2 ⊢
        omega
      rw [pow_add κ, h1, ← pow_add, e, hq]
    have hdvd := orderOf_dvd_of_pow_eq_one hE
    rw [horder] at hdvd
    have := exp_eq_of_dvd ha i.2 j.2 hdvd
    omega
  refine ⟨c ⟨a, by omega⟩ ⟨a, by omega⟩, fun u w => ?_⟩
  rw [hc]
  rw [Finset.sum_eq_single ⟨a, by omega⟩, Finset.sum_eq_single ⟨a, by omega⟩]
  · rw [mul_pow]
  · intro j _ hj
    rw [hzero _ _ (Or.inr fun h => hj (Fin.ext h)), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hzero _ _ (Or.inl fun h => hi (Fin.ext h)), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem bilinear_of_equivariant' [CharP K 2] {a : ℕ} (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (β : K → K → K)
    (h1 : ∀ u u' w, β (u + u') w = β u w + β u' w) (h2 : ∀ u w w', β u (w + w') = β u w + β u w')
    {κ : K} (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w)
    (hβ : ∀ u w, β (κ * u) (κ ^ (2 ^ (a + 1) + 1) * w) = κ ^ (2 ^ (a + 1) + 1) * β u w) :
    ∃ c : K, ∀ u w, β u w = c * (u * w) ^ 2 ^ a :=
  bilinear_of_equivariant ha hK (AddMonoidHom.mk' (fun u => AddMonoidHom.mk' (β u) (h2 u))
    fun u u' => AddMonoidHom.ext fun w => h1 u u' w) hκ hβ

end Equivariant

end CFSG.SeitzReduction.RankOne.SzCoords
