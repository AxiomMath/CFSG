module

public import CFSG.LieType.Ree.ReeTorus

public section

namespace CFSG.LieType.Ree.LargeReeCover

open CFSG.Blueprint.Chevalley ReeTag

abbrev f4i (i : Fin 4) : Fin F4.tag.rank :=
  Fin.cast rfl i

@[expose] def torusExp0 (θ : ℤ) (β : Fin F4.tag.rank → ℤ) : ℤ :=
  F4.cartanPair (f4i 0) β + F4.cartanPair (f4i 3) β * θ

@[expose] def torusExp1 (θ : ℤ) (β : Fin F4.tag.rank → ℤ) : ℤ :=
  F4.cartanPair (f4i 1) β + F4.cartanPair (f4i 2) β * θ

section Arith

theorem four_le_two_pow {a : ℕ} (ha : 2 ≤ a) : (4 : ℤ) ≤ 2 ^ a := by
  calc (4 : ℤ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) ha

theorem two_pow_two_mul_add_one (a : ℕ) :
    (2 : ℤ) ^ (2 * a + 1) = 2 * (2 ^ a) ^ 2 - 1 + 1 := by
  rw [pow_succ, pow_mul, ← pow_mul, ← pow_mul, mul_comm a 2]
  ring

theorem odd_modulus (θ : ℤ) : Odd (2 * θ ^ 2 - 1) :=
  ⟨θ ^ 2 - 1, by ring⟩

theorem isCoprime_two_pow (θ : ℤ) (i : ℕ) : IsCoprime (2 * θ ^ 2 - 1) (2 ^ i) := by
  refine IsCoprime.pow_right ?_
  exact ⟨-1, θ ^ 2, by ring⟩

theorem not_dvd_two_mul {θ x : ℤ} (h : ¬ (2 * θ ^ 2 - 1) ∣ x) : ¬ (2 * θ ^ 2 - 1) ∣ 2 * x :=
  fun h2 => h ((isCoprime_two_pow θ 1).dvd_of_dvd_mul_left (by simpa using h2))

@[expose] def goodND (x y : ℤ) : Bool :=
  decide (|y| ≤ 16 ∧ |x| + 4 * |y| < 31 ∧ ((y = 0 ∧ x ≠ 0) ∨ (y ≠ 0 ∧ |x| < 4 * |y|)))

@[expose] def goodRed : ℕ → ℤ → ℤ → Bool
  | 0, x, y => goodND x y
  | n + 1, x, y => goodND x y || (x % 2 == 0 && y % 2 == 0 && goodRed n (x / 2) (y / 2))

theorem not_dvd_of_goodND {θ x y : ℤ} (hθ : 4 ≤ θ) (h : goodND x y = true) :
    ¬ (2 * θ ^ 2 - 1) ∣ x + y * θ := by
  simp only [goodND, decide_eq_true_eq] at h
  obtain ⟨hy, hxy, hne⟩ := h
  have hx0 := abs_nonneg x
  have hy0 := abs_nonneg y
  have hv : x + y * θ ≠ 0 := by
    rcases hne with ⟨rfl, hx⟩ | ⟨hy', hlt⟩
    · simpa using hx
    · intro h0
      have h1 : |x| = |y| * θ := by
        rw [show x = -(y * θ) by linarith, abs_neg, abs_mul, abs_of_pos (by linarith : 0 < θ)]
      have h2 : 1 ≤ |y| := Int.one_le_abs hy'
      nlinarith [mul_le_mul_of_nonneg_left hθ hy0]
  have hlt : |x + y * θ| < 2 * θ ^ 2 - 1 := by
    have h1 : |x + y * θ| ≤ |x| + |y| * θ := by
      calc |x + y * θ| ≤ |x| + |y * θ| := abs_add_le _ _
        _ = |x| + |y| * θ := by rw [abs_mul, abs_of_pos (by linarith : 0 < θ)]
    nlinarith [mul_nonneg (sub_nonneg.2 hy) (sub_nonneg.2 hθ), sq_nonneg (θ - 4)]
  exact fun hd => hv (Int.eq_zero_of_abs_lt_dvd hd hlt)

theorem not_dvd_of_goodRed {θ : ℤ} (hθ : 4 ≤ θ) :
    ∀ (n : ℕ) (x y : ℤ), goodRed n x y = true → ¬ (2 * θ ^ 2 - 1) ∣ x + y * θ
  | 0, x, y, h => not_dvd_of_goodND hθ h
  | n + 1, x, y, h => by
    simp only [goodRed, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with h | ⟨⟨hx, hy⟩, h⟩
    · exact not_dvd_of_goodND hθ h
    · have e : x + y * θ = 2 * (x / 2 + y / 2 * θ) := by
        have hx' : x = 2 * (x / 2) := by omega
        have hy' : y = 2 * (y / 2) := by omega
        linear_combination hx' + θ * hy'
      rw [e]
      exact not_dvd_two_mul (not_dvd_of_goodRed hθ n _ _ h)

@[expose] def unitForm (p q : ℤ) : Bool :=
  decide ((p, q) ∈ ([(1, 0), (-1, 0), (0, 1), (0, -1), (2, 0), (-2, 0), (0, 2), (0, -2), (-1, 1),
    (1, -1), (1, -2), (-1, 2), (1, 1), (-1, -1), (1, 2), (-1, -2)] : List (ℤ × ℤ)))

theorem isCoprime_of_unitForm {θ p q : ℤ} (h : unitForm p q = true) :
    IsCoprime (p + q * θ) (2 * θ ^ 2 - 1) := by
  simp only [unitForm, decide_eq_true_eq, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
    or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨1, 0, by ring⟩
  · exact ⟨-1, 0, by ring⟩
  · exact ⟨2 * θ, -1, by ring⟩
  · exact ⟨-2 * θ, -1, by ring⟩
  · exact ⟨θ ^ 2, -1, by ring⟩
  · exact ⟨-θ ^ 2, -1, by ring⟩
  · exact ⟨θ, -1, by ring⟩
  · exact ⟨-θ, -1, by ring⟩
  · exact ⟨-2 * (θ + 1), 1, by ring⟩
  · exact ⟨2 * (θ + 1), 1, by ring⟩
  · exact ⟨-(2 * θ + 1), -2, by ring⟩
  · exact ⟨2 * θ + 1, -2, by ring⟩
  · exact ⟨-2 * (θ - 1), 1, by ring⟩
  · exact ⟨2 * (θ - 1), 1, by ring⟩
  · exact ⟨2 * θ - 1, -2, by ring⟩
  · exact ⟨-(2 * θ - 1), -2, by ring⟩

@[expose] def depList : List (ℤ × ℤ) :=
  [(1, 0), (0, 2), (1, 2), (2, 2), (0, 1), (1, 1), (-1, 2), (2, -2), (1, -1)]

theorem exists_dvd_two_pow_add {a i j : ℕ} {l : ℤ}
    (h : (2 * (2 ^ a : ℤ) ^ 2 - 1) ∣ 2 ^ i + 2 ^ j * l) :
    ∃ g < 2 * a + 1, (2 * (2 ^ a : ℤ) ^ 2 - 1) ∣ 2 ^ g + l := by
  set N : ℤ := 2 * (2 ^ a : ℤ) ^ 2 - 1 with hN
  set f := 2 * a + 1 with hf
  have hf1 : (2 : ℤ) ^ f = N + 1 := two_pow_two_mul_add_one a
  have hpow : ∀ k : ℕ, N ∣ (2 : ℤ) ^ (f * k) - 1 := fun k => by
    have h1 := sub_dvd_pow_sub_pow ((2 : ℤ) ^ f) 1 k
    rw [one_pow, ← pow_mul, hf1, add_sub_cancel_right] at h1
    exact h1
  set e := i + j * (f - 1) with he
  have h1 : N ∣ 2 ^ e + l := by
    have h2 : N ∣ 2 ^ (j * (f - 1)) * (2 ^ i + 2 ^ j * l) := dvd_mul_of_dvd_right h _
    have h3 : N ∣ (2 ^ (f * j) - 1) * l := dvd_mul_of_dvd_left (hpow j) _
    have e1 : (2 : ℤ) ^ (j * (f - 1)) * (2 ^ i + 2 ^ j * l) - (2 ^ (f * j) - 1) * l =
        2 ^ e + l := by
      have e2 : f * j = j * (f - 1) + j := by
        have : 1 ≤ f := by omega
        rw [mul_comm f j, ← Nat.mul_add_one, Nat.sub_add_cancel this]
      rw [e2, pow_add, he, pow_add]
      ring
    rw [← e1]
    exact dvd_sub h2 h3
  refine ⟨e % f, Nat.mod_lt _ (by omega), ?_⟩
  have h4 : N ∣ (2 : ℤ) ^ e - 2 ^ (e % f) := by
    have e3 : (2 : ℤ) ^ e - 2 ^ (e % f) = (2 ^ (f * (e / f)) - 1) * 2 ^ (e % f) := by
      rw [sub_mul, one_mul, ← pow_add, Nat.div_add_mod]
    rw [e3]
    exact dvd_mul_of_dvd_left (hpow _) _
  have e4 : (2 : ℤ) ^ (e % f) + l = (2 ^ e + l) - (2 ^ e - 2 ^ (e % f)) := by ring
  rw [e4]
  exact dvd_sub h1 h4

theorem two_pow_le_sq {a g : ℕ} (hg : g < 2 * a + 1) : (2 : ℤ) ^ g ≤ (2 ^ a) ^ 2 := by
  rw [← pow_mul]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

theorem not_dvd_of_depList {a g : ℕ} (ha : 2 ≤ a) (hg : g < 2 * a + 1) {l : ℤ × ℤ}
    (hl : l ∈ depList) : ¬ (2 * (2 ^ a : ℤ) ^ 2 - 1) ∣ 2 ^ g + (l.1 + l.2 * 2 ^ a) := by
  have hθ := four_le_two_pow ha
  have ht := two_pow_le_sq hg
  have ht1 : (1 : ℤ) ≤ 2 ^ g := one_le_pow₀ (by norm_num)
  set θ : ℤ := 2 ^ a with hθdef
  set t : ℤ := 2 ^ g with htdef
  obtain ⟨s, hs⟩ : ∃ s : ℤ, θ = 4 * s := ⟨2 ^ (a - 2), by
    rw [hθdef, mul_comm, show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel ha]⟩
  have hv : ∀ v : ℤ, v ≠ 0 → |v| ≤ t + 2 + 2 * θ → ¬ (2 * θ ^ 2 - 1) ∣ v := fun v hv hb hd =>
    hv (Int.eq_zero_of_abs_lt_dvd hd
      (by nlinarith [mul_nonneg (sub_nonneg.2 hθ) (by linarith : (0 : ℤ) ≤ θ + 2)]))
  have hpar : t = 1 ∨ t = 2 ∨ ∃ u : ℤ, t = 4 * u := by
    rcases Nat.lt_or_ge g 2 with hg2 | hg2
    · interval_cases g
      · exact Or.inl (by rw [htdef]; norm_num)
      · exact Or.inr (Or.inl (by rw [htdef]; norm_num))
    · refine Or.inr (Or.inr ⟨2 ^ (g - 2), ?_⟩)
      rw [htdef, mul_comm, show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel hg2]
  simp only [depList, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine hv _ ?_ ?_ <;> simp only <;>
    first
    | (rw [abs_le]; constructor <;> nlinarith)
    | (intro h0; rcases hpar with h1 | h1 | ⟨u, h1⟩ <;> omega)

end Arith

@[expose] def depOK (a0 a1 b0 b1 c0 c1 d0 d1 : ℤ) : Bool :=
  (unitForm a0 a1 || unitForm b0 b1) &&
    depList.any fun l => decide (2 * c0 = 2 * l.1 * a0 + l.2 * a1 ∧ c1 = l.1 * a1 + l.2 * a0 ∧
      2 * d0 = 2 * l.1 * b0 + l.2 * b1 ∧ d1 = l.1 * b1 + l.2 * b0)

@[expose] def pairOK (a0 a1 b0 b1 c0 c1 d0 d1 : ℤ) : Bool :=
  goodRed 3 (2 * (a0 * d0 - b0 * c0) + (a1 * d1 - b1 * c1))
      (2 * (a0 * d1 + a1 * d0 - b0 * c1 - b1 * c0)) ||
    depOK a0 a1 b0 b1 c0 c1 d0 d1

theorem not_dvd_of_pairOK {a : ℕ} (ha : 2 ≤ a) {a0 a1 b0 b1 c0 c1 d0 d1 : ℤ}
    (h : pairOK a0 a1 b0 b1 c0 c1 d0 d1 = true) (i j : ℕ) :
    ¬ ((2 * (2 ^ a : ℤ) ^ 2 - 1) ∣ 2 ^ i * (a0 + a1 * 2 ^ a) + 2 ^ j * (c0 + c1 * 2 ^ a) ∧
      (2 * (2 ^ a : ℤ) ^ 2 - 1) ∣ 2 ^ i * (b0 + b1 * 2 ^ a) + 2 ^ j * (d0 + d1 * 2 ^ a)) := by
  have hθ := four_le_two_pow ha
  set θ : ℤ := 2 ^ a with hθdef
  set N : ℤ := 2 * θ ^ 2 - 1 with hN
  rintro ⟨h1, h2⟩
  simp only [pairOK, Bool.or_eq_true] at h
  rcases h with h | h
  ·
    have hD : N ∣ 2 ^ i * ((a0 + a1 * θ) * (d0 + d1 * θ) - (b0 + b1 * θ) * (c0 + c1 * θ)) := by
      have e : (2 : ℤ) ^ i * ((a0 + a1 * θ) * (d0 + d1 * θ) - (b0 + b1 * θ) * (c0 + c1 * θ)) =
          (2 ^ i * (a0 + a1 * θ) + 2 ^ j * (c0 + c1 * θ)) * (d0 + d1 * θ) -
            (2 ^ i * (b0 + b1 * θ) + 2 ^ j * (d0 + d1 * θ)) * (c0 + c1 * θ) := by ring
      rw [e]
      exact dvd_sub (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_left h2 _)
    have hD' := (isCoprime_two_pow θ i).dvd_of_dvd_mul_left hD
    have e2 : 2 * ((a0 + a1 * θ) * (d0 + d1 * θ) - (b0 + b1 * θ) * (c0 + c1 * θ)) =
        (2 * (a0 * d0 - b0 * c0) + (a1 * d1 - b1 * c1)) +
          2 * (a0 * d1 + a1 * d0 - b0 * c1 - b1 * c0) * θ + (a1 * d1 - b1 * c1) * N := by
      rw [hN]
      ring
    have hx : N ∣ (2 * (a0 * d0 - b0 * c0) + (a1 * d1 - b1 * c1)) +
        2 * (a0 * d1 + a1 * d0 - b0 * c1 - b1 * c0) * θ := by
      have h3 : N ∣ 2 * ((a0 + a1 * θ) * (d0 + d1 * θ) - (b0 + b1 * θ) * (c0 + c1 * θ)) :=
        dvd_mul_of_dvd_right hD' _
      rw [e2] at h3
      have h4 : N ∣ (a1 * d1 - b1 * c1) * N := dvd_mul_left _ _
      have := dvd_sub h3 h4
      rwa [add_sub_cancel_right] at this
    exact not_dvd_of_goodRed hθ 3 _ _ h hx
  ·
    simp only [depOK, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨hu, l, hl, e1, e2, e3, e4⟩ := h
    have hc : N ∣ (c0 + c1 * θ) - (l.1 + l.2 * θ) * (a0 + a1 * θ) := by
      refine (isCoprime_two_pow θ 1).dvd_of_dvd_mul_left ⟨-(l.2 * a1), ?_⟩
      rw [pow_one]
      linear_combination e1 + 2 * θ * e2
    have hd : N ∣ (d0 + d1 * θ) - (l.1 + l.2 * θ) * (b0 + b1 * θ) := by
      refine (isCoprime_two_pow θ 1).dvd_of_dvd_mul_left ⟨-(l.2 * b1), ?_⟩
      rw [pow_one]
      linear_combination e3 + 2 * θ * e4
    have hA : N ∣ (2 ^ i + 2 ^ j * (l.1 + l.2 * θ)) * (a0 + a1 * θ) := by
      have e : (2 ^ i + 2 ^ j * (l.1 + l.2 * θ)) * (a0 + a1 * θ) =
          (2 ^ i * (a0 + a1 * θ) + 2 ^ j * (c0 + c1 * θ)) -
            2 ^ j * ((c0 + c1 * θ) - (l.1 + l.2 * θ) * (a0 + a1 * θ)) := by ring
      rw [e]
      exact dvd_sub h1 (dvd_mul_of_dvd_right hc _)
    have hB : N ∣ (2 ^ i + 2 ^ j * (l.1 + l.2 * θ)) * (b0 + b1 * θ) := by
      have e : (2 ^ i + 2 ^ j * (l.1 + l.2 * θ)) * (b0 + b1 * θ) =
          (2 ^ i * (b0 + b1 * θ) + 2 ^ j * (d0 + d1 * θ)) -
            2 ^ j * ((d0 + d1 * θ) - (l.1 + l.2 * θ) * (b0 + b1 * θ)) := by ring
      rw [e]
      exact dvd_sub h2 (dvd_mul_of_dvd_right hd _)
    have hlam : N ∣ 2 ^ i + 2 ^ j * (l.1 + l.2 * θ) := by
      rcases hu with hu | hu
      · exact (isCoprime_of_unitForm hu).symm.dvd_of_dvd_mul_right hA
      · exact (isCoprime_of_unitForm hu).symm.dvd_of_dvd_mul_right hB
    obtain ⟨g, hg, hdg⟩ := exists_dvd_two_pow_add hlam
    exact not_dvd_of_depList ha hg hl hdg

theorem f4_pairOK : ∀ k < Tag.F4.rootCertificate.roots.length,
    ∀ l < Tag.F4.rootCertificate.roots.length,
    0 < height (Tag.F4.rootCertificate.root k) → 0 < height (Tag.F4.rootCertificate.root l) →
    pairOK (∑ j : Fin 4, Tag.F4.cartan (0 : Fin 4) j * Tag.F4.rootCertificate.root k j)
      (∑ j : Fin 4, Tag.F4.cartan (3 : Fin 4) j * Tag.F4.rootCertificate.root k j)
      (∑ j : Fin 4, Tag.F4.cartan (1 : Fin 4) j * Tag.F4.rootCertificate.root k j)
      (∑ j : Fin 4, Tag.F4.cartan (2 : Fin 4) j * Tag.F4.rootCertificate.root k j)
      (∑ j : Fin 4, Tag.F4.cartan (0 : Fin 4) j * Tag.F4.rootCertificate.root l j)
      (∑ j : Fin 4, Tag.F4.cartan (3 : Fin 4) j * Tag.F4.rootCertificate.root l j)
      (∑ j : Fin 4, Tag.F4.cartan (1 : Fin 4) j * Tag.F4.rootCertificate.root l j)
      (∑ j : Fin 4, Tag.F4.cartan (2 : Fin 4) j * Tag.F4.rootCertificate.root l j) = true := by
  decide +kernel

theorem f4_unitOK : ∀ k < Tag.F4.rootCertificate.roots.length,
    0 < height (Tag.F4.rootCertificate.root k) →
    (unitForm (∑ j : Fin 4, Tag.F4.cartan (0 : Fin 4) j * Tag.F4.rootCertificate.root k j)
        (∑ j : Fin 4, Tag.F4.cartan (3 : Fin 4) j * Tag.F4.rootCertificate.root k j) ||
      unitForm (∑ j : Fin 4, Tag.F4.cartan (1 : Fin 4) j * Tag.F4.rootCertificate.root k j)
        (∑ j : Fin 4, Tag.F4.cartan (2 : Fin 4) j * Tag.F4.rootCertificate.root k j)) = true := by
  decide +kernel

theorem f4_torusExp_isCoprime
    (θ : ℤ) {α : Fin F4.tag.rank → ℤ} (hα : IsRoot F4.tag α)
    (hαp : 0 < height α) :
    IsCoprime (torusExp0 θ α) (2 * θ ^ 2 - 1) ∨ IsCoprime (torusExp1 θ α) (2 * θ ^ 2 - 1) := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check F4.tag)).1 hα
  have h := f4_unitOK k hk hαp
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl (isCoprime_of_unitForm h)
  · exact Or.inr (isCoprime_of_unitForm h)

theorem f4_torusExp_pair_not_dvd
    {a : ℕ} (ha : 2 ≤ a) {α β : Fin F4.tag.rank → ℤ}
    (hα : IsRoot F4.tag α) (hαp : 0 < height α) (hβ : IsRoot F4.tag β) (hβp : 0 < height β)
    (i j : ℕ) :
    ¬ ((2 * (2 ^ a : ℤ) ^ 2 - 1) ∣ 2 ^ i * torusExp0 (2 ^ a) α + 2 ^ j * torusExp0 (2 ^ a) β ∧
      (2 * (2 ^ a : ℤ) ^ 2 - 1) ∣
        2 ^ i * torusExp1 (2 ^ a) α + 2 ^ j * torusExp1 (2 ^ a) β) := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check F4.tag)).1 hα
  obtain ⟨l, hl, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check F4.tag)).1 hβ
  exact not_dvd_of_pairOK ha (f4_pairOK k hk l hl hαp hβp) i j

end CFSG.LieType.Ree.LargeReeCover
