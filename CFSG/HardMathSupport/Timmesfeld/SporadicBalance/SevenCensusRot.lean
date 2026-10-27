module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SevenCensus
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SevenCensus

@[expose] def actR : Bool → ℕ × ℕ → ℕ × ℕ
  | false, (a, b) => ((3 * b) % 7, (a + 5 * b) % 7)
  | true, (a, b) => ((6 * a + 5 * b) % 7, (a + b) % 7)

@[expose] def actWR (w : List Bool) (v : ℕ × ℕ) : ℕ × ℕ := w.foldl (fun v i => actR i v) v

@[expose] def wordsR : List ((ℕ × ℕ) × List Bool) :=
  [ ((0, 1), [false]),
    ((0, 2), [false, false, true, false, false, true]),
    ((0, 3), [true, false, true, false]),
    ((0, 4), [false, true, false, true, false, false]),
    ((0, 5), [true, false, false, true, false]),
    ((0, 6), [false, true, true]),
    ((1, 0), []),
    ((1, 1), [false, false, true]),
    ((1, 2), [true, false, false, true, false, false, true, false]),
    ((1, 3), [true, false, true, false, true]),
    ((1, 4), [true, false, false, true, false, false]),
    ((1, 5), [false, false, true, false, true, true, true]),
    ((1, 6), [true, true, true]),
    ((2, 0), [true, false, false, true, true, true]),
    ((2, 1), [true, false, true, false, false]),
    ((2, 2), [true, false, true, false, true, false]),
    ((2, 3), [true, false, false, true, false, false, true, false, true]),
    ((2, 4), [false, true, false, false]),
    ((2, 5), [true, false, false, true, true]),
    ((2, 6), [false, true, true, true]),
    ((3, 0), [true, false, true]),
    ((3, 1), [false, true, false, false, true, true, true]),
    ((3, 2), [false, false, true, false, false, true, true]),
    ((3, 3), [false, true, false]),
    ((3, 4), [true, false]),
    ((3, 5), [false, false]),
    ((3, 6), [false, false, true, false]),
    ((4, 0), [false, true, false, true, false]),
    ((4, 1), [false, false, true, false, true, true]),
    ((4, 2), [false, false, true, true]),
    ((4, 3), [true, false, true, true]),
    ((4, 4), [false, true, false, true, true]),
    ((4, 5), [false, false, true, false, false]),
    ((4, 6), [false, true, false, false, true]),
    ((5, 0), [true, false, false, true]),
    ((5, 1), [false, true]),
    ((5, 2), [true, false, false]),
    ((5, 3), [false, true, false, false, true, true]),
    ((5, 4), [true, false, true, false, true, false, false, true]),
    ((5, 5), [true, false, false, true, false, false, true]),
    ((5, 6), [false, true, false, true]),
    ((6, 0), [true, true]),
    ((6, 1), [true]),
    ((6, 2), [false, false, true, false, true]),
    ((6, 3), [false, false, true, false, false, true, false]),
    ((6, 4), [false, true, false, true, false, false, true]),
    ((6, 5), [true, false, true, false, true, false, false]),
    ((6, 6), [false, false, true, true, true])]

theorem wordsR_cover : (List.range 7).all (fun a => (List.range 7).all fun b =>
    (a == 0 && b == 0) || wordsR.any fun e => e.1 == (a, b) && actWR e.2 (1, 0) == (a, b)) =
      true := by
  decide

theorem exists_wordR {a b : ℕ} (ha : a < 7) (hb : b < 7) (hab : ¬ (a = 0 ∧ b = 0)) :
    ∃ w : List Bool, actWR w (1, 0) = (a, b) := by
  have h := wordsR_cover
  rw [List.all_eq_true] at h
  have h1 := h a (List.mem_range.2 ha)
  rw [List.all_eq_true] at h1
  have h2 := h1 b (List.mem_range.2 hb)
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h2
  rcases h2 with h2 | ⟨e, -, -, he⟩
  · exact absurd h2 hab
  · exact ⟨e.2, he⟩

variable {G : Type*} [Group G]

section ActionR

variable {x y h k : G} (h₁ : x ^ 7 = 1) (h₂ : y ^ 7 = 1) (hc : Commute x y)
  (hhx : h * x * h⁻¹ = y) (hhy : h * y * h⁻¹ = x ^ 3 * y ^ 5)
  (hkx : k * x * k⁻¹ = x ^ 6 * y) (hky : k * y * k⁻¹ = x ^ 5 * y)
include h₁ h₂ hc hhx hhy hkx hky

@[expose] def kOf (h k : G) : Bool → G
  | false => h
  | true => k

@[expose] def gWR (h k : G) : List Bool → G
  | [] => 1
  | i :: w => gWR h k w * kOf h k i

omit h₁ h₂ hc hhx hhy hkx hky in
theorem conj_split (g : G) (a b : ℕ) :
    g * (x ^ a * y ^ b) * g⁻¹ = (g * x * g⁻¹) ^ a * (g * y * g⁻¹) ^ b := by
  rw [conj_pow, conj_pow]
  group

theorem conj_letterR (i : Bool) (a b : ℕ) :
    kOf h k i * (x ^ a * y ^ b) * (kOf h k i)⁻¹ =
      x ^ (actR i (a, b)).1 * y ^ (actR i (a, b)).2 := by
  cases i
  · have e1 : h * x * h⁻¹ = x ^ 0 * y ^ 1 := by rw [pow_zero, one_mul, pow_one, hhx]
    rw [kOf, conj_split, e1, hhy, pw_pow h₁ h₂ hc, pw_pow h₁ h₂ hc, pw_mul h₁ h₂ hc, actR,
      pw_mod h₁ h₂ hc (0 * a + 3 * b)]
    congr 3 <;> ring_nf
  · have e2 : k * y * k⁻¹ = x ^ 5 * y ^ 1 := by rw [pow_one, hky]
    have e1 : k * x * k⁻¹ = x ^ 6 * y ^ 1 := by rw [pow_one, hkx]
    rw [kOf, conj_split, e1, e2, pw_pow h₁ h₂ hc, pw_pow h₁ h₂ hc, pw_mul h₁ h₂ hc, actR,
      pw_mod h₁ h₂ hc (6 * a + 5 * b)]
    congr 3 <;> ring_nf

theorem conj_wordR (w : List Bool) (a b : ℕ) :
    gWR h k w * (x ^ a * y ^ b) * (gWR h k w)⁻¹ =
      x ^ (actWR w (a, b)).1 * y ^ (actWR w (a, b)).2 := by
  induction w generalizing a b with
  | nil => simp [gWR, actWR]
  | cons i w ih =>
    have hact : actWR (i :: w) (a, b) = actWR w (actR i (a, b)) := rfl
    rw [hact, ← ih, ← conj_letterR h₁ h₂ hc hhx hhy hkx hky i a b, gWR]
    group

end ActionR

variable [Finite G]

theorem census_seven_rot (hG : (Nat.card G).factorization 7 = 2) {x y h k : G}
    (h₁ : x ^ 7 = 1) (h1 : x ≠ 1) (hc : x * y = y * x) (hne : ∀ a < 7, y ≠ x ^ a)
    (hhx : h * x * h⁻¹ = y) (hhy : h * y * h⁻¹ = x ^ 3 * y ^ 5)
    (hkx : k * x * k⁻¹ = x ^ 6 * y) (hky : k * y * k⁻¹ = x ^ 5 * y)
    {s : G} (hs : orderOf s = 7) : ∃ g : G, g * s * g⁻¹ = x := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hc' : Commute x y := hc
  have ho₁ : orderOf x = 7 := orderOf_eq_prime h₁ h1
  have h₂ : y ^ 7 = 1 := by rw [← hhx, conj_pow, h₁, mul_one, mul_inv_cancel]
  have ho₂ : orderOf y = 7 := by
    rw [← hhx, ← MulAut.conj_apply, MulEquiv.orderOf_eq, ho₁]
  have hyN : y ∉ Subgroup.zpowers x := by
    intro hm
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hm
    have hn1 : x ^ n = x ^ (n % 7) := by rw [← zpow_mod_orderOf, ho₁]; simp
    have hn' : x ^ n = x ^ ((n % 7).toNat) := by
      rw [hn1, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    exact hne ((n % 7).toNat) (by omega) (by rw [← hn', hn])
  have hd : Subgroup.zpowers y ⊓ Subgroup.zpowers x = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers y ⊓ Subgroup.zpowers x : Subgroup G) ∣ 7 := by
      have := Subgroup.card_dvd_of_le (inf_le_right (a := Subgroup.zpowers y)
        (b := Subgroup.zpowers x))
      rwa [Nat.card_zpowers, ho₁] at this
    rcases (Nat.dvd_prime (by norm_num)).1 hdvd with hd1 | hd7
    · exact Subgroup.eq_bot_of_card_eq _ hd1
    · exfalso
      have hle : (Subgroup.zpowers y ⊓ Subgroup.zpowers x : Subgroup G) =
          Subgroup.zpowers y := by
        refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
        rw [hd7, Nat.card_zpowers, ho₂]
      apply hyN
      have := Subgroup.mem_zpowers y
      rw [← hle] at this
      exact (Subgroup.mem_inf.1 this).2
  have hN : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro z
    have hcy : ∀ n : ℤ, y * x ^ n * y⁻¹ = x ^ n := fun n => by
      rw [(hc'.symm.zpow_right n).eq, mul_inv_cancel_right]
    constructor
    · intro hz
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      rw [hcy]
      exact Subgroup.zpow_mem_zpowers x n
    · intro hz
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hz
      have : z = x ^ n := by
        have := congrArg (fun w => y⁻¹ * w * y) hn
        rw [← hcy n] at this
        simpa [mul_assoc] using this.symm
      rw [this]
      exact Subgroup.zpow_mem_zpowers x n
  have hA := card_sup_of_le_normalizer hN hd
  rw [Nat.card_zpowers, Nat.card_zpowers, ho₁, ho₂] at hA
  set A := Subgroup.zpowers y ⊔ Subgroup.zpowers x with hAdef
  have hAset := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN
  let P : Sylow 7 G := Sylow.ofCard A (by rw [hA, hG]; norm_num)
  have hsz : IsPGroup 7 (Subgroup.zpowers s) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨Q, hQ⟩ := hsz.exists_le_sylow
  obtain ⟨m₀, hm₀⟩ := MulAction.exists_smul_eq G P Q
  have hsQ : s ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers s)
  rw [← hm₀, Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at hsQ
  obtain ⟨t, htA, hts⟩ := (Subgroup.mem_smul_pointwise_iff_exists s (MulAut.conj m₀) A).1 hsQ
  rw [MulAut.smul_def, MulAut.conj_apply] at hts
  suffices ht : ∃ g : G, g * t * g⁻¹ = x by
    obtain ⟨g, hg⟩ := ht
    refine ⟨g * m₀⁻¹, ?_⟩
    rw [← hts, ← hg]
    group
  have hto : t ≠ 1 := by
    rintro rfl
    rw [mul_one, mul_inv_cancel] at hts
    rw [← hts, orderOf_one] at hs
    norm_num at hs
  rw [← SetLike.mem_coe, hAset] at htA
  obtain ⟨u, hu, v, hv, rfl⟩ := htA
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
  have hz : ∀ (z : G) (n : ℤ), orderOf z = 7 → z ^ n = z ^ (n % 7).toNat := by
    intro z n hzo
    have hz1 : z ^ n = z ^ (n % 7) := by rw [← zpow_mod_orderOf, hzo]; simp
    rw [hz1, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
  set a := (i % 7).toNat with ha
  set b := (j % 7).toNat with hb
  have hform : y ^ j * x ^ i = x ^ a * y ^ b := by
    rw [hz y j ho₂, hz x i ho₁, ((hc'.pow_pow a b).eq).symm]
  have hto' : y ^ j * x ^ i ≠ 1 := hto
  change ∃ g : G, g * (y ^ j * x ^ i) * g⁻¹ = x
  rw [hform] at hto' ⊢
  have ha7 : a < 7 := by omega
  have hb7 : b < 7 := by omega
  have hab : ¬ (a = 0 ∧ b = 0) := by
    rintro ⟨h0, h0'⟩
    rw [h0, h0', pow_zero, pow_zero, one_mul] at hto'
    exact hto' rfl
  obtain ⟨w, hw⟩ := exists_wordR ha7 hb7 hab
  have hwc := conj_wordR h₁ h₂ hc' hhx hhy hkx hky w 1 0
  rw [hw, pow_one, pow_zero, mul_one] at hwc
  refine ⟨(gWR h k w)⁻¹, ?_⟩
  rw [← hwc]
  group

theorem ne_of_card_rot {x y h : G} (h₁ : x ^ 7 = 1)
    (hcard : Nat.card (Subgroup.closure ({x, y} : Set G)) = 7 ^ 2) (hhx : h * x * h⁻¹ = y) :
    x ≠ 1 ∧ ∀ a < 7, y ≠ x ^ a := by
  have h₂ : y ^ 7 = 1 := by rw [← hhx, conj_pow, h₁, mul_one, mul_inv_cancel]
  have hle : ∀ z : G, z ^ 7 = 1 → Subgroup.closure ({x, y} : Set G) ≤ Subgroup.zpowers z →
      False := by
    intro z hz hsub
    have h1 := Subgroup.card_le_of_le hsub
    have h2 : Nat.card (Subgroup.zpowers z) ≤ 7 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hz)
    rw [hcard] at h1
    omega
  have hx1 : x ≠ 1 := by
    rintro rfl
    refine hle y h₂ ?_
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers z
  have hne : ∀ a < 7, y ≠ x ^ a := by
    rintro a - rfl
    refine hle x h₁ ?_
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact Subgroup.mem_zpowers z
    · exact Subgroup.npow_mem_zpowers x a
  exact ⟨hx1, hne⟩

theorem census_seven_rot_of_card (hG : (Nat.card G).factorization 7 = 2) {x y h k : G}
    (h₁ : x ^ 7 = 1) (hc : x * y = y * x)
    (hcard : Nat.card (Subgroup.closure ({x, y} : Set G)) = 7 ^ 2)
    (hhx : h * x * h⁻¹ = y) (hhy : h * y * h⁻¹ = x ^ 3 * y ^ 5)
    (hkx : k * x * k⁻¹ = x ^ 6 * y) (hky : k * y * k⁻¹ = x ^ 5 * y)
    {s : G} (hs : orderOf s = 7) : ∃ g : G, g * s * g⁻¹ = x :=
  census_seven_rot hG h₁ (ne_of_card_rot h₁ hcard hhx).1 hc (ne_of_card_rot h₁ hcard hhx).2 hhx
    hhy hkx hky hs

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SevenCensus
