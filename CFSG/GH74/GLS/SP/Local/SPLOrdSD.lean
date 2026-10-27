module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.LinearCombination

public section

open Subgroup DihedralGroup

namespace CFSG.GH74.GLS.SP.Local

variable {I : Type} [Group I]

@[expose] def par {d : ℕ} (hd : 2 ∣ d) (i : ZMod d) : ℕ := (ZMod.castHom hd (ZMod 2) i).val

private noncomputable def sgm (σ : MulAut I) (x : ZMod 2) : MulAut I := σ ^ x.val

private lemma sgm_add (σ : MulAut I) (hσ : σ * σ = 1) (x y : ZMod 2) :
    sgm σ (x + y) = sgm σ x * sgm σ y := by
  have h : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h x with rfl | rfl <;> rcases h y with rfl | rfl
  · simp [sgm]
  · simp [sgm]
  · simp [sgm]
  · have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have hv0 : (0 : ZMod 2).val = 0 := rfl
    have hv1 : (1 : ZMod 2).val = 1 := rfl
    rw [h11]
    simp only [sgm, hv0, hv1, pow_zero, pow_one]
    exact hσ.symm

@[expose] noncomputable def dihAct (σ : MulAut I) (hσ : σ * σ = 1) {d : ℕ} [NeZero d]
    (hd : 2 ∣ d) : DihedralGroup d →* MulAut I where
  toFun g := match g with
    | r k => σ ^ par hd k
    | sr k => σ ^ par hd k
  map_one' := by
    show σ ^ par hd 0 = 1
    simp [par]
  map_mul' := by
    intro a b
    have hp : ∀ x y : ZMod d, σ ^ par hd (x + y) = σ ^ par hd x * σ ^ par hd y := by
      intro x y
      have h2 : ZMod.castHom hd (ZMod 2) (x + y) =
          ZMod.castHom hd (ZMod 2) x + ZMod.castHom hd (ZMod 2) y := map_add _ _ _
      have := sgm_add σ hσ (ZMod.castHom hd (ZMod 2) x) (ZMod.castHom hd (ZMod 2) y)
      rw [← h2] at this
      exact this
    have hm : ∀ x y : ZMod d, σ ^ par hd (x - y) = σ ^ par hd y * σ ^ par hd x := by
      intro x y
      have h2 : ZMod.castHom hd (ZMod 2) (x - y) =
          ZMod.castHom hd (ZMod 2) y + ZMod.castHom hd (ZMod 2) x := by
        rw [map_sub, sub_eq_add_neg, ZMod.neg_eq_self_mod_two, add_comm]
      have := sgm_add σ hσ (ZMod.castHom hd (ZMod 2) y) (ZMod.castHom hd (ZMod 2) x)
      rw [← h2] at this
      exact this
    rcases a with i | i <;> rcases b with j | j
    · exact hp i j
    · exact hm j i
    · exact hp i j
    · exact hm j i

theorem dihAct_r (σ : MulAut I) (hσ : σ * σ = 1) {d : ℕ} [NeZero d] (hd : 2 ∣ d) (k : ZMod d) :
    dihAct σ hσ hd (r k) = σ ^ par hd k := rfl

theorem dihAct_sr (σ : MulAut I) (hσ : σ * σ = 1) {d : ℕ} [NeZero d] (hd : 2 ∣ d) (k : ZMod d) :
    dihAct σ hσ hd (sr k) = σ ^ par hd k := rfl

@[expose] def Z0 (σ : MulAut I) (hσ : σ * σ = 1) {d : ℕ} [NeZero d] (hd : 2 ∣ d) :
    Set (I ⋊[dihAct σ hσ hd] DihedralGroup d) :=
  {x | (∃ k : ZMod d, par hd k = 0 ∧ x = ⟨1, sr k⟩) ∨
    (∃ i : I, i ≠ 1 ∧ i * i = 1 ∧ x = ⟨i, r ((d / 2 : ℕ) : ZMod d)⟩)}

@[expose] def tSD (σ : MulAut I) (hσ : σ * σ = 1) {d : ℕ} [NeZero d] (hd : 2 ∣ d) :
    I ⋊[dihAct σ hσ hd] DihedralGroup d := ⟨1, r ((d / 2 : ℕ) : ZMod d)⟩

private lemma par_eq_val_mod {d : ℕ} [NeZero d] (hd : 2 ∣ d) (k : ZMod d) :
    par hd k = k.val % 2 := by
  conv_lhs => rw [← ZMod.natCast_zmod_val k]
  unfold par
  rw [map_natCast, ZMod.val_natCast]

private lemma par_zero {d : ℕ} [NeZero d] (hd : 2 ∣ d) : par hd 0 = 0 := by
  simp [par]

private lemma par_eq_zero_iff' {d : ℕ} (hd : 2 ∣ d) (k : ZMod d) :
    par hd k = 0 ↔ ZMod.castHom hd (ZMod 2) k = 0 := ZMod.val_eq_zero _

private lemma par_eq_one_iff' {d : ℕ} (hd : 2 ∣ d) (k : ZMod d) :
    par hd k = 1 ↔ ZMod.castHom hd (ZMod 2) k = 1 := ZMod.val_eq_one (by norm_num) _

private lemma par_cases {d : ℕ} [NeZero d] (hd : 2 ∣ d) (k : ZMod d) :
    par hd k = 0 ∨ par hd k = 1 := by
  rw [par_eq_val_mod]
  omega

private lemma par_sub_zero_zero {d : ℕ} (hd : 2 ∣ d) {a b : ZMod d} (ha : par hd a = 0)
    (hb : par hd b = 0) : par hd (a - b) = 0 := by
  rw [par_eq_zero_iff'] at ha hb ⊢
  rw [map_sub, ha, hb, sub_zero]

private lemma par_sub_zero_one {d : ℕ} (hd : 2 ∣ d) {a b : ZMod d} (ha : par hd a = 0)
    (hb : par hd b = 1) : par hd (a - b) = 1 := by
  rw [par_eq_zero_iff'] at ha
  rw [par_eq_one_iff'] at hb ⊢
  rw [map_sub, ha, hb]
  decide

private lemma two_mul_half {d : ℕ} (hd : 2 ∣ d) : 2 * (d / 2) = d := Nat.mul_div_cancel' hd

private lemma delta_add_delta {d : ℕ} (hd : 2 ∣ d) :
    (((d / 2 : ℕ) : ZMod d) + ((d / 2 : ℕ) : ZMod d)) = 0 := by
  have h : d / 2 + d / 2 = d := by omega
  rw [← Nat.cast_add, h, ZMod.natCast_self]

private lemma delta_ne_zero {d : ℕ} [NeZero d] (hd : 2 ∣ d) : ((d / 2 : ℕ) : ZMod d) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hpos := NeZero.pos d
  have := Nat.le_of_dvd (by omega) h
  omega

private lemma par_delta {d : ℕ} [NeZero d] (hd : 2 ∣ d) (h4 : 4 ∣ d) :
    par hd ((d / 2 : ℕ) : ZMod d) = 0 := by
  have hpos := NeZero.pos d
  have h : d / 2 % d = d / 2 := Nat.mod_eq_of_lt (by omega)
  rw [par_eq_val_mod, ZMod.val_natCast, h]
  omega

private lemma eq_zero_or_delta_of_add_self {d : ℕ} [NeZero d] (hd : 2 ∣ d) (x : ZMod d)
    (hx : x + x = 0) : x = 0 ∨ x = ((d / 2 : ℕ) : ZMod d) := by
  have hc : x.val < d := ZMod.val_lt x
  have hx' : ((x.val + x.val : ℕ) : ZMod d) = 0 := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val]
    exact hx
  rw [ZMod.natCast_eq_zero_iff] at hx'
  obtain ⟨s, hs⟩ := hx'
  have hs2 : s < 2 := by
    by_contra hcon
    have h2 : d * 2 ≤ d * s := Nat.mul_le_mul_left d (by omega)
    omega
  have hxv : x = (x.val : ZMod d) := (ZMod.natCast_zmod_val x).symm
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
  · left
    have : x.val = 0 := by omega
    rw [hxv, this, Nat.cast_zero]
  · right
    have : x.val = d / 2 := by omega
    rw [hxv, this]

private lemma delta_mul_odd {d : ℕ} [NeZero d] (hd : 2 ∣ d) (n : ℕ) (hn : n % 2 = 1) :
    ((d / 2 : ℕ) : ZMod d) * (n : ZMod d) = ((d / 2 : ℕ) : ZMod d) := by
  rw [← Nat.cast_mul]
  have hn' : n = 2 * (n / 2) + 1 := by omega
  have h : d / 2 * n = d * (n / 2) + d / 2 := by
    calc d / 2 * n = d / 2 * (2 * (n / 2) + 1) := by rw [← hn']
      _ = (2 * (d / 2)) * (n / 2) + d / 2 := by ring
      _ = d * (n / 2) + d / 2 := by rw [two_mul_half hd]
  rw [h, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add]

private lemma delta_mul_even {d : ℕ} [NeZero d] (hd : 2 ∣ d) (n : ℕ) (hn : n % 2 = 0) :
    ((d / 2 : ℕ) : ZMod d) * (n : ZMod d) = 0 := by
  rw [← Nat.cast_mul]
  have hn' : n = 2 * (n / 2) := by omega
  have h : d / 2 * n = d * (n / 2) := by
    calc d / 2 * n = d / 2 * (2 * (n / 2)) := by rw [← hn']
      _ = (2 * (d / 2)) * (n / 2) := by ring
      _ = d * (n / 2) := by rw [two_mul_half hd]
  rw [h, Nat.cast_mul, ZMod.natCast_self, zero_mul]

private abbrev SDP (σ : MulAut I) (hσ : σ * σ = 1) {d : ℕ} [NeZero d] (hd : 2 ∣ d) : Type :=
  I ⋊[dihAct σ hσ hd] DihedralGroup d

private instance instFiniteSDP [Finite I] (σ : MulAut I) (hσ : σ * σ = 1) {d : ℕ} [NeZero d]
    (hd : 2 ∣ d) : Finite (SDP σ hσ hd) :=
  Finite.of_equiv (I × DihedralGroup d) SemidirectProduct.equivProd.symm

private lemma sr_ne_one {d : ℕ} (x : ZMod d) : (sr x : DihedralGroup d) ≠ 1 := by
  rw [← r_zero]
  intro h
  cases h

section SD

variable (σ : MulAut I) (hσ : σ * σ = 1) {d : ℕ} [NeZero d] (hd : 2 ∣ d)

private lemma act_r_zero {k : ZMod d} (hk : par hd k = 0) : dihAct σ hσ hd (r k) = 1 := by
  rw [dihAct_r, hk, pow_zero]

private lemma act_sr_zero {k : ZMod d} (hk : par hd k = 0) : dihAct σ hσ hd (sr k) = 1 := by
  rw [dihAct_sr, hk, pow_zero]

private lemma act_r_one {k : ZMod d} (hk : par hd k = 1) : dihAct σ hσ hd (r k) = σ := by
  rw [dihAct_r, hk, pow_one]

private lemma act_sr_one {k : ZMod d} (hk : par hd k = 1) : dihAct σ hσ hd (sr k) = σ := by
  rw [dihAct_sr, hk, pow_one]

private lemma mk_mul_mk (i j : I) (g h : DihedralGroup d) :
    (⟨i, g⟩ : SDP σ hσ hd) * ⟨j, h⟩ = ⟨i * dihAct σ hσ hd g j, g * h⟩ := rfl

private lemma mk_pow_of_act_one (i : I) (g : DihedralGroup d) (h : dihAct σ hσ hd g = 1)
    (n : ℕ) : (⟨i, g⟩ : SDP σ hσ hd) ^ n = ⟨i ^ n, g ^ n⟩ := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, pow_zero]
    rfl
  | succ n ih =>
    rw [pow_succ, ih, pow_succ, pow_succ, mk_mul_mk, map_pow, h, one_pow]
    rfl

private lemma mk_sq (i : I) (g : DihedralGroup d) :
    (⟨i, g⟩ : SDP σ hσ hd) ^ 2 = ⟨i * dihAct σ hσ hd g i, g * g⟩ := by
  rw [pow_two]
  rfl

private lemma orderOf_mk_eq_two_iff (i : I) (g : DihedralGroup d) :
    orderOf (⟨i, g⟩ : SDP σ hσ hd) = 2 ↔
      (i * dihAct σ hσ hd g i = 1 ∧ g * g = 1) ∧ ¬ (i = 1 ∧ g = 1) := by
  rw [orderOf_eq_prime_iff, mk_sq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨congrArg SemidirectProduct.left h1, congrArg SemidirectProduct.right h1⟩,
      fun ⟨hi, hg⟩ => h2 ?_⟩
    rw [hi, hg]
    rfl
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨SemidirectProduct.ext h1 h2, fun h => h3 ?_⟩
    exact ⟨congrArg SemidirectProduct.left h, congrArg SemidirectProduct.right h⟩

private lemma mem_zpowers_iff_pow {G : Type*} [Group G] [Finite G] (x y : G) :
    y ∈ zpowers x ↔ ∃ n : ℕ, x ^ n = y := by
  rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff]

private lemma pow_eq_one_or_self {G : Type*} [Group G] {y : G} (h : y * y = 1) (n : ℕ) :
    y ^ n = 1 ∨ y ^ n = y := by
  induction n with
  | zero => exact Or.inl (pow_zero y)
  | succ n ih =>
    rcases ih with h1 | h1
    · right
      rw [pow_succ, h1, one_mul]
    · left
      rw [pow_succ, h1, h]

private lemma tSD_notMem_zpowers [Finite I] (x : SDP σ hσ hd) (h2 : x.right * x.right = 1)
    (hne : x.right ≠ r ((d / 2 : ℕ) : ZMod d)) : tSD σ hσ hd ∉ zpowers x := by
  intro hmem
  rw [mem_zpowers_iff_pow] at hmem
  obtain ⟨n, hn⟩ := hmem
  have h1 : (x ^ n).right = x.right ^ n :=
    map_pow (SemidirectProduct.rightHom : SDP σ hσ hd →* DihedralGroup d) x n
  have hr : x.right ^ n = r ((d / 2 : ℕ) : ZMod d) := by
    rw [← h1, hn]
    rfl
  rcases pow_eq_one_or_self h2 n with h3 | h3
  · rw [h3, ← r_zero] at hr
    exact delta_ne_zero hd (r.inj hr).symm
  · rw [h3] at hr
    exact hne hr

private lemma tSD_notMem_of_right_sr [Finite I] (x : SDP σ hσ hd) (c : ZMod d)
    (hx : x.right = sr c) : tSD σ hσ hd ∉ zpowers x :=
  tSD_notMem_zpowers σ hσ hd x (by rw [hx]; exact sr_mul_self c)
    (by rw [hx]; intro h; cases h)

private lemma tSD_notMem_of_right_one [Finite I] (x : SDP σ hσ hd) (hx : x.right = 1) :
    tSD σ hσ hd ∉ zpowers x :=
  tSD_notMem_zpowers σ hσ hd x (by rw [hx, mul_one]) (by
    rw [hx, ← r_zero]
    intro h
    exact delta_ne_zero hd (r.inj h).symm)

private lemma mul_self_eq_one_of_orderOf_two {G : Type*} [Group G] {i : G}
    (hi : orderOf i = 2) : i * i = 1 := by
  have := pow_orderOf_eq_one i
  rwa [hi, pow_two] at this

private lemma ne_one_of_orderOf_two {G : Type*} [Group G] {i : G} (hi : orderOf i = 2) :
    i ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at hi
  exact absurd hi (by norm_num)

private lemma orderOf_two_of {G : Type*} [Group G] {i : G} (h1 : i ≠ 1) (h2 : i * i = 1) :
    orderOf i = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact h2) h1

private lemma shapeA [Finite I] (k j : ZMod d) (i : I) (hk : par hd k = 0)
    (hj : par hd j = 0) (hcond : ∃ n : ℕ, Even n ∧ (n : ZMod d) * j = ((d / 2 : ℕ) : ZMod d))
    (hi : orderOf i = 2) :
    orderOf (⟨i, sr (k - j)⟩ : SDP σ hσ hd) = 2 ∧ (⟨i, sr (k - j)⟩ : SDP σ hσ hd) ∉ Z0 σ hσ hd ∧
      (⟨1, sr k⟩ : SDP σ hσ hd) ∈ Z0 σ hσ hd ∧
      tSD σ hσ hd ∈ zpowers ((⟨i, sr (k - j)⟩ : SDP σ hσ hd) * ⟨1, sr k⟩) := by
  have hkj : par hd (k - j) = 0 := par_sub_zero_zero hd hk hj
  have hi1 : i ≠ 1 := ne_one_of_orderOf_two hi
  have hi2 : i * i = 1 := mul_self_eq_one_of_orderOf_two hi
  refine ⟨?_, ?_, Or.inl ⟨k, hk, rfl⟩, ?_⟩
  · rw [orderOf_mk_eq_two_iff]
    refine ⟨⟨?_, sr_mul_self _⟩, ?_⟩
    · rw [act_sr_zero σ hσ hd hkj]
      exact hi2
    · rintro ⟨_, h⟩
      exact sr_ne_one _ h
  · rintro (⟨k', hk', h⟩ | ⟨i', hi'1, hi'2, h⟩)
    · exact hi1 (congrArg SemidirectProduct.left h)
    · cases (congrArg SemidirectProduct.right h)
  · have hab : (⟨i, sr (k - j)⟩ : SDP σ hσ hd) * ⟨1, sr k⟩ = ⟨i, r j⟩ := by
      refine SemidirectProduct.ext ?_ ?_
      · show i * (dihAct σ hσ hd (sr (k - j))) 1 = i
        rw [act_sr_zero σ hσ hd hkj]
        simp
      · show sr (k - j) * sr k = r j
        rw [sr_mul_sr, sub_sub_cancel]
    rw [hab, mem_zpowers_iff_pow]
    obtain ⟨n, hn, hnj⟩ := hcond
    refine ⟨n, ?_⟩
    rw [mk_pow_of_act_one σ hσ hd i (r j) (act_r_zero σ hσ hd hj) n]
    have hin : i ^ n = 1 := by
      obtain ⟨m, rfl⟩ := hn
      rw [← two_mul, pow_mul, pow_two, hi2, one_pow]
    rw [r_pow, mul_comm j n, hnj, hin]
    rfl

private lemma shapeB [Finite I] (h4 : 4 ∣ d) (k m : ZMod d) (i : I) (hk : par hd k = 0)
    (hm : par hd m = 1) (hi : i * σ i = 1) :
    orderOf (⟨i, sr m⟩ : SDP σ hσ hd) = 2 ∧ (⟨i, sr m⟩ : SDP σ hσ hd) ∉ Z0 σ hσ hd ∧
      (⟨1, sr k⟩ : SDP σ hσ hd) ∈ Z0 σ hσ hd ∧
      tSD σ hσ hd ∈ zpowers ((⟨i, sr m⟩ : SDP σ hσ hd) * ⟨1, sr k⟩) := by
  refine ⟨?_, ?_, Or.inl ⟨k, hk, rfl⟩, ?_⟩
  · rw [orderOf_mk_eq_two_iff]
    refine ⟨⟨?_, sr_mul_self _⟩, ?_⟩
    · rw [act_sr_one σ hσ hd hm]
      exact hi
    · rintro ⟨_, h⟩
      exact sr_ne_one _ h
  · rintro (⟨k', hk', h⟩ | ⟨i', hi'1, hi'2, h⟩)
    · have hmk : m = k' := sr.inj (congrArg SemidirectProduct.right h)
      rw [hmk, hk'] at hm
      exact absurd hm (by norm_num)
    · cases (congrArg SemidirectProduct.right h)
  · have hkm : par hd (k - m) = 1 := par_sub_zero_one hd hk hm
    have hab : (⟨i, sr m⟩ : SDP σ hσ hd) * ⟨1, sr k⟩ = ⟨i, r (k - m)⟩ := by
      refine SemidirectProduct.ext ?_ ?_
      · show i * (dihAct σ hσ hd (sr m)) 1 = i
        rw [act_sr_one σ hσ hd hm]
        simp
      · show sr m * sr k = r (k - m)
        rw [sr_mul_sr]
    have hx2 : (⟨i, r (k - m)⟩ : SDP σ hσ hd) ^ 2 =
        SemidirectProduct.inr (r ((k - m) + (k - m))) := by
      rw [mk_sq, act_r_one σ hσ hd hkm]
      refine SemidirectProduct.ext ?_ ?_
      · show i * σ i = 1
        exact hi
      · show r (k - m) * r (k - m) = r ((k - m) + (k - m))
        rw [r_mul_r]
    have hu : d / 2 = 2 * (d / 4) := by omega
    rw [hab, mem_zpowers_iff_pow]
    refine ⟨d / 2, ?_⟩
    rw [hu, pow_mul, hx2, ← map_pow, r_pow]
    have hval : ((k - m + (k - m)) * ((d / 4 : ℕ) : ZMod d)) = ((d / 2 : ℕ) : ZMod d) := by
      have h1 : (k - m + (k - m)) * ((d / 4 : ℕ) : ZMod d) =
          (k - m) * ((2 * (d / 4) : ℕ) : ZMod d) := by
        push_cast
        ring
      rw [h1, ← hu, mul_comm]
      have h2 := delta_mul_odd hd (k - m).val ((par_eq_val_mod hd (k - m)).symm.trans hkm)
      rw [ZMod.natCast_zmod_val] at h2
      exact h2
    rw [hval]
    rfl

private lemma shapeC [Finite I] (h4 : 4 ∣ d) (i i₀ : I) (hi : orderOf i = 2)
    (hi₀ : orderOf i₀ = 2) (hodd : Odd (orderOf (i * i₀))) :
    orderOf (⟨i, 1⟩ : SDP σ hσ hd) = 2 ∧ (⟨i, 1⟩ : SDP σ hσ hd) ∉ Z0 σ hσ hd ∧
      (⟨i₀, r ((d / 2 : ℕ) : ZMod d)⟩ : SDP σ hσ hd) ∈ Z0 σ hσ hd ∧
      tSD σ hσ hd ∈ zpowers ((⟨i, 1⟩ : SDP σ hσ hd) * ⟨i₀, r ((d / 2 : ℕ) : ZMod d)⟩) := by
  have hi1 : i ≠ 1 := ne_one_of_orderOf_two hi
  have hi₀1 : i₀ ≠ 1 := ne_one_of_orderOf_two hi₀
  have hi2 : i * i = 1 := mul_self_eq_one_of_orderOf_two hi
  have hi₀2 : i₀ * i₀ = 1 := mul_self_eq_one_of_orderOf_two hi₀
  have hpδ := par_delta hd h4
  refine ⟨?_, ?_, Or.inr ⟨i₀, hi₀1, hi₀2, rfl⟩, ?_⟩
  · rw [orderOf_mk_eq_two_iff]
    refine ⟨⟨?_, mul_one 1⟩, ?_⟩
    · rw [map_one]
      exact hi2
    · rintro ⟨h, _⟩
      exact hi1 h
  · rintro (⟨k', hk', h⟩ | ⟨i', hi'1, hi'2, h⟩)
    · exact sr_ne_one k' (congrArg SemidirectProduct.right h).symm
    · have h' : (1 : DihedralGroup d) = r ((d / 2 : ℕ) : ZMod d) :=
        congrArg SemidirectProduct.right h
      rw [← r_zero] at h'
      exact delta_ne_zero hd (r.inj h').symm
  · have hab : (⟨i, 1⟩ : SDP σ hσ hd) * ⟨i₀, r ((d / 2 : ℕ) : ZMod d)⟩ =
        ⟨i * i₀, r ((d / 2 : ℕ) : ZMod d)⟩ := by
      refine SemidirectProduct.ext ?_ ?_
      · show i * (dihAct σ hσ hd 1) i₀ = i * i₀
        rw [map_one]
        rfl
      · show 1 * r ((d / 2 : ℕ) : ZMod d) = r ((d / 2 : ℕ) : ZMod d)
        rw [one_mul]
    rw [hab, mem_zpowers_iff_pow]
    refine ⟨orderOf (i * i₀), ?_⟩
    rw [mk_pow_of_act_one σ hσ hd _ _ (act_r_zero σ hσ hd hpδ), pow_orderOf_eq_one, r_pow]
    have ho : orderOf (i * i₀) % 2 = 1 := Nat.odd_iff.mp hodd
    rw [delta_mul_odd hd _ ho]
    rfl

private lemma sp_cases [Finite I] (h4 : 4 ∣ d) (a b : SDP σ hσ hd) (ha : orderOf a = 2)
    (haZ : a ∉ Z0 σ hσ hd) (hb : b ∈ Z0 σ hσ hd) (ht : tSD σ hσ hd ∈ zpowers (a * b)) :
    (∃ (k j : ZMod d) (i : I), par hd k = 0 ∧ par hd j = 0 ∧
        (∃ n : ℕ, Even n ∧ (n : ZMod d) * j = ((d / 2 : ℕ) : ZMod d)) ∧ orderOf i = 2 ∧
        a = ⟨i, sr (k - j)⟩ ∧ b = ⟨1, sr k⟩) ∨
    (∃ (k m : ZMod d) (i : I), par hd k = 0 ∧ par hd m = 1 ∧ i * σ i = 1 ∧
        a = ⟨i, sr m⟩ ∧ b = ⟨1, sr k⟩) ∨
    (∃ i i₀ : I, orderOf i = 2 ∧ orderOf i₀ = 2 ∧ Odd (orderOf (i * i₀)) ∧
        a = ⟨i, 1⟩ ∧ b = ⟨i₀, r ((d / 2 : ℕ) : ZMod d)⟩) := by
  obtain ⟨i, g⟩ := a
  rw [orderOf_mk_eq_two_iff] at ha
  obtain ⟨⟨hsq1, hsq2⟩, hne⟩ := ha
  have hpδ := par_delta hd h4
  rcases hb with ⟨k, hk, rfl⟩ | ⟨i₀, hi₀1, hi₀2, rfl⟩
  · rcases g with m | m
    · have hm2 : m + m = 0 := by
        have h' : r (m + m) = (r 0 : DihedralGroup d) := by
          rw [← r_mul_r, r_zero]
          exact hsq2
        exact r.inj h'
      rcases eq_zero_or_delta_of_add_self hd m hm2 with rfl | rfl
      · exfalso
        refine tSD_notMem_of_right_sr σ hσ hd _ (k - 0) ?_ ht
        show r 0 * sr k = sr (k - 0)
        rw [r_mul_sr]
      · exfalso
        have hii : i * i = 1 := by
          rw [act_r_zero σ hσ hd hpδ] at hsq1
          exact hsq1
        have hi1 : i = 1 := by
          by_contra hne1
          exact haZ (Or.inr ⟨i, hne1, hii, rfl⟩)
        subst hi1
        refine tSD_notMem_of_right_sr σ hσ hd _ (k - ((d / 2 : ℕ) : ZMod d)) ?_ ht
        show r ((d / 2 : ℕ) : ZMod d) * sr k = sr (k - ((d / 2 : ℕ) : ZMod d))
        rw [r_mul_sr]
    · rcases par_cases hd m with hm0 | hm1
      · left
        have hii : i * i = 1 := by
          rw [act_sr_zero σ hσ hd hm0] at hsq1
          exact hsq1
        have hi1 : i ≠ 1 := by
          rintro rfl
          exact haZ (Or.inl ⟨m, hm0, rfl⟩)
        have hord : orderOf i = 2 := orderOf_two_of hi1 hii
        have hkm0 : par hd (k - m) = 0 := par_sub_zero_zero hd hk hm0
        refine ⟨k, k - m, i, hk, hkm0, ?_, hord, ?_, rfl⟩
        · have hab : (⟨i, sr m⟩ : SDP σ hσ hd) * ⟨1, sr k⟩ = ⟨i, r (k - m)⟩ := by
            refine SemidirectProduct.ext ?_ ?_
            · show i * (dihAct σ hσ hd (sr m)) 1 = i
              rw [act_sr_zero σ hσ hd hm0]
              simp
            · show sr m * sr k = r (k - m)
              rw [sr_mul_sr]
          rw [hab, mem_zpowers_iff_pow] at ht
          obtain ⟨n, hn⟩ := ht
          rw [mk_pow_of_act_one σ hσ hd i (r (k - m)) (act_r_zero σ hσ hd hkm0) n] at hn
          have hn1 : i ^ n = 1 := congrArg SemidirectProduct.left hn
          have hn2 : r ((k - m) * (n : ZMod d)) = r ((d / 2 : ℕ) : ZMod d) := by
            rw [← r_pow]
            exact congrArg SemidirectProduct.right hn
          refine ⟨n, ?_, ?_⟩
          · rw [even_iff_two_dvd, ← hord]
            exact orderOf_dvd_of_pow_eq_one hn1
          · rw [mul_comm]
            exact r.inj hn2
        · rw [sub_sub_cancel]
      · right
        left
        have hii : i * σ i = 1 := by
          rw [act_sr_one σ hσ hd hm1] at hsq1
          exact hsq1
        exact ⟨k, m, i, hk, hm1, hii, rfl, rfl⟩
  · rcases g with m | m
    · have hm2 : m + m = 0 := by
        have h' : r (m + m) = (r 0 : DihedralGroup d) := by
          rw [← r_mul_r, r_zero]
          exact hsq2
        exact r.inj h'
      rcases eq_zero_or_delta_of_add_self hd m hm2 with rfl | rfl
      · right
        right
        have hii : i * i = 1 := by
          rw [act_r_zero σ hσ hd (par_zero hd)] at hsq1
          exact hsq1
        have hi1 : i ≠ 1 := by
          rintro rfl
          exact hne ⟨rfl, r_zero⟩
        have hord : orderOf i = 2 := orderOf_two_of hi1 hii
        have hord₀ : orderOf i₀ = 2 := orderOf_two_of hi₀1 hi₀2
        refine ⟨i, i₀, hord, hord₀, ?_, rfl, rfl⟩
        have hab : (⟨i, r 0⟩ : SDP σ hσ hd) * ⟨i₀, r ((d / 2 : ℕ) : ZMod d)⟩ =
            ⟨i * i₀, r ((d / 2 : ℕ) : ZMod d)⟩ := by
          refine SemidirectProduct.ext ?_ ?_
          · show i * (dihAct σ hσ hd (r 0)) i₀ = i * i₀
            rw [act_r_zero σ hσ hd (par_zero hd)]
            rfl
          · show r 0 * r ((d / 2 : ℕ) : ZMod d) = r ((d / 2 : ℕ) : ZMod d)
            rw [r_mul_r, zero_add]
        rw [hab, mem_zpowers_iff_pow] at ht
        obtain ⟨n, hn⟩ := ht
        rw [mk_pow_of_act_one σ hσ hd _ _ (act_r_zero σ hσ hd hpδ) n] at hn
        have hn1 : (i * i₀) ^ n = 1 := congrArg SemidirectProduct.left hn
        have hn2 : r (((d / 2 : ℕ) : ZMod d) * (n : ZMod d)) = r ((d / 2 : ℕ) : ZMod d) := by
          rw [← r_pow]
          exact congrArg SemidirectProduct.right hn
        have hnodd : n % 2 = 1 := by
          by_contra hcon
          have h0 := delta_mul_even hd n (by omega)
          have h3 : ((d / 2 : ℕ) : ZMod d) * (n : ZMod d) = ((d / 2 : ℕ) : ZMod d) := r.inj hn2
          rw [h0] at h3
          exact delta_ne_zero hd h3.symm
        exact Odd.of_dvd_nat (Nat.odd_iff.mpr hnodd) (orderOf_dvd_of_pow_eq_one hn1)
      · exfalso
        have hii : i * i = 1 := by
          rw [act_r_zero σ hσ hd hpδ] at hsq1
          exact hsq1
        have hi1 : i = 1 := by
          by_contra hne1
          exact haZ (Or.inr ⟨i, hne1, hii, rfl⟩)
        subst hi1
        refine tSD_notMem_of_right_one σ hσ hd _ ?_ ht
        show r ((d / 2 : ℕ) : ZMod d) * r ((d / 2 : ℕ) : ZMod d) = 1
        rw [r_mul_r, delta_add_delta hd, r_zero]
    · exfalso
      refine tSD_notMem_of_right_sr σ hσ hd _ (m + ((d / 2 : ℕ) : ZMod d)) ?_ ht
      show sr m * r ((d / 2 : ℕ) : ZMod d) = sr (m + ((d / 2 : ℕ) : ZMod d))
      rw [sr_mul_r]

end SD

private lemma gcd_dvd_aux (v e g : ℕ) (hgd : g ∣ 2 ^ (v + 1) * e) (hg : ¬ 2 ^ v ∣ g) :
    g ∣ 2 ^ (v - 1) * e := by
  obtain ⟨g₁, g₂, hg₁, hg₂, rfl⟩ := Nat.dvd_mul.mp hgd
  obtain ⟨a, ha, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hg₁
  have hav : a < v := by
    by_contra hcon
    exact hg (Dvd.dvd.mul_right (pow_dvd_pow 2 (not_lt.mp hcon)) g₂)
  exact Nat.mul_dvd_mul (pow_dvd_pow 2 (by omega)) hg₂

private lemma not_condJ_of_dvd {d : ℕ} [NeZero d] (P e : ℕ) (he : e % 2 = 1)
    (hd : d = 2 * (P * e)) (hP : 0 < P) (j : ZMod d) (hj : P ∣ j.val) :
    ¬ ∃ n : ℕ, Even n ∧ (n : ZMod d) * j = ((d / 2 : ℕ) : ZMod d) := by
  rintro ⟨n, ⟨u, rfl⟩, hn⟩
  obtain ⟨c, hc⟩ := hj
  have hd2 : d / 2 = P * e := by
    rw [hd]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  have hjc : j = (P : ZMod d) * (c : ZMod d) := by
    rw [← Nat.cast_mul, ← hc, ZMod.natCast_zmod_val]
  have h2 : (2 : ZMod d) * (P : ZMod d) * (e : ZMod d) = 0 := by
    have h0 : (((2 * (P * e) : ℕ)) : ZMod d) = 0 := by
      rw [← hd, ZMod.natCast_self]
    push_cast at h0
    linear_combination h0
  rw [hd2] at hn
  push_cast at hn
  have key : ((P * e * e : ℕ) : ZMod d) = 0 := by
    push_cast
    linear_combination (-(e : ZMod d)) * hn + ((e : ZMod d) * ((u : ZMod d) + u)) * hjc +
      ((u : ZMod d) * c) * h2
  rw [ZMod.natCast_eq_zero_iff, hd, mul_comm 2 (P * e)] at key
  have h4 : 2 ∣ e := Nat.dvd_of_mul_dvd_mul_left (Nat.mul_pos hP (by omega)) key
  omega

private lemma condJ_of_not_dvd {d : ℕ} [NeZero d] (v e : ℕ) (hv : 1 ≤ v)
    (hde : d = 2 ^ (v + 1) * e) (j : ZMod d) (hj : ¬ 2 ^ v ∣ j.val) :
    ∃ n : ℕ, Even n ∧ (n : ZMod d) * j = ((d / 2 : ℕ) : ZMod d) := by
  have hgd : Nat.gcd j.val d ∣ 2 ^ (v + 1) * e := hde ▸ Nat.gcd_dvd_right _ _
  have hg2 : ¬ 2 ^ v ∣ Nat.gcd j.val d := fun h => hj (h.trans (Nat.gcd_dvd_left _ _))
  obtain ⟨w, hw⟩ := gcd_dvd_aux v e _ hgd hg2
  have hinv : j * j⁻¹ = ((Nat.gcd j.val d : ℕ) : ZMod d) := ZMod.mul_inv_eq_gcd j
  have hd' : d = 2 * (2 ^ v * e) := by
    rw [hde, pow_succ]
    ring
  have hd2 : d / 2 = 2 ^ v * e := by
    rw [hd']
    exact Nat.mul_div_cancel_left _ (by norm_num)
  have hpow : 2 ^ v = 2 * 2 ^ (v - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hnat : 2 ^ v * e = 2 * (Nat.gcd j.val d * w) := by
    rw [← hw, hpow]
    ring
  have hjinv : (((j⁻¹).val : ℕ) : ZMod d) = j⁻¹ := ZMod.natCast_zmod_val _
  refine ⟨w * (j⁻¹).val + w * (j⁻¹).val, ⟨_, rfl⟩, ?_⟩
  rw [hd2, hnat, Nat.cast_add, Nat.cast_mul, hjinv]
  calc ((w : ZMod d) * j⁻¹ + (w : ZMod d) * j⁻¹) * j = 2 * (w : ZMod d) * (j * j⁻¹) := by ring
    _ = 2 * (w : ZMod d) * ((Nat.gcd j.val d : ℕ) : ZMod d) := by rw [hinv]
    _ = ((2 * (Nat.gcd j.val d * w) : ℕ) : ZMod d) := by push_cast; ring

private lemma condJ_iff {d : ℕ} [NeZero d] (v e : ℕ) (hv : 1 ≤ v) (he : e % 2 = 1)
    (hde : d = 2 ^ (v + 1) * e) (j : ZMod d) :
    (∃ n : ℕ, Even n ∧ (n : ZMod d) * j = ((d / 2 : ℕ) : ZMod d)) ↔ ¬ 2 ^ v ∣ j.val := by
  constructor
  · intro h hj
    refine not_condJ_of_dvd (2 ^ v) e he ?_ (by positivity) j hj h
    rw [hde, pow_succ]
    ring
  · exact condJ_of_not_dvd v e hv hde j

private lemma card_dvd_val {d : ℕ} [NeZero d] (c : ℕ) (hc : c ∣ d) (hc0 : 0 < c) :
    Nat.card {j : ZMod d // c ∣ j.val} = d / c := by
  have hd0 : 0 < d := NeZero.pos d
  obtain ⟨q, hq⟩ := hc
  have hdc : d / c = q := by
    rw [hq]
    exact Nat.mul_div_cancel_left q hc0
  rw [hdc]
  have hlt : ∀ s : Fin q, c * s.1 < d := by
    intro s
    rw [hq]
    exact (Nat.mul_lt_mul_left hc0).mpr s.2
  let f : Fin q → {j : ZMod d // c ∣ j.val} := fun s =>
    ⟨((c * s.1 : ℕ) : ZMod d), by
      rw [ZMod.val_cast_of_lt (hlt s)]
      exact Dvd.intro _ rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro s s' h
      have h1 : ((c * s.1 : ℕ) : ZMod d) = ((c * s'.1 : ℕ) : ZMod d) := congrArg Subtype.val h
      have h2 := congrArg ZMod.val h1
      rw [ZMod.val_cast_of_lt (hlt s), ZMod.val_cast_of_lt (hlt s')] at h2
      exact Fin.ext (Nat.eq_of_mul_eq_mul_left hc0 h2)
    · rintro ⟨j, s, hs⟩
      have hs' : s < q := by
        have := ZMod.val_lt j
        rw [hs, hq] at this
        exact (Nat.mul_lt_mul_left hc0).mp this
      refine ⟨⟨s, hs'⟩, ?_⟩
      apply Subtype.ext
      show ((c * s : ℕ) : ZMod d) = j
      rw [← hs, ZMod.natCast_zmod_val]
  rw [← Nat.card_eq_of_bijective f hf]
  simp

private lemma card_par_zero {d : ℕ} [NeZero d] (hd : 2 ∣ d) :
    Nat.card {k : ZMod d // par hd k = 0} = d / 2 := by
  rw [← card_dvd_val 2 hd (by norm_num)]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun k => ?_)
  rw [par_eq_val_mod]
  omega

private lemma card_par_one {d : ℕ} [NeZero d] (hd : 2 ∣ d) :
    Nat.card {k : ZMod d // par hd k = 1} = d / 2 := by
  rw [← card_par_zero hd]
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.addRight (1 : ZMod d)) fun k => ?_)
  rw [Equiv.coe_addRight, par_eq_one_iff', par_eq_zero_iff', map_add, map_one]
  generalize ZMod.castHom hd (ZMod 2) k = x
  revert x
  decide

private lemma card_Ej {d : ℕ} [NeZero d] (hd : 2 ∣ d) (v e : ℕ) (hv : 1 ≤ v)
    (hde : d = 2 ^ (v + 1) * e) :
    Nat.card {j : ZMod d // par hd j = 0 ∧ ¬ 2 ^ v ∣ j.val} = d / 2 - 2 * e := by
  have hd' : d = 2 ^ v * (2 * e) := by
    rw [hde, pow_succ]
    ring
  have h1 : Nat.card {j : ZMod d // 2 ^ v ∣ j.val} = 2 * e := by
    have hdv : 2 ^ v ∣ d := ⟨2 * e, hd'⟩
    rw [card_dvd_val (2 ^ v) hdv (by positivity), hd']
    exact Nat.mul_div_cancel_left _ (by positivity)
  have hsub : {j : ZMod d | 2 ^ v ∣ j.val} ⊆ {j : ZMod d | par hd j = 0} := by
    intro j hj
    show par hd j = 0
    rw [par_eq_val_mod]
    have h2 : 2 ∣ 2 ^ v := dvd_pow_self 2 (by omega)
    exact Nat.mod_eq_zero_of_dvd (h2.trans hj)
  have hset : {j : ZMod d | par hd j = 0 ∧ ¬ 2 ^ v ∣ j.val} =
      {j : ZMod d | par hd j = 0} \ {j : ZMod d | 2 ^ v ∣ j.val} := by
    ext j
    exact Iff.rfl
  have h3 : Set.ncard {j : ZMod d | par hd j = 0} = d / 2 :=
    (Nat.card_coe_set_eq _).symm.trans (card_par_zero hd)
  have h4 : Set.ncard {j : ZMod d | 2 ^ v ∣ j.val} = 2 * e :=
    (Nat.card_coe_set_eq _).symm.trans h1
  calc Nat.card {j : ZMod d // par hd j = 0 ∧ ¬ 2 ^ v ∣ j.val}
      = Set.ncard {j : ZMod d | par hd j = 0 ∧ ¬ 2 ^ v ∣ j.val} := Nat.card_coe_set_eq _
    _ = Set.ncard ({j : ZMod d | par hd j = 0} \ {j : ZMod d | 2 ^ v ∣ j.val}) := by rw [hset]
    _ = Set.ncard {j : ZMod d | par hd j = 0} - Set.ncard {j : ZMod d | 2 ^ v ∣ j.val} :=
        Set.ncard_sdiff hsub
    _ = d / 2 - 2 * e := by rw [h3, h4]

section Count

variable (σ : MulAut I) (hσ : σ * σ = 1) {d : ℕ} [NeZero d] (hd : 2 ∣ d)

private def Sp (p : SDP σ hσ hd × SDP σ hσ hd) : Prop :=
  orderOf p.1 = 2 ∧ p.1 ∉ Z0 σ hσ hd ∧ p.2 ∈ Z0 σ hσ hd ∧ tSD σ hσ hd ∈ zpowers (p.1 * p.2)

private abbrev TA (v : ℕ) : Type :=
  ({k : ZMod d // par hd k = 0} × {j : ZMod d // par hd j = 0 ∧ ¬ 2 ^ v ∣ j.val}) ×
    {i : I // orderOf i = 2}

private abbrev TB : Type :=
  ({k : ZMod d // par hd k = 0} × {m : ZMod d // par hd m = 1}) × {i : I // i * σ i = 1}

private abbrev TC (I : Type) [Group I] : Type :=
  {p : I × I // orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))}

private def Φ (v : ℕ) : TA (I := I) hd v ⊕ TB σ hd ⊕ TC I → SDP σ hσ hd × SDP σ hσ hd
  | .inl x => (⟨x.2.1, sr (x.1.1.1 - x.1.2.1)⟩, ⟨1, sr x.1.1.1⟩)
  | .inr (.inl x) => (⟨x.2.1, sr x.1.2.1⟩, ⟨1, sr x.1.1.1⟩)
  | .inr (.inr x) => (⟨x.1.1, 1⟩, ⟨x.1.2, r ((d / 2 : ℕ) : ZMod d)⟩)

private lemma Φ_mem [Finite I] (h4 : 4 ∣ d) (v e : ℕ) (hv : 1 ≤ v) (he : e % 2 = 1)
    (hde : d = 2 ^ (v + 1) * e) (x : TA (I := I) hd v ⊕ TB σ hd ⊕ TC I) :
    Sp σ hσ hd (Φ σ hσ hd v x) := by
  rcases x with ⟨⟨⟨k, hk⟩, ⟨j, hj, hjv⟩⟩, ⟨i, hi⟩⟩ | ⟨⟨⟨k, hk⟩, ⟨m, hm⟩⟩, ⟨i, hi⟩⟩ |
    ⟨⟨i, i₀⟩, hi, hi₀, hodd⟩
  · exact shapeA σ hσ hd k j i hk hj ((condJ_iff v e hv he hde j).mpr hjv) hi
  · exact shapeB σ hσ hd h4 k m i hk hm hi
  · exact shapeC σ hσ hd h4 i i₀ hi hi₀ hodd

private lemma Φ_surj [Finite I] (h4 : 4 ∣ d) (v e : ℕ) (hv : 1 ≤ v) (he : e % 2 = 1)
    (hde : d = 2 ^ (v + 1) * e) (p : SDP σ hσ hd × SDP σ hσ hd) (hp : Sp σ hσ hd p) :
    ∃ x, Φ σ hσ hd v x = p := by
  obtain ⟨a, b⟩ := p
  obtain ⟨ha, haZ, hb, ht⟩ := hp
  rcases sp_cases σ hσ hd h4 a b ha haZ hb ht with
    ⟨k, j, i, hk, hj, hcond, hi, rfl, rfl⟩ | ⟨k, m, i, hk, hm, hi, rfl, rfl⟩ |
    ⟨i, i₀, hi, hi₀, hodd, rfl, rfl⟩
  · exact ⟨.inl ((⟨k, hk⟩, ⟨j, hj, (condJ_iff v e hv he hde j).mp hcond⟩), ⟨i, hi⟩), rfl⟩
  · exact ⟨.inr (.inl ((⟨k, hk⟩, ⟨m, hm⟩), ⟨i, hi⟩)), rfl⟩
  · exact ⟨.inr (.inr ⟨(i, i₀), hi, hi₀, hodd⟩), rfl⟩

private lemma Φ_inj (v : ℕ) : Function.Injective (Φ σ hσ hd v) := by
  rintro (⟨⟨⟨k, hk⟩, ⟨j, hj, hjv⟩⟩, ⟨i, hi⟩⟩ | ⟨⟨⟨k, hk⟩, ⟨m, hm⟩⟩, ⟨i, hi⟩⟩ |
      ⟨⟨i₁, i₂⟩, hi₁, hi₂, hodd⟩)
    (⟨⟨⟨k', hk'⟩, ⟨j', hj', hjv'⟩⟩, ⟨i', hi'⟩⟩ | ⟨⟨⟨k', hk'⟩, ⟨m', hm'⟩⟩, ⟨i', hi'⟩⟩ |
      ⟨⟨i₁', i₂'⟩, hi₁', hi₂', hodd'⟩) h
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have hii : i = i' := congrArg SemidirectProduct.left h1
    have hkk : k = k' := sr.inj (congrArg SemidirectProduct.right h2)
    have hjj : k - j = k' - j' := sr.inj (congrArg SemidirectProduct.right h1)
    subst hii hkk
    have hjj' : j = j' := sub_right_injective hjj
    subst hjj'
    rfl
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have hmm : k - j = m' := sr.inj (congrArg SemidirectProduct.right h1)
    rw [← hmm, par_sub_zero_zero hd hk hj] at hm'
    exact absurd hm' (by norm_num)
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h
    cases congrArg SemidirectProduct.right h2
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have hmm : m = k' - j' := sr.inj (congrArg SemidirectProduct.right h1)
    rw [hmm, par_sub_zero_zero hd hk' hj'] at hm
    exact absurd hm (by norm_num)
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have hii : i = i' := congrArg SemidirectProduct.left h1
    have hkk : k = k' := sr.inj (congrArg SemidirectProduct.right h2)
    have hmm : m = m' := sr.inj (congrArg SemidirectProduct.right h1)
    subst hii hkk hmm
    rfl
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h
    cases congrArg SemidirectProduct.right h2
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h
    cases congrArg SemidirectProduct.right h2
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h
    cases congrArg SemidirectProduct.right h2
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have hi₁ : i₁ = i₁' := congrArg SemidirectProduct.left h1
    have hi₂ : i₂ = i₂' := congrArg SemidirectProduct.left h2
    subst hi₁ hi₂
    rfl

private lemma card_pairs [Finite I] (h4 : 4 ∣ d) (v e : ℕ) (hv : 1 ≤ v) (he : e % 2 = 1)
    (hde : d = 2 ^ (v + 1) * e) :
    Nat.card {p : SDP σ hσ hd × SDP σ hσ hd // Sp σ hσ hd p} =
      Nat.card (TA (I := I) hd v) + (Nat.card (TB σ hd) + Nat.card (TC I)) := by
  have hbij : Function.Bijective
      (fun x => (⟨Φ σ hσ hd v x, Φ_mem σ hσ hd h4 v e hv he hde x⟩ : {p // Sp σ hσ hd p})) := by
    constructor
    · intro x y h
      exact Φ_inj σ hσ hd v (congrArg Subtype.val h)
    · rintro ⟨p, hp⟩
      obtain ⟨x, hx⟩ := Φ_surj σ hσ hd h4 v e hv he hde p hp
      exact ⟨x, Subtype.ext hx⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_sum, Nat.card_sum]

end Count

theorem tside_count [Finite I] (σ : MulAut I) (hσ : σ * σ = 1) {d : ℕ} [NeZero d] (hd : 2 ∣ d)
    (h4 : 4 ∣ d) (ι ι' P : ℕ) (hι : ι = Nat.card {i : I // orderOf i = 2})
    (hι' : ι' = Nat.card {i : I // i * σ i = 1})
    (hP : P = Nat.card {p : I × I // orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))}) :
    Nat.card {p : (I ⋊[dihAct σ hσ hd] DihedralGroup d) × (I ⋊[dihAct σ hσ hd] DihedralGroup d) //
        orderOf p.1 = 2 ∧ p.1 ∉ Z0 σ hσ hd ∧ p.2 ∈ Z0 σ hσ hd ∧
        tSD σ hσ hd ∈ zpowers (p.1 * p.2)} =
      (d / 2) * (((d / 2) - 2 * ((d / 2) / 2 ^ (d / 2).factorization 2)) * ι + (d / 2) * ι') + P := by
  have hδ0 : d / 2 ≠ 0 := by
    have := NeZero.pos d
    omega
  have hprod : 2 ^ (d / 2).factorization 2 * ((d / 2) / 2 ^ (d / 2).factorization 2) = d / 2 :=
    Nat.ordProj_mul_ordCompl_eq_self (d / 2) 2
  have hv : 1 ≤ (d / 2).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two hδ0 (by omega)
  have he : ((d / 2) / 2 ^ (d / 2).factorization 2) % 2 = 1 := by
    have hc := Nat.coprime_ordCompl Nat.prime_two hδ0
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two] at hc
    omega
  generalize (d / 2).factorization 2 = v at hprod hv he ⊢
  generalize hev : (d / 2) / 2 ^ v = e at hprod he ⊢
  have hde : d = 2 ^ (v + 1) * e := by
    calc d = 2 * (d / 2) := (two_mul_half hd).symm
      _ = 2 * (2 ^ v * e) := by rw [hprod]
      _ = 2 ^ (v + 1) * e := by ring
  show Nat.card {p : SDP σ hσ hd × SDP σ hσ hd // Sp σ hσ hd p} = _
  rw [card_pairs σ hσ hd h4 v e hv he hde]
  have hA : Nat.card (TA (I := I) hd v) = (d / 2) * (d / 2 - 2 * e) * ι := by
    rw [Nat.card_prod, Nat.card_prod, card_par_zero hd, card_Ej hd v e hv hde, ← hι]
  have hB : Nat.card (TB σ hd) = (d / 2) * (d / 2) * ι' := by
    rw [Nat.card_prod, Nat.card_prod, card_par_zero hd, card_par_one hd, ← hι']
  have hC : Nat.card (TC I) = P := hP.symm
  rw [hA, hB, hC]
  ring

end CFSG.GH74.GLS.SP.Local
