module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement

public section

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaLocal

variable {X : Type} [Group X]

@[expose] def IsQ8Pair (p q : X) : Prop :=
  p ^ 4 = 1 ∧ q ^ 2 = p ^ 2 ∧ q * p * q⁻¹ = p⁻¹ ∧ p ^ 2 ≠ 1

namespace IsQ8Pair

variable {p q : X}

theorem sq_mul_sq (h : IsQ8Pair p q) : p ^ 2 * p ^ 2 = 1 := by
  rw [← pow_add]
  exact h.1

theorem inv_eq (h : IsQ8Pair p q) : p⁻¹ = p * p ^ 2 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ', ← pow_succ']
  exact h.1

theorem q_inv_eq (h : IsQ8Pair p q) : q⁻¹ = q * p ^ 2 := by
  rw [inv_eq_iff_mul_eq_one, ← mul_assoc, ← pow_two, h.2.1]
  exact h.sq_mul_sq

theorem mul_comm_sq (h : IsQ8Pair p q) : q * p ^ 2 = p ^ 2 * q := by
  have h1 : q * p * q⁻¹ = p⁻¹ := h.2.2.1
  have h2 : q * p ^ 2 * q⁻¹ = p⁻¹ ^ 2 := by
    rw [← h1, pow_two, pow_two]
    group
  have h3 : p⁻¹ ^ 2 = p ^ 2 := by
    rw [inv_pow, inv_eq_iff_mul_eq_one]
    exact h.sq_mul_sq
  rw [h3] at h2
  calc q * p ^ 2 = q * p ^ 2 * q⁻¹ * q := by group
    _ = p ^ 2 * q := by rw [h2]

theorem q_mul_p (h : IsQ8Pair p q) : q * p = p⁻¹ * q := by
  calc q * p = q * p * q⁻¹ * q := by group
    _ = p⁻¹ * q := by rw [h.2.2.1]

theorem swap (h : IsQ8Pair p q) : IsQ8Pair q p := by
  refine ⟨?_, h.2.1.symm, ?_, ?_⟩
  · calc q ^ 4 = q ^ 2 * q ^ 2 := by rw [← pow_add]
      _ = p ^ 2 * p ^ 2 := by rw [h.2.1]
      _ = 1 := h.sq_mul_sq
  ·
    have h1 : p * q = q * p⁻¹ := by
      have h2 : (q * p * q⁻¹)⁻¹ = p := by rw [h.2.2.1, inv_inv]
      calc p * q = (q * p * q⁻¹)⁻¹ * q := by rw [h2]
        _ = q * p⁻¹ := by group
    calc p * q * p⁻¹ = q * p⁻¹ * p⁻¹ := by rw [h1]
      _ = q * (p⁻¹ * p⁻¹) := by group
      _ = q * p ^ 2 := by
          rw [show p⁻¹ * p⁻¹ = (p ^ 2)⁻¹ by rw [pow_two]; group, inv_eq_of_mul_eq_one_right
            h.sq_mul_sq]
      _ = q⁻¹ := h.q_inv_eq.symm
  · rw [h.2.1]
    exact h.2.2.2

theorem mul_left (h : IsQ8Pair p q) : IsQ8Pair (p * q) p := by
  have hsq : (p * q) ^ 2 = p ^ 2 := by
    calc (p * q) ^ 2 = p * (q * p) * q := by rw [pow_two]; group
      _ = p * (p⁻¹ * q) * q := by rw [h.q_mul_p]
      _ = q ^ 2 := by rw [pow_two]; group
      _ = p ^ 2 := h.2.1
  refine ⟨?_, hsq.symm, ?_, ?_⟩
  · calc (p * q) ^ 4 = (p * q) ^ 2 * (p * q) ^ 2 := by rw [← pow_add]
      _ = p ^ 2 * p ^ 2 := by rw [hsq]
      _ = 1 := h.sq_mul_sq
  · calc p * (p * q) * p⁻¹ = p ^ 2 * (q * p⁻¹) := by rw [pow_two]; group
      _ = q * p ^ 2 * p⁻¹ := by rw [← mul_assoc, ← h.mul_comm_sq]
      _ = q⁻¹ * p⁻¹ := by rw [h.q_inv_eq]
      _ = (p * q)⁻¹ := by group
  · rw [hsq]
    exact h.2.2.2

theorem diag {p' q' : X} (h : IsQ8Pair p q) (h' : IsQ8Pair p' q')
    (hpp : Commute p p') (hpq : Commute p q') (hqp : Commute q p') (hqq : Commute q q')
    (hne : p ^ 2 * p' ^ 2 ≠ 1) : IsQ8Pair (p * p') (q * q') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hpp.mul_pow, h.1, h'.1, one_mul]
  · rw [hpp.mul_pow, hqq.mul_pow, h.2.1, h'.2.1]
  · calc q * q' * (p * p') * (q * q')⁻¹ = q * (q' * p) * p' * q'⁻¹ * q⁻¹ := by group
      _ = q * (p * q') * p' * q'⁻¹ * q⁻¹ := by rw [hpq.eq]
      _ = q * p * (q' * p' * q'⁻¹) * q⁻¹ := by group
      _ = q * p * p'⁻¹ * q⁻¹ := by rw [h'.2.2.1]
      _ = q * p * q⁻¹ * p'⁻¹ := by
          have : p'⁻¹ * q⁻¹ = q⁻¹ * p'⁻¹ := by
            rw [← mul_inv_rev, ← mul_inv_rev, hqp.eq]
          rw [mul_assoc (q * p), this, ← mul_assoc]
      _ = p⁻¹ * p'⁻¹ := by rw [h.2.2.1]
      _ = (p * p')⁻¹ := by rw [← mul_inv_rev, hpp.eq]
  · rw [hpp.mul_pow]
    exact hne

end IsQ8Pair

@[expose] def zmod4Pow (p : X) (k : ZMod 4) : X := p ^ k.val

theorem pow_mod_four {p : X} (hp : p ^ 4 = 1) (n : ℕ) : p ^ (n % 4) = p ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, hp, one_pow, mul_one]

theorem zmod4Pow_add {p : X} (hp : p ^ 4 = 1) (i j : ZMod 4) :
    zmod4Pow p (i + j) = zmod4Pow p i * zmod4Pow p j := by
  unfold zmod4Pow
  rw [ZMod.val_add, pow_mod_four hp, pow_add]

theorem zmod4Pow_zero (p : X) : zmod4Pow p 0 = 1 := by
  unfold zmod4Pow
  rw [ZMod.val_zero, pow_zero]

theorem zmod4Pow_neg {p : X} (hp : p ^ 4 = 1) (i : ZMod 4) :
    zmod4Pow p (-i) = (zmod4Pow p i)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← zmod4Pow_add hp, neg_add_cancel, zmod4Pow_zero]

theorem zmod4Pow_sub {p : X} (hp : p ^ 4 = 1) (i j : ZMod 4) :
    zmod4Pow p (i - j) = zmod4Pow p i * (zmod4Pow p j)⁻¹ := by
  rw [sub_eq_add_neg, zmod4Pow_add hp, zmod4Pow_neg hp]

theorem conj_zmod4Pow {p q : X} (h : IsQ8Pair p q) (i : ZMod 4) :
    q * zmod4Pow p i * q⁻¹ = (zmod4Pow p i)⁻¹ := by
  unfold zmod4Pow
  rw [← conj_pow, h.2.2.1, inv_pow]

theorem zmod4Pow_mul_q {p q : X} (h : IsQ8Pair p q) (i : ZMod 4) :
    zmod4Pow p i * q = q * zmod4Pow p (-i) := by
  have h1 := conj_zmod4Pow h (-i)
  rw [zmod4Pow_neg h.1, inv_inv] at h1
  calc zmod4Pow p i * q = q * (zmod4Pow p i)⁻¹ * q⁻¹ * q := by rw [h1]
    _ = q * zmod4Pow p (-i) := by rw [zmod4Pow_neg h.1]; group

theorem q8_xa_xa {p q : X} (h : IsQ8Pair p q) (i j : ZMod 4) :
    zmod4Pow p (2 + j - i) = q * zmod4Pow p i * (q * zmod4Pow p j) := by
  have h2 : zmod4Pow p 2 = p ^ 2 := rfl
  calc zmod4Pow p (2 + j - i) = zmod4Pow p 2 * zmod4Pow p (-i + j) := by
        rw [← zmod4Pow_add h.1]
        congr 1
        ring
    _ = q * q * (zmod4Pow p (-i) * zmod4Pow p j) := by
        rw [h2, ← pow_two, h.2.1, zmod4Pow_add h.1]
    _ = q * (q * zmod4Pow p (-i)) * zmod4Pow p j := by group
    _ = q * zmod4Pow p i * (q * zmod4Pow p j) := by
        rw [← zmod4Pow_mul_q h]
        group

@[expose] def q8Hom {p q : X} (h : IsQ8Pair p q) : QuaternionGroup 2 →* X where
  toFun x := match x with
    | .a i => zmod4Pow p i
    | .xa i => q * zmod4Pow p i
  map_one' := by
    change zmod4Pow p 0 = 1
    exact zmod4Pow_zero p
  map_mul' x y := by
    cases x with
    | a i =>
      cases y with
      | a j =>
        change zmod4Pow p (i + j) = zmod4Pow p i * zmod4Pow p j
        exact zmod4Pow_add h.1 i j
      | xa j =>
        change q * zmod4Pow p (j - i) = zmod4Pow p i * (q * zmod4Pow p j)
        rw [← mul_assoc, zmod4Pow_mul_q h, mul_assoc, ← zmod4Pow_add h.1, neg_add_eq_sub]
    | xa i =>
      cases y with
      | a j =>
        change q * zmod4Pow p (i + j) = q * zmod4Pow p i * zmod4Pow p j
        rw [zmod4Pow_add h.1, mul_assoc]
      | xa j =>
        change zmod4Pow p (((2 : ℕ) : ZMod 4) + j - i) =
          q * zmod4Pow p i * (q * zmod4Pow p j)
        rw [Nat.cast_ofNat]
        exact q8_xa_xa h i j

theorem q8Hom_injective {p q : X} (h : IsQ8Pair p q) : Function.Injective (q8Hom h) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  cases x with
  | a i =>
    change zmod4Pow p i = 1 at hx
    unfold zmod4Pow at hx
    have hv : i.val < 4 := ZMod.val_lt i
    have hi : i.val = 0 := by
      rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 by omega) with
        h0 | h1 | h2 | h3
      · exact h0
      · rw [h1, pow_one] at hx
        exact absurd (by rw [hx, one_pow]) h.2.2.2
      · rw [h2] at hx
        exact absurd hx h.2.2.2
      · rw [h3] at hx
        have : p = 1 := by
          have h4 := h.1
          rw [show 4 = 3 + 1 from rfl, pow_succ, hx, one_mul] at h4
          exact h4
        exact absurd (by rw [this, one_pow]) h.2.2.2
    have : i = 0 := (ZMod.val_eq_zero i).mp hi
    rw [this]
    rfl
  | xa i =>
    change q * zmod4Pow p i = 1 at hx
    exfalso
    have hq : q = (zmod4Pow p i)⁻¹ := eq_inv_of_mul_eq_one_left hx
    have hcomm : q * p = p * q := by
      have hc : Commute q p := by
        rw [hq]
        unfold zmod4Pow
        exact ((Commute.refl p).pow_left _).inv_left
      exact hc.eq
    have h1 := h.2.2.1
    rw [hcomm, mul_inv_cancel_right] at h1
    apply h.2.2.2
    rw [pow_two]
    calc p * p = p * p⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel p

theorem IsQ8Pair.exists_quaternion {p q : X} (h : IsQ8Pair p q) :
    ∃ Q : Subgroup X, p ∈ Q ∧ q ∈ Q ∧ AschbacherTheorem3.IsQuaternionTwoGroup Q ∧
      ∀ S : Subgroup X, p ∈ S → q ∈ S → Q ≤ S := by
  refine ⟨(q8Hom h).range, ⟨.a 1, ?_⟩, ⟨.xa 0, ?_⟩, ⟨3, le_rfl,
    ⟨(MonoidHom.ofInjective (q8Hom_injective h)).symm⟩⟩, ?_⟩
  · change zmod4Pow p 1 = p
    have : Fact (1 < 4) := ⟨by norm_num⟩
    unfold zmod4Pow
    rw [ZMod.val_one, pow_one]
  · change q * zmod4Pow p 0 = q
    rw [zmod4Pow_zero, mul_one]
  · rintro S hpS hqS _ ⟨x, rfl⟩
    cases x with
    | a i =>
      change p ^ i.val ∈ S
      exact S.pow_mem hpS _
    | xa i =>
      change q * p ^ i.val ∈ S
      exact S.mul_mem hqS (S.pow_mem hpS _)

theorem IsQ8Pair.map {Y : Type} [Group Y] {p q : X} (h : IsQ8Pair p q) (f : X →* Y)
    (hf : Function.Injective f) : IsQ8Pair (f p) (f q) := by
  refine ⟨by rw [← map_pow, h.1, map_one], by rw [← map_pow, ← map_pow, h.2.1], ?_, ?_⟩
  · rw [← map_inv, ← map_mul, ← map_mul, h.2.2.1, map_inv]
  · rw [← map_pow]
    intro h1
    exact h.2.2.2 (hf (h1.trans (map_one f).symm))

theorem IsQ8Pair.of_map {Y : Type} [Group Y] {p q : X} (f : X →* Y)
    (hf : Function.Injective f) (h : IsQ8Pair (f p) (f q)) : IsQ8Pair p q := by
  refine ⟨hf ?_, hf ?_, hf ?_, fun h1 => h.2.2.2 ?_⟩
  · rw [map_pow, h.1, map_one]
  · rw [map_pow, map_pow, h.2.1]
  · rw [map_mul, map_mul, map_inv, h.2.2.1, map_inv]
  · rw [← map_pow, h1, map_one]

theorem IsQ8Pair.not_commute {p q : X} (h : IsQ8Pair p q) : q * p ≠ p * q := by
  intro hqp
  apply h.2.2.2
  have h1 := h.2.2.1
  rw [hqp, mul_inv_cancel_right] at h1
  rw [pow_two]
  calc p * p = p * p⁻¹ := by rw [← h1]
    _ = 1 := mul_inv_cancel p

theorem two_le_two_pow {n : ℕ} (hn : 3 ≤ n) : 2 ≤ 2 ^ (n - 2) :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem quaternionGroup_sq_eq_one_of_central {m : ℕ} (hm : 2 ≤ m) {g : QuaternionGroup m}
    (hg : ∀ y, g * y = y * g) : g ^ 2 = 1 := by
  cases g with
  | a i =>
    have h1 := hg (QuaternionGroup.xa 0)
    rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at h1
    have h2 := QuaternionGroup.xa.inj h1
    rw [pow_two, QuaternionGroup.a_mul_a, QuaternionGroup.one_def]
    congr 1
    linear_combination -h2
  | xa i =>
    exfalso
    have h1 := hg (QuaternionGroup.a 1)
    rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at h1
    have h2 := QuaternionGroup.xa.inj h1
    have h3 : ((2 : ℕ) : ZMod (2 * m)) = 0 := by
      rw [Nat.cast_ofNat]
      linear_combination h2
    rw [ZMod.natCast_eq_zero_iff] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega

theorem sq_eq_one_of_central {Q : Subgroup X} (hQ : AschbacherTheorem3.IsQuaternionTwoGroup Q)
    {x : X} (hx : x ∈ Q) (hxc : ∀ y ∈ Q, x * y = y * x) : x ^ 2 = 1 := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hQ
  have hcen : ∀ y, e ⟨x, hx⟩ * y = y * e ⟨x, hx⟩ := by
    intro y
    have h1 : (⟨x, hx⟩ : Q) * e.symm y = e.symm y * ⟨x, hx⟩ :=
      Subtype.ext (hxc _ (e.symm y).2)
    have h2 := congrArg e h1
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  have h3 := quaternionGroup_sq_eq_one_of_central (two_le_two_pow hn) hcen
  rw [← map_pow] at h3
  have h4 : (⟨x, hx⟩ : Q) ^ 2 = 1 := e.injective (h3.trans (map_one e).symm)
  exact congrArg Subtype.val h4

theorem quaternionGroup_q8Pair {m : ℕ} (hm : 2 ≤ m) (hev : Even m) :
    IsQ8Pair (QuaternionGroup.a ((m / 2 : ℕ) : ZMod (2 * m)))
      (QuaternionGroup.xa (0 : ZMod (2 * m))) := by
  obtain ⟨k, hk⟩ := hev
  have hmk : m / 2 = k := by omega
  rw [hmk]
  have hpow : ∀ j : ℕ, (QuaternionGroup.a ((k : ℕ) : ZMod (2 * m))) ^ j =
      QuaternionGroup.a 1 ^ (k * j) := by
    intro j
    rw [pow_mul, QuaternionGroup.a_one_pow]
  have hsq : (QuaternionGroup.a ((k : ℕ) : ZMod (2 * m))) ^ 2 =
      QuaternionGroup.a (m : ZMod (2 * m)) := by
    rw [hpow, QuaternionGroup.a_one_pow]
    congr 1
    rw [hk]
    push_cast
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hpow, show k * 4 = 2 * m by omega, QuaternionGroup.a_one_pow_n]
  · rw [QuaternionGroup.xa_sq, hsq]
  · have hinv : (QuaternionGroup.a ((k : ℕ) : ZMod (2 * m)))⁻¹ =
        QuaternionGroup.a (-((k : ℕ) : ZMod (2 * m))) := by
      rw [inv_eq_iff_mul_eq_one, QuaternionGroup.a_mul_a, add_neg_cancel,
        QuaternionGroup.a_zero]
    rw [hinv, mul_inv_eq_iff_eq_mul, QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa]
    congr 1
    ring
  · rw [hsq, QuaternionGroup.one_def]
    intro h
    have h1 := QuaternionGroup.a.inj h
    rw [ZMod.natCast_eq_zero_iff] at h1
    have := Nat.le_of_dvd (by omega) h1
    omega

theorem exists_q8Pair {Q : Subgroup X} (hQ : AschbacherTheorem3.IsQuaternionTwoGroup Q) :
    ∃ p ∈ Q, ∃ q ∈ Q, IsQ8Pair p q := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hQ
  have hm := two_le_two_pow hn
  have hev : Even (2 ^ (n - 2)) := (Nat.even_pow' (by omega)).mpr even_two
  have h := (quaternionGroup_q8Pair hm hev).map (Q.subtype.comp e.symm.toMonoidHom)
    (Q.subtype_injective.comp e.symm.injective)
  exact ⟨_, (e.symm _).2, _, (e.symm _).2, h⟩

theorem q8Pair_normalize {W Y : Subgroup X} {p q : X} (h : IsQ8Pair p q) (hpY : p ∈ Y)
    (hqY : q ∈ Y) (hW : ∀ x ∈ Y, ∀ y ∈ Y, x ∉ W → y ∉ W → x * y ∈ W) :
    ∃ P R : X, IsQ8Pair P R ∧ P ∈ W ∧ P ∈ Y ∧ R ∈ Y ∧ P ^ 2 = p ^ 2 ∧
      (∀ y : X, Commute p y → Commute q y → Commute P y ∧ Commute R y) ∧
      (R ∈ W → q ∈ W ∧ p ∈ W) := by
  by_cases hp : p ∈ W
  · exact ⟨p, q, h, hp, hpY, hqY, rfl, fun y h1 h2 => ⟨h1, h2⟩, fun hq => ⟨hq, hp⟩⟩
  · by_cases hq : q ∈ W
    · exact ⟨q, p, h.swap, hq, hqY, hpY, h.2.1, fun y h1 h2 => ⟨h2, h1⟩,
        fun hp' => absurd hp' hp⟩
    · exact ⟨p * q, p, h.mul_left, hW p hpY q hqY hp hq, Y.mul_mem hpY hqY, hpY,
        h.mul_left.2.1.symm, fun y h1 h2 => ⟨h1.mul_left h2, h1⟩, fun hp' => absurd hp' hp⟩

theorem exists_q8Pair_of_index_two {W Y : Subgroup X} {p₁ q₁ p₂ q₂ : X}
    (h₁ : IsQ8Pair p₁ q₁) (h₂ : IsQ8Pair p₂ q₂) (hpp : Commute p₁ p₂) (hpq : Commute p₁ q₂)
    (hqp : Commute q₁ p₂) (hqq : Commute q₁ q₂) (hne : p₁ ^ 2 * p₂ ^ 2 ≠ 1)
    (hp₁ : p₁ ∈ Y) (hq₁ : q₁ ∈ Y) (hp₂ : p₂ ∈ Y) (hq₂ : q₂ ∈ Y)
    (hW : ∀ x ∈ Y, ∀ y ∈ Y, x ∉ W → y ∉ W → x * y ∈ W) :
    ∃ p ∈ W, ∃ q ∈ W, IsQ8Pair p q := by
  obtain ⟨P₁, R₁, hP₁, hP₁W, hP₁Y, hR₁Y, hP₁sq, hc₁, hR₁W⟩ := q8Pair_normalize h₁ hp₁ hq₁ hW
  obtain ⟨P₂, R₂, hP₂, hP₂W, hP₂Y, hR₂Y, hP₂sq, hc₂, hR₂W⟩ := q8Pair_normalize h₂ hp₂ hq₂ hW
  by_cases hR₁ : R₁ ∈ W
  · exact ⟨P₁, hP₁W, R₁, hR₁, hP₁⟩
  by_cases hR₂ : R₂ ∈ W
  · exact ⟨P₂, hP₂W, R₂, hR₂, hP₂⟩
  have hc₂P₁ := hc₂ P₁ (hc₁ p₂ hpp hqp).1.symm (hc₁ q₂ hpq hqq).1.symm
  have hc₂R₁ := hc₂ R₁ (hc₁ p₂ hpp hqp).2.symm (hc₁ q₂ hpq hqq).2.symm
  refine ⟨P₁ * P₂, W.mul_mem hP₁W hP₂W, R₁ * R₂, hW R₁ hR₁Y R₂ hR₂Y hR₁ hR₂, ?_⟩
  refine hP₁.diag hP₂ hc₂P₁.1.symm hc₂P₁.2.symm hc₂R₁.1.symm hc₂R₁.2.symm ?_
  rw [hP₁sq, hP₂sq]
  exact hne

end DeltaLocal

end CFSG.ComponentClassification.AschbacherTheorem5
