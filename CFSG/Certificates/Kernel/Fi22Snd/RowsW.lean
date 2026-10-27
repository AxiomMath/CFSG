module

public import Certificates.Data.Kernel.Fi22Nbr3153W
public import CFSG.Certificates.Kernel.Fi22Snd.Rows

public section

namespace CFSG.KC.Fi22Snd

open CFSG.KC.Enum CFSG.KC.N3153

@[expose] def posF (B p : Nat) : Nat := p % B + 48 * B * (p / B)

@[expose] def DilOK (D : Nat → Nat) : Prop :=
  ∀ m < 2 ^ 4096, ∀ q, (D m).testBit q = true ↔ ∃ p, (p < 4096 ∧ m.testBit p = true) ∧ q = 48 * p

theorem roundK_testBit {x H s : Nat} {P : Nat → Prop} {pos pos' : Nat → Nat} {b : Nat → Prop}
    (hx : ∀ q, x.testBit q = true ↔ ∃ p, P p ∧ q = pos p)
    (hH : ∀ p, P p → (H.testBit (pos p) = true ↔ b p))
    (hpos : ∀ p, P p → (b p → pos' p = pos p + s) ∧ (¬ b p → pos' p = pos p)) :
    ∀ q, (roundK H s x).testBit q = true ↔ ∃ p, P p ∧ q = pos' p := by
  intro q
  rw [roundK, CFSG.KC.Pack.strictN_eq]
  change ((x ^^^ (x &&& H)) ||| ((x &&& H) <<< s)).testBit q = true ↔ _
  have e1 : (x ^^^ (x &&& H)).testBit q = (x.testBit q && !H.testBit q) := by
    rw [Nat.testBit_xor, Nat.testBit_and]
    cases x.testBit q <;> cases H.testBit q <;> rfl
  rw [Nat.testBit_or, e1, Nat.testBit_shiftLeft, Nat.testBit_and]
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, ge_iff_le]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h0, h1, h2⟩)
    · obtain ⟨p, hp, rfl⟩ := (hx q).1 h1
      have hb : ¬ b p := fun hb => by
        rw [(hH p hp).2 hb] at h2
        exact Bool.noConfusion h2
      exact ⟨p, hp, ((hpos p hp).2 hb).symm⟩
    · obtain ⟨p, hp, hq⟩ := (hx _).1 h1
      rw [hq] at h2
      have hb := (hH p hp).1 h2
      refine ⟨p, hp, ?_⟩
      rw [(hpos p hp).1 hb]
      omega
  · rintro ⟨p, hp, rfl⟩
    by_cases hb : b p
    · right
      rw [(hpos p hp).1 hb, Nat.add_sub_cancel]
      exact ⟨by omega, (hx _).2 ⟨p, hp, rfl⟩, (hH p hp).2 hb⟩
    · left
      rw [(hpos p hp).2 hb]
      refine ⟨(hx _).2 ⟨p, hp, rfl⟩, ?_⟩
      cases h : H.testBit (pos p)
      · rfl
      · exact absurd ((hH p hp).1 h) hb

theorem mask_testBit {H B e : Nat}
    (h : allN 4096 (fun p => Nat.beq (Nat.land (Nat.shiftRight H (posF B p)) 1) (p / e % 2)) = true)
    {p : Nat} (hp : p < 4096) : H.testBit (posF B p) = true ↔ p / e % 2 = 1 := by
  have h1 := Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec h p hp)
  rw [← beq_bit, h1, Nat.beq_eq]

theorem round_step {x H B e s : Nat} {m : Nat}
    (hx : ∀ q, x.testBit q = true ↔ ∃ p, (p < 4096 ∧ m.testBit p = true) ∧ q = posF B p)
    (hH : allN 4096 (fun p => Nat.beq (Nat.land (Nat.shiftRight H (posF B p)) 1) (p / e % 2)) = true)
    (hpos : ∀ p, (p / e % 2 = 1 → posF e p = posF B p + s) ∧ (¬ p / e % 2 = 1 → posF e p = posF B p)) :
    ∀ q, (roundK H s x).testBit q = true ↔ ∃ p, (p < 4096 ∧ m.testBit p = true) ∧ q = posF e p :=
  roundK_testBit hx (fun p hp => mask_testBit hH hp.1) (fun p _ => hpos p)

theorem testBit_ge {m k q : Nat} (hm : m < 2 ^ k) (hq : k ≤ q) : m.testBit q = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) hq))

theorem start_testBit {m : Nat} (hm : m < 2 ^ 4096) :
    ∀ q, m.testBit q = true ↔ ∃ p, (p < 4096 ∧ m.testBit p = true) ∧ q = posF 4096 p := by
  intro q
  constructor
  · intro h
    have hq : q < 4096 := by
      by_contra hq
      rw [testBit_ge hm (by omega)] at h
      exact Bool.noConfusion h
    exact ⟨q, ⟨hq, h⟩, by unfold posF; omega⟩
  · rintro ⟨p, ⟨hp, h⟩, rfl⟩
    have e : posF 4096 p = p := by
      unfold posF
      omega
    rw [e]
    exact h

theorem end_testBit {D m : Nat}
    (h : ∀ q, D.testBit q = true ↔ ∃ p, (p < 4096 ∧ m.testBit p = true) ∧ q = posF 1 p) :
    ∀ q, D.testBit q = true ↔ ∃ p, (p < 4096 ∧ m.testBit p = true) ∧ q = 48 * p := by
  intro q
  rw [h]
  have e : ∀ p, posF 1 p = 48 * p := fun p => by
    unfold posF
    omega
  simp only [e]

theorem testBit_sum_pow {f : Nat → Nat} : ∀ m, (∀ i, i + 1 < m → f i < f (i + 1)) →
    (∀ q, (∑ i ∈ Finset.range m, 2 ^ f i).testBit q = true ↔ ∃ i < m, f i = q) ∧
      (0 < m → ∑ i ∈ Finset.range m, 2 ^ f i < 2 ^ (f (m - 1) + 1))
  | 0, _ => ⟨fun q => by simp, fun h => absurd h (Nat.lt_irrefl 0)⟩
  | m + 1, hf => by
    obtain ⟨A, B⟩ := testBit_sum_pow m (fun i hi => hf i (by omega))
    set a := ∑ i ∈ Finset.range m, 2 ^ f i with ha
    have hlt : a < 2 ^ f m := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [ha]
      · exact lt_of_lt_of_le (B hm) (Nat.pow_le_pow_right (by norm_num) (by
          have := hf (m - 1) (by omega)
          rw [Nat.sub_add_cancel hm] at this
          omega))
    have hs : ∑ i ∈ Finset.range (m + 1), 2 ^ f i = 2 ^ f m * 2 ^ 0 + a := by
      rw [Finset.sum_range_succ, pow_zero, Nat.mul_one, Nat.add_comm]
    refine ⟨fun q => ?_, fun _ => ?_⟩
    · rw [hs, Nat.testBit_two_pow_mul_add _ hlt]
      by_cases hq : q < f m
      · rw [if_pos hq, A]
        constructor
        · rintro ⟨i, hi, rfl⟩
          exact ⟨i, by omega, rfl⟩
        · rintro ⟨i, hi, rfl⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · exact ⟨i, hi, rfl⟩
          · omega
      · rw [if_neg hq, Nat.testBit_two_pow]
        have hno : ¬ ∃ i < m, f i = q := by
          rintro ⟨i, hi, rfl⟩
          have h1 := (A (f i)).2 ⟨i, hi, rfl⟩
          rw [testBit_ge hlt (by omega)] at h1
          exact Bool.noConfusion h1
        rw [decide_eq_true_iff]
        constructor
        · intro h
          exact ⟨m, by omega, by omega⟩
        · rintro ⟨i, hi, rfl⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · exact absurd ⟨i, hi, rfl⟩ hno
          · omega
    · rw [hs, pow_zero, Nat.mul_one, Nat.add_sub_cancel, Nat.pow_succ]
      omega

theorem rowOK_of_W {n d : Nat} {R M S D : Nat → Nat} (hn : n ≤ 4096) (hd : d < 2 ^ 64)
    (hD : DilOK D) {x : Nat} (h : rowOKW n d R M S D x = true) : rowOK n d R M S x = true := by
  unfold rowOKW at h
  rw [CFSG.KC.Pack.strictB_eq, CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h1, h'⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h2, h''⟩ := CFSG.KC.Pack.band_iff.1 h'
  obtain ⟨h3, h'''⟩ := CFSG.KC.Pack.band_iff.1 h''
  obtain ⟨h4, h5⟩ := CFSG.KC.Pack.band_iff.1 h'''
  unfold rowOK
  rw [CFSG.KC.Pack.strictB_eq]
  refine CFSG.KC.Pack.band_iff.2 ⟨h1, CFSG.KC.Pack.band_iff.2 ⟨h2, CFSG.KC.Pack.band_iff.2 ⟨h3, ?_⟩⟩⟩
  set r := R x with hr
  set m := M x with hmd
  have hm : m < 2 ^ 4096 := by
    have := Nat.le_of_ble_eq_true h4
    change m + 1 ≤ 1 <<< 4096 at this
    rw [Nat.one_shiftLeft] at this
    omega
  have hS : S x = x + 1 + D m * 2 ^ 128 := by
    rw [Nat.eq_of_beq_eq_true h5]
    change x + 1 + D m <<< 128 = _
    rw [Nat.shiftLeft_eq]
  have hmask : Nat.shiftRight (maskK d r) (nat_lit 64) = m := Nat.eq_of_beq_eq_true h3
  have hinc : ∀ i, i + 1 < d → rg r i < rg r (i + 1) := fun i hi =>
    Nat.le_of_ble_eq_true (CFSG.KC.Pack.allN_spec h2 i (by change i < d - 1; omega))
  have hlast : rg r (d - 1) < n := Nat.le_of_ble_eq_true h1
  have hlt : ∀ i < d, rg r i < n := by
    have key : ∀ k i, i + k = d - 1 → rg r i < n := by
      intro k
      induction k with
      | zero =>
        intro i hi
        obtain rfl : i = d - 1 := by omega
        exact hlast
      | succ k ih => exact fun i hi => lt_trans (hinc i (by omega)) (ih (i + 1) (by omega))
    exact fun i hi => key (d - 1 - i) i (by omega)
  have hbits : ∀ q, (D m).testBit q = true ↔ ∃ i < d, 48 * rg r i = q := by
    intro q
    rw [hD m hm q]
    constructor
    · rintro ⟨p, ⟨_, hp⟩, rfl⟩
      rw [← hmask, maskK_testBit hd, decide_eq_true_iff, decodeRow_eq, List.mem_map] at hp
      obtain ⟨i, hi, rfl⟩ := hp
      exact ⟨i, List.mem_range.1 hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨rg r i, ⟨by have := hlt i hi; omega, ?_⟩, rfl⟩
      rw [← hmask, maskK_testBit hd, decide_eq_true_iff, decodeRow_eq, List.mem_map]
      exact ⟨i, List.mem_range.2 hi, rfl⟩
  have hsum : ∑ i ∈ Finset.range d, 2 ^ (48 * rg r i) = D m := by
    apply Nat.eq_of_testBit_eq
    intro q
    have A := (testBit_sum_pow (f := fun i => 48 * rg r i) d
      (fun i hi => by have := hinc i hi; omega)).1 q
    apply Bool.eq_iff_iff.2
    rw [A, hbits]
  have hsp : spreadK d r = 2 ^ 128 * ∑ i ∈ Finset.range d, 2 ^ (48 * rg r i) + d := by
    rw [spreadK_eq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
      Nat.mul_one, Finset.mul_sum]
    simp only [pow_add]
  rw [Nat.beq_eq]
  change spreadK d r + (x + 1) = S x + d
  rw [hsp, hsum, hS]
  ring

end CFSG.KC.Fi22Snd

end
