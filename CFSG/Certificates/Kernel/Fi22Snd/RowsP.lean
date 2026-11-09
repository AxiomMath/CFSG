module

public import Certificates.Data.Kernel.Fi22Nbr3153M
public import CFSG.Certificates.Kernel.Fi22Snd.RowsW
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KC.Fi22Snd

open CFSG.KC.Enum CFSG.KC.N3153

theorem mod48_count : ∀ k Z, Z < 2 ^ (48 * k) → (∀ q, Z.testBit q = true → 48 ∣ q) →
    Z ≡ ∑ p ∈ Finset.range k, (if Z.testBit (48 * p) = true then 1 else 0) [MOD 2 ^ 48 - 1]
  | 0, Z, hZ, _ => by
    have : Z = 0 := by simpa using hZ
    subst this
    rfl
  | k + 1, Z, hZ, hb => by
    have hb48 : Z % 2 ^ 48 < 2 ^ 48 := Nat.mod_lt _ (by positivity)
    have hZe : Z = 2 ^ 48 * (Z / 2 ^ 48) + Z % 2 ^ 48 := (Nat.div_add_mod Z _).symm
    have hbit : ∀ j, Z.testBit (48 + j) = (Z / 2 ^ 48).testBit j := fun j => by
      conv_lhs => rw [hZe]
      rw [Nat.testBit_two_pow_mul_add _ hb48, if_neg (by omega), Nat.add_sub_cancel_left]
    have hlow : ∀ j, (Z % 2 ^ 48).testBit j = true → j = 0 := by
      intro j hj
      have hj48 : j < 48 := by
        by_contra hj'
        rw [testBit_ge hb48 (by omega)] at hj
        exact Bool.noConfusion hj
      have h1 : Z.testBit j = true := by
        rw [hZe, Nat.testBit_two_pow_mul_add _ hb48, if_pos hj48]
        exact hj
      have := hb j h1
      omega
    have hle : Z % 2 ^ 48 ≤ 1 := by
      have e : Z % 2 ^ 48 = Z % 2 ^ 48 % 2 ^ 1 := by
        apply Nat.eq_of_testBit_eq
        intro j
        conv_rhs => rw [Nat.testBit_mod_two_pow]
        by_cases hj : j < 1
        · simp [hj]
        · cases h : (Z % 2 ^ 48).testBit j
          · simp
          · exact absurd (hlow j h) (by omega)
      rw [e]
      exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    have hZ' : Z / 2 ^ 48 < 2 ^ (48 * k) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      have e : 48 * k + 48 = 48 * (k + 1) := by ring
      rw [e]
      exact hZ
    have hb' : ∀ q, (Z / 2 ^ 48).testBit q = true → 48 ∣ q := by
      intro q hq
      rw [← hbit] at hq
      have := hb _ hq
      omega
    have ih := mod48_count k _ hZ' hb'
    have h0 : (if Z.testBit (48 * 0) = true then 1 else 0) = Z % 2 ^ 48 := by
      have e : Z.testBit 0 = (Z % 2 ^ 48).testBit 0 := by
        conv_lhs => rw [hZe]
        have h048 : 0 < 48 := by norm_num
        rw [Nat.testBit_two_pow_mul_add _ hb48, if_pos h048]
      rw [Nat.mul_zero, e]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h | h <;> rw [h] <;> rfl
    rw [Finset.sum_range_succ', h0]
    have hs : ∀ p ∈ Finset.range k, (if Z.testBit (48 * (p + 1)) = true then 1 else 0) =
        (if (Z / 2 ^ 48).testBit (48 * p) = true then 1 else 0) := by
      intro p _
      have e : 48 * (p + 1) = 48 + 48 * p := by ring
      rw [e, hbit]
    rw [Finset.sum_congr rfl hs]
    have h48 : 2 ^ 48 ≡ 1 [MOD 2 ^ 48 - 1] := Nat.modEq_sub (by norm_num)
    calc Z = 2 ^ 48 * (Z / 2 ^ 48) + Z % 2 ^ 48 := hZe
      _ ≡ 1 * (Z / 2 ^ 48) + Z % 2 ^ 48 [MOD 2 ^ 48 - 1] :=
        Nat.ModEq.add_right _ (Nat.ModEq.mul_right _ h48)
      _ = Z / 2 ^ 48 + Z % 2 ^ 48 := by rw [Nat.one_mul]
      _ ≡ _ [MOD 2 ^ 48 - 1] := Nat.ModEq.add_right _ ih

@[expose] def ones16 : Nat → Nat
  | 0 => 0
  | k + 1 => 1 + 65536 * ones16 k

theorem ones16_eq (k : Nat) : (2 ^ (16 * k) - 1) / 65535 = ones16 k := by
  have h : ∀ k, 65535 * ones16 k + 1 = 2 ^ (16 * k) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      have e : 16 * (k + 1) = 16 * k + 16 := by ring
      rw [e, pow_add, ← ih, ones16]
      ring
  rw [← h k, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by norm_num)]

theorem ones16_bit : ∀ k i, i < k → (32768 * ones16 k).testBit (16 * i + 15) = true
  | 0, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, i, hi => by
    have e : 32768 * ones16 (k + 1) = 2 ^ 16 * (32768 * ones16 k) + 32768 := by
      rw [ones16]
      ring
    rw [e, Nat.testBit_two_pow_mul_add _ (by norm_num)]
    rcases i with _ | i
    · rfl
    · have e' : 16 * (i + 1) + 15 - 16 = 16 * i + 15 := by omega
      rw [ite_eq_right (by omega), e']
      exact ones16_bit k i (by omega)

theorem pow16_succ (i : Nat) : 2 ^ (16 * (i + 1)) = 65536 * 2 ^ (16 * i) := by
  have e : 16 * (i + 1) = 16 + 16 * i := by ring
  rw [e, pow_add]
  rfl

theorem sortCore16 : ∀ k A B, (∀ i < k, A / 2 ^ (16 * i) % 65536 < 32768) →
    (∀ i < k, B / 2 ^ (16 * i) % 65536 < 32768) →
    A % 2 ^ (16 * k) + ones16 k ≤ 32768 * ones16 k + B % 2 ^ (16 * k) ∧
    ∀ i < k, (32768 * ones16 k + B % 2 ^ (16 * k) - (A % 2 ^ (16 * k) + ones16 k)).testBit
      (16 * i + 15) = true → A / 2 ^ (16 * i) % 65536 < B / 2 ^ (16 * i) % 65536
  | 0, _, _, _, _ => ⟨by simp [ones16, Nat.mod_one], fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | k + 1, A, B, ha, hb => by
    have hdiv : ∀ X i, X / 2 ^ (16 * (i + 1)) = X / 65536 / 2 ^ (16 * i) := fun X i => by
      rw [pow16_succ, Nat.div_div_eq_div_mul]
    have ih := sortCore16 k (A / 65536) (B / 65536)
      (fun i hi => by rw [← hdiv]; exact ha (i + 1) (by omega))
      (fun i hi => by rw [← hdiv]; exact hb (i + 1) (by omega))
    have ha0 : A % 65536 < 32768 := by simpa using ha 0 (by omega)
    have hb0 : B % 65536 < 32768 := by simpa using hb 0 (by omega)
    have hA : A % 2 ^ (16 * (k + 1)) = A % 65536 + 65536 * (A / 65536 % 2 ^ (16 * k)) := by
      rw [pow16_succ, Nat.mod_mul]
    have hB : B % 2 ^ (16 * (k + 1)) = B % 65536 + 65536 * (B / 65536 % 2 ^ (16 * k)) := by
      rw [pow16_succ, Nat.mod_mul]
    obtain ⟨ih1, ih2⟩ := ih
    have hX : 32768 * ones16 (k + 1) + B % 2 ^ (16 * (k + 1)) -
        (A % 2 ^ (16 * (k + 1)) + ones16 (k + 1)) =
        2 ^ 16 * (32768 * ones16 k + B / 65536 % 2 ^ (16 * k) -
          (A / 65536 % 2 ^ (16 * k) + ones16 k)) + (32768 + B % 65536 - (A % 65536 + 1)) := by
      rw [hA, hB, ones16]
      norm_num
      omega
    refine ⟨by rw [hA, hB, ones16]; omega, fun i hi hbit => ?_⟩
    rw [hX, Nat.testBit_two_pow_mul_add _ (by norm_num; omega)] at hbit
    rcases i with _ | i
    · rw [ite_eq_left (by omega), Nat.testBit_eq_decide_div_mod_eq] at hbit
      have := of_decide_eq_true hbit
      simp only [Nat.mul_zero, pow_zero, Nat.div_one]
      norm_num at this
      omega
    · have e' : 16 * (i + 1) + 15 - 16 = 16 * i + 15 := by omega
      rw [ite_eq_right (by omega), e'] at hbit
      rw [hdiv, hdiv]
      exact ih2 i (by omega) hbit

theorem sortK16_spec {k r : Nat} (hb : ∀ i < k, rg r i < 32768 ∧ rg r (i + 1) < 32768)
    (h : sortK16 k r = true) : ∀ i < k, rg r i < rg r (i + 1) := by
  have hrg : ∀ X i, rg X i = X / 2 ^ (16 * i) % 65536 := fun X i => by
    change (X >>> (16 * i)) &&& (2 ^ 16 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have hrg1 : ∀ i, rg r (i + 1) = r / 65536 / 2 ^ (16 * i) % 65536 := fun i => by
    rw [hrg, pow16_succ, Nat.div_div_eq_div_mul]
  unfold sortK16 at h
  rw [CFSG.KC.Pack.strictB_eq, CFSG.KC.Pack.strictB_eq, CFSG.KC.Pack.strictB_eq] at h
  have h' := Nat.eq_of_beq_eq_true h
  change ((32768 * ((1 <<< (16 * k) - 1) / 65535) + (r >>> 16) % (1 <<< (16 * k)) -
    (r % (1 <<< (16 * k)) + (1 <<< (16 * k) - 1) / 65535)) &&&
    (32768 * ((1 <<< (16 * k) - 1) / 65535))) = 32768 * ((1 <<< (16 * k) - 1) / 65535) at h'
  have e16 : (2 : Nat) ^ 16 = 65536 := by norm_num
  rw [Nat.one_shiftLeft, ones16_eq, Nat.shiftRight_eq_div_pow, e16] at h'
  obtain ⟨-, hc⟩ := sortCore16 k r (r / 65536)
    (fun i hi => by rw [← hrg]; exact (hb i hi).1)
    (fun i hi => by rw [← hrg1]; exact (hb i hi).2)
  intro i hi
  rw [hrg, hrg1]
  apply hc i hi
  have hg := ones16_bit k i hi
  rw [← h', Nat.testBit_and] at hg
  exact (Bool.and_eq_true_iff.1 hg).1

theorem rowOKW_of_P {n d : Nat} {R M S D : Nat → Nat} (hD : DilOK D) {x : Nat}
    (h : rowOKP n d R M S D x = true) : rowOKW n d R M S D x = true := by
  unfold rowOKP at h
  rw [CFSG.KC.Pack.strictB_eq, CFSG.KC.Pack.strictB_eq, CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h1, h'⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h2, h''⟩ := CFSG.KC.Pack.band_iff.1 h'
  obtain ⟨h3, h'''⟩ := CFSG.KC.Pack.band_iff.1 h''
  obtain ⟨h4, h''''⟩ := CFSG.KC.Pack.band_iff.1 h'''
  obtain ⟨h5, h6⟩ := CFSG.KC.Pack.band_iff.1 h''''
  unfold rowOKW
  rw [CFSG.KC.Pack.strictB_eq, CFSG.KC.Pack.strictB_eq]
  set r := R x with hr
  set m := M x with hmd
  have hm : m < 2 ^ 4096 := by
    have := Nat.le_of_ble_eq_true h4
    change m + 1 ≤ 1 <<< 4096 at this
    rw [Nat.one_shiftLeft] at this
    omega
  have hmem : ∀ i < d, m.testBit (rg r i) = true := fun i hi => by
    rw [← beq_bit]
    exact CFSG.KC.Pack.allN_spec h3 i hi
  have hent : ∀ i < d, rg r i < 4096 := fun i hi => by
    by_contra hc
    have := hmem i hi
    rw [testBit_ge hm (by omega)] at this
    exact Bool.noConfusion this
  have hinc : ∀ i, i + 1 < d → rg r i < rg r (i + 1) := fun i hi =>
    sortK16_spec (k := d - 1) (fun j hj => ⟨by have := hent j (by omega); omega,
      by have := hent (j + 1) (by omega); omega⟩) h2 i (by omega)
  refine CFSG.KC.Pack.band_iff.2 ⟨h1, CFSG.KC.Pack.band_iff.2
    ⟨CFSG.KS.PackFld.allN_of_forall fun i hi => Nat.blt_eq.mpr (hinc i (by
      change i < d - 1 at hi
      omega)), CFSG.KC.Pack.band_iff.2 ⟨?_, CFSG.KC.Pack.band_iff.2 ⟨h4, h6⟩⟩⟩⟩
  have hstrict : ∀ i j, i < j → j < d → rg r i < rg r j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hij | rfl
      · exact lt_trans (ih hij (by omega)) (hinc j (by omega))
      · exact hinc i (by omega)
  have hd : d ≤ 4096 := by
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · omega
    have key : ∀ i < d, i ≤ rg r i := by
      intro i hi
      induction i with
      | zero => exact Nat.zero_le _
      | succ i ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih (by omega)) (hinc i hi))
    have := key (d - 1) (by omega)
    have := hent (d - 1) (by omega)
    omega
  set Dm := D m with hDm
  have hDbit : ∀ p < 4096, Dm.testBit (48 * p) = m.testBit p := by
    intro p hp
    apply Bool.eq_iff_iff.2
    rw [hD m hm]
    constructor
    · rintro ⟨p', ⟨_, hp'⟩, e⟩
      obtain rfl : p = p' := by omega
      exact hp'
    · intro hb
      exact ⟨p, ⟨hp, hb⟩, rfl⟩
  have hDlt : Dm < 2 ^ (48 * 4096) := by
    apply Nat.lt_pow_two_of_testBit
    intro q hq
    cases hb : Dm.testBit q
    · rfl
    · obtain ⟨p, ⟨hp, _⟩, rfl⟩ := (hD m hm q).1 hb
      omega
  have hDdvd : ∀ q, Dm.testBit q = true → 48 ∣ q := by
    intro q hq
    obtain ⟨p, -, rfl⟩ := (hD m hm q).1 hq
    exact Dvd.intro p rfl
  have hcong := mod48_count 4096 Dm hDlt hDdvd
  rw [Finset.sum_congr rfl (fun p hp => by rw [hDbit p (Finset.mem_range.1 hp)])] at hcong
  set B := (Finset.range 4096).filter (fun p => m.testBit p = true) with hB
  have hcard : B.card = d := by
    have h5' : Dm % (2 ^ 48 - 1) = d := Nat.eq_of_beq_eq_true h5
    rw [hB, Finset.card_filter]
    have hle : ∑ p ∈ Finset.range 4096, (if m.testBit p = true then 1 else 0) ≤ 4096 := by
      calc _ ≤ ∑ p ∈ Finset.range 4096, 1 := Finset.sum_le_sum (fun p _ => by split <;> omega)
        _ = 4096 := by simp
    have := hcong
    unfold Nat.ModEq at this
    rw [h5', Nat.mod_eq_of_lt (by omega)] at this
    omega
  set A := (Finset.range d).image (rg r) with hA
  have hAcard : A.card = d := by
    rw [hA, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj e
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    rcases lt_trichotomy i j with hij | hij | hij
    · exact absurd e (ne_of_lt (hstrict i j hij hj'))
    · exact hij
    · exact absurd e (ne_of_gt (hstrict j i hij hi'))
  have hAB : A ⊆ B := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hq
    have hi' := Finset.mem_range.1 hi
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hent i hi'), hmem i hi'⟩
  have hEq : A = B := Finset.eq_of_subset_of_card_le hAB (by rw [hcard, hAcard])
  rw [Nat.beq_eq]
  apply Nat.eq_of_testBit_eq
  intro q
  rw [maskK_testBit (by omega), decodeRow_eq]
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_iff, List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hmem i (List.mem_range.1 hi)
  · intro hq
    have hq4 : q < 4096 := by
      by_contra hc
      rw [testBit_ge hm (by omega)] at hq
      exact Bool.noConfusion hq
    have : q ∈ A := by
      rw [hEq]
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hq4, hq⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 this
    exact ⟨i, List.mem_range.2 (Finset.mem_range.1 hi), rfl⟩

end CFSG.KC.Fi22Snd

end
