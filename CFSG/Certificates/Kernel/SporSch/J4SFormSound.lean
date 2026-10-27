module

public import CFSG.Certificates.Kernel.SporSch.J4SBigSound
public import CFSG.Sporadic.Schreier.J4SFormData
import CFSG.Sporadic.J4.F2Spec
import CFSG.Sporadic.HS.SmallF2Spec

public section

namespace CFSG.KS.SporSch.J4B

open CFSG.KC.J4Q CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native

@[expose] noncomputable def lowJ : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r acc => Nat.lor acc (Nat.shiftLeft (Nat.sub (Nat.shiftLeft (nat_lit 1) r) (nat_lit 1))
      (Nat.mul (nat_lit 128) r))) (nat_lit 112)

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

private theorem row_lt' {X : Array Nat} (hX : WfN X) (i : Nat) : X[i]?.getD 0 < 2 ^ 112 := by
  by_cases h : i < X.size
  · have := hX.2 i (hX.1 ▸ h)
    rw [getElem!_pos X i h] at this
    rwa [getElem?_pos X i h, Option.getD_some]
  · rw [getElem?_neg X i h, Option.getD_none]
    exact Nat.two_pow_pos _

private theorem wf_of_rows {X : Array Nat} (hs : X.size = 112) (h : ∀ i < 112, X[i]?.getD 0 < 2 ^ 112) :
    WfN X := ⟨hs, fun i hi => by
  have := h i hi
  rwa [getElem?_pos X i (hs ▸ hi), Option.getD_some, ← getElem!_pos X i (hs ▸ hi)] at this⟩

private theorem bit_foldr (R : Nat → Nat) (p : Nat) : ∀ l : List Nat,
    (l.foldr (fun i acc => Nat.lor (Nat.shiftLeft (R i) (128 * i)) acc) 0).testBit p =
      l.any fun i => (decide (128 * i ≤ p) && (R i).testBit (p - 128 * i))
  | [] => by simp
  | i :: l => by
    rw [List.foldr_cons, List.any_cons, ← bit_foldr R p l]
    change ((R i <<< (128 * i)) ||| _).testBit p = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]

theorem encN_bit {X : Array Nat} (hX : WfN X) (p : Nat) :
    (encN X).testBit p = (decide (p / 128 < 112) && (X[p / 128]?.getD 0).testBit (p % 128)) := by
  unfold encN
  rw [bit_foldr]
  simp only [Array.getD_eq_getD_getElem?]
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    have hq : p - 128 * i < 112 := by
      by_contra hc
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (row_lt' hX i)
        (Nat.pow_le_pow_right (by omega) (by omega)))] at h2
      exact Bool.false_ne_true h2
    have e1 : p / 128 = i := by omega
    have e2 : p % 128 = p - 128 * i := by omega
    rw [e1, e2]
    exact ⟨hi, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨p / 128, h1, by omega, ?_⟩
    have e2 : p - 128 * (p / 128) = p % 128 := by omega
    rw [e2]
    exact h2

theorem xor_enc {X Y : Array Nat} (_hX : WfN X) (_hY : WfN Y) :
    WfN (xorRows112 X Y) ∧ encN (xorRows112 X Y) = Nat.xor (encN X) (encN Y) := by
  have hr : ∀ i < 112, (xorRows112 X Y)[i]?.getD 0 = X[i]?.getD 0 ^^^ Y[i]?.getD 0 := by
    intro i hi
    simp [xorRows112, hi]
  have hW : WfN (xorRows112 X Y) := wf_of_rows (by simp [xorRows112]) fun i hi => by
    rw [hr i hi]
    exact Nat.xor_lt_two_pow (row_lt' _hX i) (row_lt' _hY i)
  refine ⟨hW, ?_⟩
  change _ = encN X ^^^ encN Y
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_xor, encN_bit hW, encN_bit _hX, encN_bit _hY]
  by_cases hq : p / 128 < 112
  · simp [hq, hr _ hq, Nat.testBit_xor]
  · simp [hq]

private theorem low_bit : ∀ m, m ≤ 112 → ∀ p,
    (Nat.rec (motive := fun _ => Nat) 0
      (fun r acc => acc ||| ((1 <<< r) - 1) <<< (128 * r)) m).testBit p =
      (decide (p / 128 < m) && decide (p % 128 < p / 128))
  | 0, _, p => by simp
  | m + 1, hm, p => by
    change ((Nat.rec (motive := fun _ => Nat) 0
      (fun r acc => acc ||| ((1 <<< r) - 1) <<< (128 * r)) m) |||
        ((1 <<< m) - 1) <<< (128 * m)).testBit p = _
    rw [Nat.testBit_or, low_bit m (by omega) p, Nat.testBit_shiftLeft, Nat.one_shiftLeft,
      Nat.testBit_two_pow_sub_one, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ge_iff_le]
    omega

private theorem lowJ_bit (p : Nat) :
    lowJ.testBit p = (decide (p / 128 < 112) && decide (p % 128 < p / 128)) :=
  low_bit 112 (Nat.le_refl _) p

theorem lower_enc {X : Array Nat} (_hX : WfN X) :
    WfN (lowerRows X) ∧ encN (lowerRows X) = Nat.land (encN X) lowJ := by
  have hr : ∀ i < 112, (lowerRows X)[i]?.getD 0 = X[i]?.getD 0 % 2 ^ i := by
    intro i hi
    simp [lowerRows, hi]
  have hW : WfN (lowerRows X) := wf_of_rows (by simp [lowerRows]) fun i hi => by
    rw [hr i hi]
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos i))
      (Nat.pow_le_pow_right (by omega) (by omega))
  refine ⟨hW, ?_⟩
  change _ = encN X &&& lowJ
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_and, encN_bit hW, encN_bit _hX, lowJ_bit]
  by_cases hq : p / 128 < 112
  · rw [hr _ hq, Nat.testBit_mod_two_pow]
    cases (X[p / 128]?.getD 0).testBit (p % 128) <;> simp [hq]
  · simp [hq]

theorem beq_enc {X Y : Array Nat} (_hX : WfN X) (_hY : WfN Y) :
    (X == Y) = Nat.beq (encN X) (encN Y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]
  exact ⟨fun h => h ▸ rfl, enc_inj _hX _hY⟩


section Proofs

open CFSG.KC.J4Q CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

theorem row_lt_tr {X : Array Nat} (hX : WfN X) (i : Nat) : X[i]?.getD 0 < 2 ^ 112 := by
  by_cases h : i < X.size
  · have := hX.2 i (hX.1 ▸ h)
    rw [getElem!_pos X i h] at this
    rwa [getElem?_pos X i h, Option.getD_some]
  · rw [getElem?_neg X i h, Option.getD_none]
    exact Nat.two_pow_pos _

theorem wf_of_rows_tr {X : Array Nat} (hs : X.size = 112)
    (h : ∀ i < 112, X[i]?.getD 0 < 2 ^ 112) : WfN X := ⟨hs, fun i hi => by
  have := h i hi
  rwa [getElem?_pos X i (hs ▸ hi), Option.getD_some, ← getElem!_pos X i (hs ▸ hi)] at this⟩

open CFSG.Sporadic.J4.Native (V2) in
theorem v2N_bit (a : V2) {j : Nat} (hj : j < 128) : (v2N a).testBit j = a.testBit j := by
  rw [← CFSG.Sporadic.J4.Native.V2.testBit_toNat a hj]
  congr 1
  apply Nat.eq_of_testBit_eq
  intro k
  change (a.lo.toNat ||| a.hi.toNat <<< 64).testBit k =
    (a.lo.toNat + 2 ^ 64 * a.hi.toNat).testBit k
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ (UInt64.toNat_lt _), Nat.testBit_or,
    Nat.testBit_shiftLeft]
  by_cases hk : k < 64
  · simp [hk]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (UInt64.toNat_lt a.lo)
      (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [hk, Nat.le_of_not_lt hk]

theorem mapRow_bit (X : Array Nat) (i : Nat) {q : Nat} (hq : q < 128) :
    (v2N ((X.map ofN)[i]?.getD CFSG.Sporadic.J4.Native.V2.zero)).testBit q =
      (X[i]?.getD 0).testBit q := by
  rw [Array.getElem?_map]
  cases X[i]? with
  | none =>
    rw [Option.map_none, Option.getD_none, Option.getD_none, v2N_zero]
  | some x =>
    rw [Option.map_some, Option.getD_some, Option.getD_some, ofN_bits]
    simp [hq]

theorem wfA_map {X : Array Nat} (hX : WfN X) : WfA (X.map ofN) := by
  refine ⟨by rw [Array.size_map, hX.1], Array.all_eq_true.mpr fun i hi => ?_⟩
  rw [Array.getElem_map]
  have hi' : i < X.size := by simpa using hi
  have := row_lt_tr hX i
  rw [getElem?_pos X i hi', Option.getD_some] at this
  exact wf_ofN this

theorem encN_eq_encR {X : Array Nat} (hX : WfN X) : encN X = encR (X.map ofN) := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [encN_bit hX, encR_bit, mapRow_bit X _ (Nat.mod_lt _ (by omega))]

theorem tr_enc_proved (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X : Array Nat}
    (_hX : WfN X) :
    WfN (transposeRows 112 X) ∧ encN (transposeRows 112 X) = trJ t0 t1 t2 t3 t4 t5 t6 (encN X) := by
  have hr : ∀ r < 112, (transposeRows 112 X)[r]?.getD 0 =
      ofBits 112 fun i => (X[i]?.getD 0).testBit r := by
    intro r hr
    simp [transposeRows, hr]
  have hW : WfN (transposeRows 112 X) := wf_of_rows_tr (by simp [transposeRows]) fun r hr' => by
    rw [hr r hr']
    exact CFSG.Sporadic.SmallF2.ofBits_lt _ _
  refine ⟨hW, ?_⟩
  rw [encN_eq_encR _hX, ← enc_transposeRows _hK (wfA_map _hX)]
  apply Nat.eq_of_testBit_eq
  intro p
  rw [encN_bit hW, encR_bit]
  by_cases hq : p / 128 < 112
  · have hm : p % 128 < 128 := Nat.mod_lt _ (by omega)
    have hT : (CFSG.Sporadic.J4.Native.transposeRows (X.map ofN))[p / 128]?.getD
        CFSG.Sporadic.J4.Native.V2.zero = CFSG.Sporadic.J4.Native.V2.ofFn fun i =>
          ((X.map ofN)[i]?.getD CFSG.Sporadic.J4.Native.V2.zero).testBit (p / 128) := by
      simp [CFSG.Sporadic.J4.Native.transposeRows, hq]
    rw [hr _ hq, CFSG.Sporadic.SmallF2.ofBits_testBit, hT, v2N_bit _ hm]
    by_cases hm2 : p % 128 < 112
    · rw [CFSG.Sporadic.J4.Native.V2.ofFn_testBit _ hm2, ← v2N_bit (j := p / 128) _ (by omega),
        mapRow_bit X _ (by omega)]
      simp [hq, hm2]
    · rw [(CFSG.Sporadic.J4.Native.V2.wf_iff_testBit _).1
        (CFSG.Sporadic.J4.Native.V2.ofFn_wf _) _ (by omega) hm]
      simp [hm2]
  · simp [hq]

end Proofs

theorem tr_enc (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X : Array Nat} (_hX : WfN X) :
    WfN (transposeRows 112 X) ∧ encN (transposeRows 112 X) = trJ t0 t1 t2 t3 t4 t5 t6 (encN X) :=
  tr_enc_proved _hK _hX

end CFSG.KS.SporSch.J4B

end
