
module

public import CFSG.Sporadic.Fi24.OrbitBase
public import CFSG.Certificates.Kernel.Spor.Fi24FixSound
public import CFSG.Certificates.Kernel.Spor.Mat3Sound

public section

namespace CFSG.KC.Fi24FixS

open CFSG.Sporadic.Fi24 CFSG.Sporadic.Fi24.Native CFSG.KC.Fi24FixK CFSG.KS.Mat3

@[expose] def digL : List Char :=
  ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J',
    'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'a', 'b', 'c', 'd',
    'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x',
    'y', 'z', '!', '#', '$', '%', '&', '(', ')', '*', '+', ',', '-', '.', '/', ':', ';', '<', '=', '>',
    '?']

theorem digits81_toList : digits81.toList = digL := by
  unfold digits81
  rw [String.toList_append]
  rfl

@[expose] def tblD (c : ℕ) : ℕ :=
  ((Array.range 128).map fun c => digL.idxOf (Char.ofNat c))[c]?.getD 0

set_option exponentiation.threshold 1000

theorem D81_lt : D81 < 2 ^ 896 := by decide +kernel

theorem d81_ge {c : ℕ} (hc : 128 ≤ c) : d81 c = 0 := by
  unfold d81
  change (D81 >>> (7 * c)) &&& 127 = 0
  have : D81 >>> (7 * c) = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (lt_of_lt_of_le D81_lt (Nat.pow_le_pow_right (by norm_num) (by omega)))
  rw [this, Nat.zero_and]

theorem d81_lt : ∀ c < 128, d81 c = digL.idxOf (Char.ofNat c) := by
  decide +kernel

theorem d81_eq (c : ℕ) : d81 c = tblD c := by
  rcases Nat.lt_or_ge c 128 with h | h
  · rw [d81_lt c h]
    unfold tblD
    simp [Array.getElem?_map, Array.getElem?_range, h]
  · rw [d81_ge h]
    unfold tblD
    rw [Array.getElem?_eq_none (by simpa using h)]
    rfl

@[expose] def dig4 (x : ℕ) : List ℕ := [x % 3, x / 3 % 3, x / 9 % 3, x / 27 % 3]

theorem foldl_push (f : Char → ℕ) : ∀ (l : List Char) (a : Array ℕ),
    (l.foldl (fun b ch => (((b.push (f ch % 3)).push (f ch / 3 % 3)).push (f ch / 9 % 3)).push
      (f ch / 27 % 3)) a).toList = a.toList ++ l.flatMap fun ch => dig4 (f ch)
  | [], a => by simp
  | ch :: l, a => by
    rw [List.foldl_cons, foldl_push f l, List.flatMap_cons]
    simp [dig4]

theorem decode81_toList (s : String) :
    (decode81 s).toList = s.toList.flatMap fun ch => dig4 (d81 ch.toNat) := by
  unfold decode81
  simp only [Id.run, bind_pure, List.forIn_pure_yield_eq_foldl, digits81_toList]
  have := foldl_push (fun ch => tblD ch.toNat) s.toList (Array.mkEmpty (4 * s.length))
  simp only [d81_eq]
  unfold tblD at this ⊢
  change Array.toList (List.foldl _ _ _) = _
  rw [this]
  simp

theorem flatMap_dig4 {f : Char → ℕ} : ∀ (l : List Char) (t s : ℕ), t < l.length → s < 4 →
    (l.flatMap fun ch => dig4 (f ch))[4 * t + s]? = some (f l[t]! / 3 ^ s % 3)
  | [], t, s, ht, _ => absurd ht (Nat.not_lt_zero t)
  | ch :: l, t, s, ht, hs => by
    rw [List.flatMap_cons]
    rcases t with _ | t
    · rw [List.getElem?_append_left (by simp [dig4]; omega)]
      interval_cases s <;> simp [dig4]
    · rw [List.getElem?_append_right (by simp [dig4]; omega)]
      have e : 4 * (t + 1) + s - (dig4 (f ch)).length = 4 * t + s := by simp [dig4]; omega
      rw [e, flatMap_dig4 l t s (by simp at ht; omega) hs]
      simp

theorem bv_trit (v : ℕ) (hv : v < 3) : bv (decide (v = 1)) (decide (v = 2)) = (v : ZMod 3) := by
  interval_cases v <;> rfl

theorem rowsWF_initRows : RowsWF (initRows ()) := by
  intro x hx
  unfold initRows at hx
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hx
  exact ofTrits_wf (by norm_num) _

theorem initRows_size : (initRows ()).size = 253 := by
  unfold initRows
  simp

theorem rowW_initRows_val {i j : ℕ} (hi : i < 253) (hj : j < 781) :
    (rowW (initRows ()) i).val j = ((if j < 253 then (if j = i then 1 else 0) else
      (decode81 initData)[528 * i + (j - 253)]?.getD 0 : ℕ) : ZMod 3) := by
  unfold rowW initRows
  rw [Array.getElem?_ofFn]
  simp only [hi, ↓reduceDIte]
  rw [Option.getD_some, ofTrits_val (by norm_num), if_pos hj]

theorem span_eq_pt_zero {R L : ℕ} {CT : ℕ → ℕ} {cs : List Char} (hL : L = 2 ^ 609961 - 1)
    (hcs : initData = String.ofList cs) (hd : digitsOK CT 33396 cs 0 = true)
    (hc : colsOK (Nat.land R L) (Nat.shiftRight R 609961) CT = true)
    (hr : rowsZOK (Nat.land R L) (Nat.shiftRight R 609961) = true) :
    LinearMap.range (mat3 781 609961 R).mulVecLin = (pt 0).sp := by
  obtain ⟨hlen, hCT⟩ := digitsOK_spec cs 0 hd
  simp only [Nat.zero_add] at hlen hCT
  have hb1 : ∀ p < 609961, (Nat.land R L).testBit p = R.testBit p := by
    intro p hp
    change (R &&& L).testBit p = _
    rw [Nat.testBit_and, hL, Nat.testBit_two_pow_sub_one]
    simp [hp]
  have hb2 : ∀ p, (Nat.shiftRight R 609961).testBit p = R.testBit (609961 + p) := by
    intro p
    change (R >>> 609961).testBit p = _
    rw [Nat.testBit_shiftRight]
  have hcol := colsOK_spec hc
  have hrow := rowsZOK_spec hr
  have hent : ∀ j i : Fin 781, mat3 781 609961 R j i =
      if (i : ℕ) < 253 then (rowW (initRows ()) i).val j else 0 := by
    intro j i
    have hp : 781 * j.val + i.val < 609961 := by omega
    unfold mat3
    rw [← hb1 _ hp, ← hb2]
    by_cases hi : i.val < 253
    · rw [if_pos hi, rowW_initRows_val hi j.isLt]
      by_cases hj : j.val < 253
      · obtain ⟨a, b⟩ := (hrow j j.isLt i i.isLt).1 hj
        rw [a, b, if_pos hj]
        by_cases e : i.val = j.val
        · simp [e, bv]
        · simp [e, Ne.symm e, bv]
      · rw [if_neg hj]
        have hj' : j.val - 253 < 528 := by omega
        obtain ⟨a, b⟩ := hcol (j.val - 253) hj' i hi
        have e1 : 781 * (253 + (j.val - 253)) + i.val = 781 * j.val + i.val := by omega
        rw [e1] at a b
        rw [a, b, bv_trit _ (Nat.mod_lt _ (by norm_num))]
        have ht : 132 * i.val + (j.val - 253) / 4 < cs.length := by omega
        have e2 : 528 * i.val + (j.val - 253) = 4 * (132 * i.val + (j.val - 253) / 4) +
            (j.val - 253) % 4 := by omega
        rw [e2, Array.getElem?_toList.symm.trans rfl, decode81_toList, hcs, String.toList_ofList,
          flatMap_dig4 cs _ _ ht (Nat.mod_lt _ (by norm_num)), Option.getD_some, hCT _ ht]
    · rw [if_neg hi]
      by_cases hj : j.val < 253
      · obtain ⟨a, b⟩ := (hrow j j.isLt i i.isLt).1 hj
        have e : i.val ≠ j.val := by omega
        rw [a, b]
        simp [e, bv]
      · obtain ⟨a, b⟩ := (hrow j j.isLt i i.isLt).2 (by omega) (by omega)
        rw [a, b]
        rfl
  rw [Matrix.range_mulVecLin]
  have hpt : (pt 0).sp = rowSpan 253 (initRows ()) := by
    change rowSpan 253 (formAt gensT orb rootForm 0).rows = _
    rw [formAt_zero]
    have := (rref_spec 781 rowsWF_initRows).2.2
    rw [initRows_size] at this
    exact this
  rw [hpt, rowSpan]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : i.val < 253
    · have e : (mat3 781 609961 R).col i = vecW (rowW (initRows ()) i.val) := by
        funext j
        change mat3 781 609961 R j i = _
        rw [hent, if_pos hi]
        rfl
      rw [e]
      exact Submodule.subset_span ⟨⟨i.val, hi⟩, rfl⟩
    · have e : (mat3 781 609961 R).col i = 0 := by
        funext j
        change mat3 781 609961 R j i = _
        rw [hent, if_neg hi]
        rfl
      rw [e]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have e : vecW (rowW (initRows ()) i.val) = (mat3 781 609961 R).col ⟨i.val, by omega⟩ := by
      funext j
      change _ = mat3 781 609961 R j ⟨i.val, by omega⟩
      rw [hent, if_pos i.isLt]
      rfl
    beta_reduce
    rw [e]
    exact Submodule.subset_span ⟨_, rfl⟩

end CFSG.KC.Fi24FixS

end
