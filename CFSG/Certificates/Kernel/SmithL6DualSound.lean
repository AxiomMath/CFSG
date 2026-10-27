module

public import Certificates.Data.Kernel.SmithL6Dual

public section

namespace CFSG.KC.SmithL6D

open CFSG.SmithL6 CFSG.KC.Sym6Sq

theorem strictA_eq {α : Type} (y : Nat) (k : Nat → α) : strictA y k = k y := by
  cases y <;> rfl

theorem forceA_eq {α : Type} (L : List Nat) (k : List Nat → α) : forceA L k = k L := by
  unfold forceA
  induction L generalizing k with
  | nil => rfl
  | cons x L ih =>
    rw [← ih (fun L' => k (x :: L'))]
    exact strictA_eq x _

theorem loopK_cons (T PM PA m : Nat) (LM : List Nat) (a : Nat) (LA : List Nat) (k : Nat) :
    loopK T PM PA (m :: LM) (a :: LA) k = (okK T PM PA k m a && loopK T PM PA LM LA (k + 1)) := by
  change (okK T PM PA k m a && strictA (Nat.succ k) (loopK T PM PA LM LA)) = _
  rw [strictA_eq]

theorem loopK_sound (T PM PA : Nat) : ∀ (LM LA : List Nat) (k : Nat),
    loopK T PM PA LM LA k = true → ∀ n (h : n < LM.length) (h' : n < LA.length),
      okK T PM PA (k + n) LM[n] LA[n] = true
  | [], _, _, _, n, h, _ => absurd h (Nat.not_lt_zero n)
  | _ :: _, [], _, _, n, _, h' => absurd h' (Nat.not_lt_zero n)
  | m :: LM, a :: LA, k, hl, n, h, h' => by
    rw [loopK_cons, Bool.and_eq_true] at hl
    cases n with
    | zero => exact hl.1
    | succ n =>
      have := loopK_sound T PM PA LM LA (k + 1) hl.2 n (by simpa using h) (by simpa using h')
      rw [Nat.add_assoc, Nat.add_comm 1 n] at this
      exact this

theorem okK_parts {T PM PA k m a : Nat} (h : okK T PM PA k m a = true) :
    lane11 T (m % hp) = k ∧ lane64 PM k = m ∧ lane64 PA k = a ∧
      lane11 T (a % hp) < 1395 ∧ lane64 PM (lane11 T (a % hp)) = a ∧
        lane64 PA (lane11 T (a % hp)) = m := by
  unfold okK at h
  rw [strictA_eq] at h
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2.1.1, h.2.1.2, h.2.2⟩

theorem dual_of_ok (T PM PA : Nat) (M A : Nat → Nat)
    (h : ∀ k < 1395, okK T PM PA k (M k) (A k) = true) (i : Nat) (hi : i < 1395) :
    lane11 T (A i % hp) < 1395 ∧ M (lane11 T (A i % hp)) = A i ∧
      A (lane11 T (A i % hp)) = M i ∧ ∀ k < 1395, M k = A i → k = lane11 T (A i % hp) := by
  obtain ⟨-, hMi, hAi, hj, hPM, hPA⟩ := okK_parts (h i hi)
  obtain ⟨-, hMj, hAj, -, -, -⟩ := okK_parts (h _ hj)
  refine ⟨hj, ?_, ?_, fun k hk hk' => ?_⟩
  · rw [← hMj, hPM]
  · rw [← hAj, hPA]
  · obtain ⟨hTk, -⟩ := okK_parts (h k hk)
    rw [← hTk, hk']

theorem find_range_unique (n j : Nat) (p : Nat → Bool) (hj : j < n) (hp : p j = true)
    (hu : ∀ k < n, p k = true → k = j) : ((List.range n).find? p).getD n = j := by
  cases h : (List.range n).find? p with
  | none =>
    have := List.find?_eq_none.1 h j (List.mem_range.2 hj)
    exact absurd hp this
  | some k =>
    exact hu k (List.mem_range.1 (List.mem_of_find?_eq_some h)) (List.find?_some h)

theorem wData_size : wData.size = 1395 := by
  decide +kernel

theorem maskArr_get (k : Nat) (hk : k < 1395) :
    maskArr[k]! = (wData.toList.map mskK)[k]! := by
  have hW : k < wData.size := by rw [wData_size]; exact hk
  rw [getElem!_pos maskArr k (by simp [maskArr]; exact hk),
    getElem!_pos (wData.toList.map mskK) k (by simpa using hW)]
  simp only [maskArr, Array.getElem_ofFn, List.getElem_map, Array.getElem_toList]
  unfold wMask wB mskK
  rw [getElem!_pos wData k hW]

theorem form_mod (φ x : Nat) (hφ : φ < 64) : form φ x = form φ (x % 64) := by
  unfold form
  congr 1
  apply Nat.eq_of_testBit_eq
  intro i
  have h64 : (64 : Nat) = 2 ^ 6 := rfl
  rw [Nat.testBit_and, Nat.testBit_and, h64, Nat.testBit_mod_two_pow]
  by_cases hi : i < 6
  · simp [hi]
  · have hle : (2 : Nat) ^ 6 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    have : φ.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (h64 ▸ hφ) hle)
    simp [this]

theorem fFB_holds : fFB = true := by
  decide +kernel

theorem form_fF (φ x : Nat) (hφ : φ < 64) (hx : x < 64) : form φ x = (fF x).testBit φ := by
  have h := fFB_holds
  unfold fFB at h
  rw [List.all_eq_true] at h
  have h' := h φ (List.mem_range.2 hφ)
  rw [List.all_eq_true] at h'
  exact beq_iff_eq.1 (h' x (List.mem_range.2 hx))

theorem foldl_bits (p : Nat → Bool) : ∀ n t,
    ((List.range n).foldl (fun acc φ => if p φ = true then acc ||| 2 ^ φ else acc) 0).testBit t =
      (decide (t < n) && p t)
  | 0, t => by simp
  | n + 1, t => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have ih := foldl_bits p n t
    by_cases hp : p n = true
    · rw [if_pos hp, Nat.testBit_or, ih, Nat.testBit_two_pow]
      by_cases h1 : t < n
      · have h2 : n ≠ t := by omega
        simp [h1, h2, Nat.lt_succ_of_lt h1]
      · by_cases h2 : n = t
        · subst h2
          simp [hp]
        · have h3 : ¬ t < n + 1 := by omega
          simp [h1, h2, h3]
    · rw [if_neg hp, ih]
      by_cases h1 : t < n
      · simp [h1, Nat.lt_succ_of_lt h1]
      · by_cases h2 : t = n
        · subst h2
          simp [hp]
        · have h3 : ¬ t < n + 1 := by omega
          simp [h1, h3]

theorem annK_eq (c : Nat) : annK c = annK2 c := by
  unfold annK annMaskOf
  change _ = gU ((fF (c % 64) ||| fF (c / 64 % 64)) ||| fF (c / 4096 % 64))
  have h1 : c % 64 < 64 := Nat.mod_lt _ (by decide)
  have h2 : c / 64 % 64 < 64 := Nat.mod_lt _ (by decide)
  have h3 : c / 4096 % 64 < 64 := Nat.mod_lt _ (by decide)
  have hM : (18446744073709551615 : Nat) = 2 ^ 64 - 1 := by decide
  apply Nat.eq_of_testBit_eq
  intro t
  rw [foldl_bits]
  unfold gU
  have ex : ∀ x y : Nat, Nat.xor x y = x ^^^ y := fun _ _ => rfl
  have ea : ∀ x y : Nat, Nat.land x y = x &&& y := fun _ _ => rfl
  rw [ex, ea, hM, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases ht : t < 64
  · rw [Nat.testBit_or, Nat.testBit_or, form_mod t (c / 4096) ht, form_fF t _ ht h1,
      form_fF t _ ht h2, form_fF t _ ht h3]
    simp [ht]
  · simp [ht]

theorem annArr_get (k : Nat) (hk : k < 1395) :
    annArr[k]! = (wData.toList.map annK2)[k]! := by
  have hW : k < wData.size := by rw [wData_size]; exact hk
  rw [getElem!_pos annArr k (by simp [annArr]; exact hk),
    getElem!_pos (wData.toList.map annK2) k (by simpa using hW)]
  simp only [annArr, Array.getElem_ofFn, List.getElem_map, Array.getElem_toList]
  rw [← annK_eq]
  unfold wB annK
  rw [getElem!_pos wData k hW]

theorem chkSwapPlanes_of (h : dualK wData.toList = true) : chkSwapPlanes = true := by
  unfold dualK at h
  rw [forceA_eq, forceA_eq, strictA_eq, strictA_eq, strictA_eq] at h
  generalize bldT (wData.toList.map mskK) = T at h
  generalize bldP (wData.toList.map mskK) = PM at h
  generalize bldP (wData.toList.map annK2) = PA at h
  have hok : ∀ k < 1395, okK T PM PA k ((wData.toList.map mskK)[k]!)
      ((wData.toList.map annK2)[k]!) = true := by
    intro k hk
    have hLM : k < (wData.toList.map mskK).length := by
      rw [List.length_map, Array.length_toList, wData_size]
      exact hk
    have hLA : k < (wData.toList.map annK2).length := by
      rw [List.length_map, Array.length_toList, wData_size]
      exact hk
    have := loopK_sound T PM PA _ _ 0 h k hLM hLA
    rw [Nat.zero_add] at this
    rw [getElem!_pos (wData.toList.map mskK) k hLM, getElem!_pos (wData.toList.map annK2) k hLA]
    exact this
  unfold chkSwapPlanes
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  obtain ⟨hj, hMj, hAj, hu⟩ := dual_of_ok T PM PA (fun k => (wData.toList.map mskK)[k]!)
    (fun k => (wData.toList.map annK2)[k]!) hok i hi
  have hd : dualIdx i = lane11 T ((wData.toList.map annK2)[i]! % hp) := by
    unfold dualIdx
    refine find_range_unique 1395 _ _ hj ?_ fun k hk hk' => hu k hk ?_
    · rw [maskArr_get _ hj, annArr_get _ hi, hMj]
      exact beq_self_eq_true _
    · rw [beq_iff_eq, maskArr_get _ hk, annArr_get _ hi] at hk'
      exact hk'
  dsimp only
  rw [hd, maskArr_get _ hj, annArr_get _ hi, annArr_get _ hj, maskArr_get _ hi, hMj, hAj]
  rw [decide_eq_true hj]
  simp only [beq_self_eq_true, Bool.and_self]

end CFSG.KC.SmithL6D
