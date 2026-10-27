module

public import CFSG.Certificates.Kernel.WordRelK.Bits

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.WordRelK

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Visible CFSG.Monster.B CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Sp8.WordRel

private theorem pairN_zero_right (a : Nat) : Model.pairN a 0 = false := by
  simp only [Model.pairN, Nat.and_zero]
  rfl

private theorem pairN_zero_left (d : Nat) : Model.pairN 0 d = false := by
  simp only [Model.pairN, Nat.zero_and]
  rfl

private theorem mul_T (u t : Nat) :
    Model.Pauli.mul (false, u, 0) (false, t, 0) = (false, u ^^^ t, 0) := by
  simp only [Model.Pauli.mul, Model.Pauli.s, Model.Pauli.a, Model.Pauli.d, pairN_zero_right,
    Bool.xor_false, Nat.xor_zero]

private theorem mul_D (u t : Nat) :
    Model.Pauli.mul (false, 0, u) (false, 0, t) = (false, 0, u ^^^ t) := by
  simp only [Model.Pauli.mul, Model.Pauli.s, Model.Pauli.a, Model.Pauli.d, pairN_zero_left,
    Bool.xor_false, Nat.xor_zero]

private theorem mul_split (s : Bool) (a d : Nat) :
    Model.Pauli.mul (Model.Pauli.mul (s, 0, 0) (false, a, 0)) (false, 0, d) = (s, a, d) := by
  simp only [Model.Pauli.mul, Model.Pauli.s, Model.Pauli.a, Model.Pauli.d, pairN_zero_right,
    pairN_zero_left, Bool.xor_false, Nat.zero_xor, Nat.xor_zero]

private theorem mod_two_pow_succ (a n : Nat) :
    a % 2 ^ (n + 1) = a % 2 ^ n ^^^ (if a.testBit n then 2 ^ n else 0) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  split
  · rw [Nat.testBit_two_pow]
    rcases Nat.lt_trichotomy i n with h | rfl | h
    · simp [h, Nat.lt_succ_of_lt h, Nat.ne_of_gt h]
    · simp_all
    · simp [show ¬ i < n + 1 by omega, show ¬ i < n by omega, show n ≠ i by omega]
  · simp only [Nat.zero_testBit, Bool.xor_false]
    rcases Nat.lt_trichotomy i n with h | rfl | h
    · simp [h, Nat.lt_succ_of_lt h]
    · simp_all
    · simp [show ¬ i < n + 1 by omega, show ¬ i < n by omega]

@[expose] def applyN (n acc yb rb : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun acc _ _ => acc)
    (fun _ ih acc yb rb =>
      ih (bif Nat.beq (yb % 2) 1 then mulP acc (rb % 33554432) else acc) (yb / 2)
        (rb / 33554432))
    n acc yb rb

theorem applyRow_eq (row y : Nat) :
    applyRow row y = applyN 24 (y / 16777216 * 16777216) (y % 16777216) row := rfl

theorem applyN_succ (n acc yb rb : Nat) : applyN (n + 1) acc yb rb =
    applyN n (bif Nat.beq (yb % 2) 1 then mulP acc (rb % 33554432) else acc) (yb / 2)
      (rb / 33554432) := rfl

section Hom

variable {G : Type*} [Group G] (φ : Model.Pauli → G)
  (hφ : ∀ x y, φ (Model.Pauli.mul x y) = φ x * φ y)

include hφ

theorem hom_one : φ (false, 0, 0) = 1 := by
  have h : Model.Pauli.mul (false, 0, 0) (false, 0, 0) = (false, 0, 0) := by decide
  have h2 : φ (false, 0, 0) * φ (false, 0, 0) = φ (false, 0, 0) * 1 := by
    rw [mul_one, ← hφ, h]
  exact mul_left_cancel h2

theorem hom_T_decomp (a : Nat) : ∀ n, φ (false, a % 2 ^ n, 0) =
    ((List.range n).map fun k => if a.testBit k then φ (false, 2 ^ k, 0) else 1).prod
  | 0 => by
    rw [pow_zero, Nat.mod_one]
    exact hom_one φ hφ
  | n + 1 => by
    have hb : φ (false, (if a.testBit n then 2 ^ n else 0), 0) =
        if a.testBit n then φ (false, 2 ^ n, 0) else 1 := by
      cases a.testBit n
      · exact hom_one φ hφ
      · rfl
    rw [List.range_succ, List.map_append, List.prod_append, ← hom_T_decomp a n,
      List.map_singleton, List.prod_singleton, ← hb, ← hφ, mul_T, mod_two_pow_succ]

theorem hom_D_decomp (d : Nat) : ∀ n, φ (false, 0, d % 2 ^ n) =
    ((List.range n).map fun k => if d.testBit k then φ (false, 0, 2 ^ k) else 1).prod
  | 0 => by
    rw [pow_zero, Nat.mod_one]
    exact hom_one φ hφ
  | n + 1 => by
    have hb : φ (false, 0, (if d.testBit n then 2 ^ n else 0)) =
        if d.testBit n then φ (false, 0, 2 ^ n) else 1 := by
      cases d.testBit n
      · exact hom_one φ hφ
      · rfl
    rw [List.range_succ, List.map_append, List.prod_append, ← hom_D_decomp d n,
      List.map_singleton, List.prod_singleton, ← hb, ← hφ, mul_D, mod_two_pow_succ]

theorem hom_unpackP_decomp (y : Nat) :
    φ (unpackP y) = φ ((unpackP y).1, 0, 0) *
      ((List.range 24).map fun k =>
        if (y % 16777216).testBit k then φ (basisP k) else 1).prod := by
  have hu : unpackP y = ((unpackP y).1, y % 2 ^ 12, y / 2 ^ 12 % 2 ^ 12) := rfl
  have hT := hom_T_decomp φ hφ y 12
  have hD := hom_D_decomp φ hφ (y / 2 ^ 12) 12
  have h1 : ((List.range 12).map fun k => if y.testBit k then φ (false, 2 ^ k, 0) else 1) =
      (List.range 12).map fun k => if (y % 16777216).testBit k then φ (basisP k) else 1 := by
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    have hb : basisP k = (false, 2 ^ k, 0) := by simp [basisP, hk]
    rw [hb, show (16777216 : Nat) = 2 ^ 24 from rfl, Nat.testBit_mod_two_pow]
    simp [show k < 24 by omega]
  have h2 : ((List.range 12).map fun k =>
        if (y / 2 ^ 12).testBit k then φ (false, 0, 2 ^ k) else 1) =
      ((List.range 12).map (12 + ·)).map
        fun k => if (y % 16777216).testBit k then φ (basisP k) else 1 := by
    rw [List.map_map]
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    have hb : basisP (12 + k) = (false, 0, 2 ^ k) := by
      simp [basisP, show ¬ 12 + k < 12 by omega]
    rw [Function.comp_apply, hb, show (16777216 : Nat) = 2 ^ 24 from rfl,
      Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp [show 12 + k < 24 by omega, Nat.add_comm k 12]
  rw [show (24 : Nat) = 12 + 12 from rfl, List.range_add, List.map_append, List.prod_append,
    ← h1, ← h2, ← hT, ← hD, ← mul_assoc, ← hφ, ← hφ, mul_split, ← hu]

theorem applyN_spec : ∀ n acc yb rb, φ (unpackP (applyN n acc yb rb)) =
    φ (unpackP acc) * ((List.range n).map fun k =>
      if yb.testBit k then φ (unpackP (rb / 2 ^ (25 * k) % 33554432)) else 1).prod
  | 0, acc, _, _ => by
    rw [List.range_zero, List.map_nil, List.prod_nil, mul_one]
    rfl
  | n + 1, acc, yb, rb => by
    have hstep : φ (unpackP (bif Nat.beq (yb % 2) 1 then mulP acc (rb % 33554432) else acc)) =
        φ (unpackP acc) * (if yb.testBit 0 then φ (unpackP (rb % 33554432)) else 1) := by
      rcases Nat.mod_two_eq_zero_or_one yb with h | h
      · have h0 : yb.testBit 0 = false := by simp [Nat.testBit_zero, h]
        rw [h, h0]
        simp
      · have h0 : yb.testBit 0 = true := by simp [Nat.testBit_zero, h]
        rw [h, h0, show Nat.beq 1 1 = true from rfl, cond_true, if_pos rfl, unpackP_mulP, hφ]
    have hl : ((List.range n).map fun k =>
          if (yb / 2).testBit k then φ (unpackP (rb / 33554432 / 2 ^ (25 * k) % 33554432))
          else 1) =
        (List.range n).map ((fun k =>
          if yb.testBit k then φ (unpackP (rb / 2 ^ (25 * k) % 33554432)) else 1) ∘ Nat.succ) := by
      apply List.map_congr_left
      intro k _
      rw [Function.comp_apply, Nat.testBit_succ, Nat.div_div_eq_div_mul,
        show (33554432 : Nat) * 2 ^ (25 * k) = 2 ^ (25 * Nat.succ k) by
          rw [Nat.succ_eq_add_one, Nat.mul_succ, Nat.pow_add, Nat.mul_comm]]
    rw [applyN_succ, applyN_spec n, hstep, hl, List.range_succ_eq_map, List.map_cons,
      List.prod_cons, List.map_map, mul_assoc, Nat.mul_zero, Nat.pow_zero, Nat.div_one]

end Hom

theorem applyN_lt : ∀ n {acc : Nat}, acc < 2 ^ 25 → ∀ yb rb, applyN n acc yb rb < 2 ^ 25
  | 0, _, h, _, _ => h
  | n + 1, acc, h, yb, rb => by
    rw [applyN_succ]
    refine applyN_lt n ?_ (yb / 2) (rb / 33554432)
    cases Nat.beq (yb % 2) 1
    · exact h
    · exact mulP_lt h (Nat.mod_lt _ (by decide))

private theorem unpackP_sign {y : Nat} (hy : y < 2 ^ 25) :
    unpackP (y / 16777216 * 16777216) = ((unpackP y).1, 0, 0) := by
  have h : y / 16777216 < 2 := by omega
  have hs : (unpackP y).1 = Nat.beq (y / 16777216 % 2) 1 := rfl
  rw [hs]
  generalize y / 16777216 = t at h
  interval_cases t <;> rfl

theorem exists_conjQ {ℓ : XLetter} (h : okT ℓ = true) :
    ∃ P : Pvis, ∀ y, conjQ P (pauliQ y) = pauliQ (ℓ.conjN y) := by
  cases ℓ with
  | lift k =>
    have hk : k < 44 := by
      have h' : Nat.blt k 43 = true := h
      rw [Nat.blt_eq] at h'
      omega
    exact ⟨h1Lift ⟨k, hk⟩, fun y => conjQ_h1Lift ⟨k, hk⟩ y⟩
  | pc q => exact ⟨rhoPair (pauliQ q), fun y => conjQ_rhoPair_toQ q y⟩
  | sign a => exact ⟨_, fun y => conjQ_sign_toQ a y⟩

theorem exists_conjSC {ℓ : XLetter} (h : okT ℓ = true) :
    ∃ ψ : SpinCoord ≃* SpinCoord, ∀ y, ψ (toSC y) = toSC (ℓ.conjN y) := by
  obtain ⟨P, hP⟩ := exists_conjQ h
  refine ⟨(spinEquiv.trans (conjQ P)).trans spinEquiv.symm, fun y => ?_⟩
  change spinEquiv.symm (conjQ P (pauliQ y)) = _
  rw [hP]
  exact spinEquiv.symm_apply_apply _

theorem toSC_applyRow {T r : Nat} (hT : tabOK T r = true)
    (hr : okT (letterAt r) = true) {y : Nat} (hy : y < 2 ^ 25) :
    toSC (unpackP (applyRow (rowAt T r) y)) = toSC ((letterAt r).conjN (unpackP y)) := by
  obtain ⟨P, hP⟩ := exists_conjSC hr
  have hT': ((letterAt r).conjN (true, 0, 0) == (true, 0, 0)) = true ∧
      allBelow 24 (fun k => unpackP (entryAt (rowAt T r) k) == (letterAt r).conjN (basisP k)) =
        true := by
    simpa only [tabOK, Bool.and_eq_true] using hT
  have hz : (letterAt r).conjN (true, 0, 0) = (true, 0, 0) := beq_iff_eq.1 hT'.1
  have he := allBelow_true hT'.2
  have hs : P (toSC ((unpackP y).1, 0, 0)) = toSC ((unpackP y).1, 0, 0) := by
    cases (unpackP y).1
    · rw [hom_one toSC toSC_mul, map_one]
    · rw [hP, hz]
  have hl : ((List.range 24).map fun k =>
        if (y % 16777216).testBit k then
          toSC (unpackP (rowAt T r / 2 ^ (25 * k) % 33554432)) else 1) =
      (List.range 24).map (P ∘ fun k =>
        if (y % 16777216).testBit k then toSC (basisP k) else 1) := by
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    have hek := beq_iff_eq.1 (he k hk)
    rw [entryAt, Nat.shiftRight_eq_div_pow] at hek
    rw [Function.comp_apply]
    cases (y % 16777216).testBit k
    · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, map_one]
    · rw [if_pos rfl, if_pos rfl, hP, hek]
  rw [applyRow_eq, applyN_spec toSC toSC_mul, unpackP_sign hy, ← hP,
    hom_unpackP_decomp toSC toSC_mul (y := y), map_mul, map_list_prod, List.map_map, hl, hs]

theorem unpackP_applyRow {T r : Nat} (hT : tabOK T r = true)
    (hr : okT (letterAt r) = true) {y : Nat} (hy : y < 2 ^ 25) :
    unpackP (applyRow (rowAt T r) y) = (letterAt r).conjN (unpackP y) :=
  pauliQ_injective_box (unpackP_canon _) (conjN_canon hr (unpackP_canon y))
    (congrArg spinEquiv (toSC_applyRow hT hr hy))

theorem applyRow_lt (row : Nat) {y : Nat} (hy : y < 2 ^ 25) : applyRow row y < 2 ^ 25 := by
  rw [applyRow_eq]
  exact applyN_lt 24 (lt_of_le_of_lt (Nat.div_mul_le_self _ _) hy) _ _

theorem unpackP_conjW {T : Nat}
    (hT : ∀ r < 52, tabOK T r = true) :
    ∀ (w : List XLetter), allL okT w = true → ∀ {y : Nat}, y < 2 ^ 25 →
      conjW T w y < 2 ^ 25 ∧ unpackP (conjW T w y) = xConj w (unpackP y)
  | [], _, _, hy => ⟨hy, rfl⟩
  | ℓ :: w, hw, y, hy => by
    have hw' : (okT ℓ && allL okT w) = true := hw
    rw [Bool.and_eq_true] at hw'
    obtain ⟨h1, h2⟩ := unpackP_conjW hT w hw'.2 hy
    have hr : okT (letterAt (rowIdx ℓ)) = true := by rw [letterAt_rowIdx hw'.1]; exact hw'.1
    have e1 : conjW T (ℓ :: w) y = applyRow (rowAt T (rowIdx ℓ)) (conjW T w y) := rfl
    have e2 : xConj (ℓ :: w) (unpackP y) = ℓ.conjN (xConj w (unpackP y)) := rfl
    rw [e1, e2]
    refine ⟨applyRow_lt _ h1, ?_⟩
    rw [unpackP_applyRow (hT _ (rowIdx_lt hw'.1)) hr h1, letterAt_rowIdx hw'.1, h2]

private theorem genP_spec : ∀ i < 23, genP i < 2 ^ 25 ∧ unpackP (genP i) = pauliGen i := by
  decide +kernel

private theorem all_ok_of_allL {w : List XLetter} (h : allL okT w = true) :
    w.all XLetter.ok = true :=
  List.all_eq_true.2 fun ℓ hℓ => okT_ok (allL_true h ℓ hℓ)

theorem relCheck_of_relT {T : Nat}
    (hT : ∀ r < 52, tabOK T r = true) {w w' : List XLetter} (h : relT T w w' = true) :
    relCheck w w' = true := by
  simp only [relT, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hw, hw'⟩, hpc⟩, htr⟩ := h
  have hpc' := allBelow_true hpc
  simp only [relCheck, Bool.and_eq_true]
  refine ⟨⟨⟨all_ok_of_allL hw, all_ok_of_allL hw'⟩, ?_⟩, htr⟩
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  obtain ⟨hlt, hg⟩ := genP_spec i hi
  have e := pcEqN_of_pcEqP (hpc' i hi)
  rw [(unpackP_conjW hT w hw hlt).2, (unpackP_conjW hT w' hw' hlt).2, hg] at e
  exact e

theorem tabOK_of_chunks {T : Nat} (h : ∀ c < 4, tabChunk T c = true) :
    ∀ r < 52, tabOK T r = true := by
  intro r hr
  have h0 := allBelow_true (h 0 (by decide))
  have h1 := allBelow_true (h 1 (by decide))
  have h2 := allBelow_true (h 2 (by decide))
  have h3 := allBelow_true (h 3 (by decide))
  have c0 : chunkLo 0 = 0 := rfl
  have c1 : chunkLo 1 = 23 := rfl
  have c2 : chunkLo 2 = 32 := rfl
  have c3 : chunkLo 3 = 43 := rfl
  have c4 : chunkLo 4 = 52 := rfl
  rw [c0, c1] at h0
  rw [c1, c2] at h1
  rw [c2, c3] at h2
  rw [c3, c4] at h3
  by_cases r0 : r < 23
  · simpa using h0 r (by omega)
  by_cases r1 : r < 32
  · simpa [show 23 + (r - 23) = r by omega] using h1 (r - 23) (by omega)
  by_cases r2 : r < 43
  · simpa [show 32 + (r - 32) = r by omega] using h2 (r - 32) (by omega)
  · simpa [show 43 + (r - 43) = r by omega] using h3 (r - 43) (by omega)

end CFSG.KC.WordRelK
