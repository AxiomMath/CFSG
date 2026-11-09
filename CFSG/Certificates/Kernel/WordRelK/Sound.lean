module

public import CFSG.Certificates.Kernel.WordRelK.Bits

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.WordRelK

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Visible CFSG.Monster.B CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Sp8.WordRel

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
    · simp only [Bool.false_eq_true, ↓reduceIte, map_one]
    · simp only [↓reduceIte, hP, hek]
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
