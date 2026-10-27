module

public import CFSG.GF2Type.SmithTypeE.L6.ModBase
public import CFSG.GF2Type.SmithTypeE.L6.ModSteps
public import Certificates.Certificate38651

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open CFSG.SmithL6 CFSG.GF2Type.SmithTypeE.LMod
open CFSG.SmithE (applyCols)
open CFSG.LargeExtraspecial.SMod20 (V decode decode_xor decode_zero eq_of_decode_eq)

theorem wtCheck_holds : mfChkWt = true :=
  Certificates.certificate38651.1

theorem tvAdjCheck_holds : mfChkTvAdj = true :=
  Certificates.certificate38651.2

theorem maskArr_get' {i : Nat} (hi : i < 1395) : maskArr[i]! = wMask i := by
  simp [maskArr, getElem!_pos, hi]

theorem adjM_eq' {i j : Nat} (hi : i < 1395) (hj : j < 1395) : adjM i j = adjW i j := by
  simp only [adjM, adjW, maskArr_get' hi, maskArr_get' hj]

section Wt


theorem mfChkWt_parts :
    (∀ j < 1395, wtIdx[wt j]! = j) ∧
      ∀ i < 1395, wt i < 2 ^ 20 ∧ wt i ≠ 0 ∧ (∃ j < 1395, adjW i j = true ∧ wt j ≠ wt i) ∧
        ∀ j < 1395, adjW i j = false → mfIsWt (wt i ^^^ wt j) = false := by
  have hW := wtCheck_holds
  simp only [mfChkWt, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
    beq_iff_eq, bne_iff_ne, ne_eq, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hW
  obtain ⟨h1, h3⟩ := hW
  refine ⟨fun j hj => by simpa [wtArr_get hj] using h1 j hj, fun i hi => ?_⟩
  obtain ⟨⟨⟨h4, h4'⟩, j, hj, h5, h6⟩, h7⟩ := h3 i hi
  refine ⟨by simpa [wtArr_get hi] using h4, by simpa [wtArr_get hi] using h4',
    ⟨j, hj, by rwa [adjM_eq' hi hj] at h5, by simpa [wtArr_get hi, wtArr_get hj] using h6⟩,
    fun j hj hadj => ?_⟩
  rcases h7 j hj with h | h
  · rw [adjM_eq' hi hj, hadj] at h
    exact absurd h (by decide)
  · simpa [wtArr_get hi, wtArr_get hj] using h

theorem wt_ne_zero' {i : Nat} (hi : i < 1395) : wt i ≠ 0 :=
  (mfChkWt_parts.2 i hi).2.1

theorem wt_lt' {i : Nat} (hi : i < 1395) : wt i < 2 ^ 20 :=
  (mfChkWt_parts.2 i hi).1

theorem exists_adj' {i : Nat} (hi : i < 1395) :
    ∃ j < 1395, adjW i j = true ∧ wt j ≠ wt i :=
  (mfChkWt_parts.2 i hi).2.2.1

theorem wt_ne_xor' {i j : Nat} (hi : i < 1395) (hj : j < 1395) (hadj : adjW i j = false) :
    ∀ k < 1395, wt k ≠ wt i ^^^ wt j := by
  intro k hk hk'
  have h := (mfChkWt_parts.2 i hi).2.2.2 j hj hadj
  have : mfIsWt (wt i ^^^ wt j) = true := by
    simp only [mfIsWt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [← hk', mfChkWt_parts.1 k hk, wtArr_get hk]
    exact ⟨hk, rfl⟩
  rw [h] at this
  exact absurd this (by decide)

end Wt

section Tv


theorem tv_wt' {k i : Nat} (hk : k < 1953) (hi : i < 1395) :
    ∃ j < 1395, wt j = applyCols (tvCols k) (wt i) ∧ adjW i j = true := by
  obtain ⟨hj, hw, -⟩ := tw_parts hk hi
  have h := tvAdjCheck_holds
  simp only [mfChkTvAdj, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at h
  have h' := (h k hk i hi).2
  exact ⟨planeImg k i, hj, hw, by rwa [adjM_eq' hi hj] at h'⟩

end Tv

section Pairs


theorem pair_rel_sym' {k l : Nat} (hk : k < 1953) (hl : l < 1953) :
    (∀ c < 2 ^ 20, applyCols (tvCols k) (applyCols (tvCols l) c) =
      applyCols (tvCols l) (applyCols (tvCols k) c)) ∨
    (∀ c < 2 ^ 20, applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k) c)) =
      applyCols (tvCols l) (applyCols (tvCols k) (applyCols (tvCols l) c))) ∨
    (∀ c < 2 ^ 20, applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k)
        (applyCols (tvCols l) c))) =
      applyCols (tvCols l) (applyCols (tvCols k) (applyCols (tvCols l)
        (applyCols (tvCols k) c)))) := by
  rcases pair_general ⟨k, hk⟩ ⟨l, hl⟩ with h | h | h
  · exact Or.inl (comm_code_of_relC hk hl h)
  · exact Or.inr (Or.inl (braid_code_of_relB hk hl h))
  · exact Or.inr (Or.inr (dih_code_of_relD hk hl h))

end Pairs

section Int


theorem int_rel_sym' {k l : Nat} (hk : k < 1953) (hl : l < 1953) (hkl : k ≠ l) {c c' : Nat}
    (hc : c < 2 ^ 20) (hc' : c' < 2 ^ 20)
    (h : applyCols (tvCols k) c ^^^ c = applyCols (tvCols l) c' ^^^ c') :
    applyCols (tvCols k) c ^^^ c = 0 ∨
      ((∀ e < 2 ^ 20, applyCols (tvCols k) (applyCols (tvCols l) e) =
        applyCols (tvCols l) (applyCols (tvCols k) e)) ∧
       ∃ j < 1395, wt j = applyCols (tvCols k) c ^^^ c) := by
  have hbd : applyCols (tvCols k) c ^^^ c < 2 ^ 20 :=
    Nat.xor_lt_two_pow (n := 20) (applyCols_tv_lt hk c) hc
  have hu1 : InEV (tvE ⟨k, hk⟩) (decode (applyCols (tvCols k) c ^^^ c)) := by
    refine ⟨decode c, ?_⟩
    rw [decode_xor, ← tvEquiv_decode hk c]
    rfl
  have hu2 : InEV (tvE ⟨l, hl⟩) (decode (applyCols (tvCols k) c ^^^ c)) := by
    refine ⟨decode c', ?_⟩
    rw [h, decode_xor, ← tvEquiv_decode hl c']
    rfl
  rcases intV_general ⟨k, hk⟩ ⟨l, hl⟩ (fun e => hkl (congrArg Fin.val e)) _ hu1 hu2 with
    h0 | ⟨hC, j, hj⟩
  · left
    exact eq_of_decode_eq hbd (by norm_num) (h0.trans decode_zero.symm)
  · right
    refine ⟨comm_code_of_relC hk hl hC, j.val, j.2, ?_⟩
    exact eq_of_decode_eq (wt_lt' j.2) hbd hj.symm

end Int

theorem modelFacts :
    ModelFacts where
  wt_ne_zero := fun hi => wt_ne_zero' hi
  exists_adj := fun hi => exists_adj' hi
  wt_ne_xor := fun hi hj hadj => wt_ne_xor' hi hj hadj
  tv_wt := fun hk hi => tv_wt' hk hi
  pair_rel_sym := fun hk hl _ => pair_rel_sym' hk hl
  int_rel_sym := fun hk hl hkl _ _ hc hc' h => int_rel_sym' hk hl hkl hc hc' h

end CFSG.GF2Type.SmithTypeE.L6
