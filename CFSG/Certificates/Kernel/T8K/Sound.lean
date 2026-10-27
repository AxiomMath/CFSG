module

public import CFSG.Certificates.Kernel.P0RankK.Collector
public import CFSG.Certificates.Kernel.WordRelK.Rel
public import Certificates.Data.Kernel.T8K
public import CFSG.GroupTheory.ElemAbelianClosure

set_option linter.unusedSectionVars false

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.T8K

open CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Sp8.WordRel CFSG.Open
open MonsterB.P0Rank CFSG.KC.P0Col CFSG.KC.WordRelK


theorem pcElt_toPC (c : ℕ × ℕ × ℕ) : pcElt (toPC c) = wordX (nfWord c) := by
  simp only [pcElt, pcL, toPC, nfWord, lD, tD, uE, wordX_append]

private theorem uProd_zero : uProd 0 = ([] : List XLetter) := by decide +kernel

theorem pcElt_zero : pcElt ((0, 0), 0) = 1 := by
  simp only [pcElt, pcL, pc_lD_zero, pc_tD_zero, uE, uProd_zero, wordX_nil, mul_one]

private theorem sq_of {c : ℕ × ℕ × ℕ}
    (h : (MonsterB.P0Rank.pmul p0Data (toPC c) (toPC c) == ((0, 0), 0)) = true) :
    wordX (nfWord c) * wordX (nfWord c) = 1 := by
  rw [← pcElt_toPC, ← pcElt_pmul, beq_iff_eq.1 h, pcElt_zero]

private theorem comm_of {c c' : ℕ × ℕ × ℕ}
    (h : (MonsterB.P0Rank.pmul p0Data (toPC c) (toPC c') == MonsterB.P0Rank.pmul p0Data (toPC c') (toPC c)) = true) :
    wordX (nfWord c) * wordX (nfWord c') = wordX (nfWord c') * wordX (nfWord c) := by
  rw [← pcElt_toPC, ← pcElt_toPC, ← pcElt_pmul, ← pcElt_pmul, beq_iff_eq.1 h]

theorem commPL_spec : ∀ {gs : List (ℕ × ℕ × ℕ)}, commPL gs = true →
    (∀ c ∈ gs, wordX (nfWord c) * wordX (nfWord c) = 1) ∧
      ∀ c ∈ gs, ∀ c' ∈ gs,
        wordX (nfWord c) * wordX (nfWord c') = wordX (nfWord c') * wordX (nfWord c)
  | [], _ => ⟨by simp, by simp⟩
  | c :: rest, h => by
    simp only [commPL, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨hsq, hall⟩, hrest⟩ := h
    obtain ⟨ih1, ih2⟩ := commPL_spec hrest
    refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx'
      · exact sq_of hsq
      · exact ih1 x hx'
    · rcases List.mem_cons.1 hx with rfl | hx' <;> rcases List.mem_cons.1 hy with rfl | hy'
      · rfl
      · exact comm_of (hall y hy')
      · exact (comm_of (hall x hx')).symm
      · exact ih2 x hx' y hy'

theorem isElemAbelian_of_commPL {gs : List (ℕ × ℕ × ℕ)} (h : commPL gs = true) :
    IsElemAbelian 2 (Subgroup.closure {g | ∃ c ∈ gs, g = wordX (nfWord c)}) := by
  obtain ⟨hsq, hcomm⟩ := commPL_spec h
  refine IsElemAbelian.closure_of_commute ?_ ?_
  · rintro a ⟨c, hc, rfl⟩ b ⟨c', hc', rfl⟩
    exact hcomm c hc c' hc'
  · rintro a ⟨c, hc, rfl⟩
    rw [pow_two]
    exact hsq c hc

theorem conj_of_conjT {T : Nat} (hT : ∀ r < 52, tabOK T r = true) {w : List XLetter}
    {m : List ℕ} (h : conjT T w m = true) (τ : ℕ) :
    wordX w * wordX (tWord τ) * (wordX w)⁻¹ = wordX (tWord (colsAct m τ)) := by
  simp only [conjT, Bool.and_eq_true] at h
  obtain ⟨hlen, hrel⟩ := h
  have hlen' : m.length = 9 := Nat.eq_of_beq_eq_true hlen
  change wordX w * tD τ * (wordX w)⁻¹ = tD (colsAct m τ)
  rw [colsAct_prod tD tD_xor, hlen', pc_tD_eq_prod τ, ← MulAut.conj_apply, map_list_prod,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro j hj
  have hj9 := List.mem_range.1 hj
  simp only [Function.comp_apply]
  split_ifs
  · have e := wordX_eq_of_relT hT (allBelow_true hrel j hj9)
    rw [wordX_append, wordX_append] at e
    rw [MulAut.conj_apply]
    exact (congrArg (· * (wordX w)⁻¹) e).trans (mul_inv_cancel_right _ _)
  · simp

end CFSG.KC.T8K
