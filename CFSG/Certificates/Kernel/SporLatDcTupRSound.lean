module

public import Certificates.Data.Kernel.SporLatDcTupR
public import CFSG.Certificates.Kernel.SporLatDcTSound

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.KC.E64F

theorem otActRc_sound {w : Nat} {Ps : List Nat} {lbl rows : List (List Nat)}
    (h : otActRc w Ps lbl rows = true) :
    ∀ l < Ps.length, ∀ i < lbl.length, (rows.getD l []).getD i 0 < lbl.length ∧
      lbl.getD ((rows.getD l []).getD i 0) [] = tupW w (Ps.getD l 0) (lbl.getD i []) := by
  unfold otActRc at h
  rw [Bool.and_eq_true, Nat.ble_eq, allIdxRc_eq, allIdx_iff] at h
  obtain ⟨hl, h⟩ := h
  intro l hlP i hi
  have e := h l (by omega)
  simp only [Nat.zero_add, Bool.and_eq_true, Nat.beq_eq, zipAllRc_eq, List.all_eq_true] at e
  obtain ⟨hrl, hz⟩ := e
  have e := zipAllDc (d := 0) (e := []) hz hrl i hi
  beta_reduce at e
  simp only [Nat.blt_eq, eqLRc_iff, mapRc_eq] at e
  rw [List.getD_eq_getElem _ _ (by omega : l < rows.length)]
  exact ⟨e.1, e.2⟩

theorem otIdxR_otIdxOK {w m : Nat} {Ps : List Nat} {O : OmegaData (List Nat)}
    (h : otIdxR w m Ps O = true) : otIdxOK w m Ps O = true := by
  unfold otIdxR at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h0, hn⟩, ha⟩, ht⟩, hnd⟩ := h
  have hact := otActRc_sound ha
  have eR : ∀ l, ((O.pn.toList.map Array.toList).getD l []) =
      (O.pn.toList.getD l default).toList := by
    intro l
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases O.pn.toList[l]? <;> rfl
  simp only [eR] at hact
  unfold otIdxOK
  rw [← omOKL_eq]
  unfold omOKL
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨h0, hn⟩, ?_⟩, ht⟩, hnd⟩
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  intro l hl i hi
  exact hact l hl i hi

theorem codeSetT_ne_of {n : Nat} {t : Array Nat} {x : List Nat} {c : Nat} (hc : c ∈ x)
    (h : (!x.contains (codeAT n t c)) = true) : (!(codeSetT n t x == x)) = true := by
  rw [Bool.not_eq_true', beq_eq_false_iff_ne]
  intro he
  have hm : codeAT n t c ∈ codeSetT n t x := by
    unfold codeSetT
    rw [insN_eq]
    exact (List.perm_insertionSort _ _).symm.subset (List.mem_map_of_mem hc)
  rw [he] at hm
  simp [hm] at h

theorem wordFR_eq (L : Nat → Nat → Nat) (p : Nat) : ∀ w : List Nat, wordFR L w p = wordF L w p
  | [] => rfl
  | l :: w => by
    change L l (wordFR L w p) = L l (wordF L w p)
    rw [wordFR_eq L p w]

theorem wordER_eq (L : Nat → Nat → Nat) (E : List (List Nat)) (p : Nat) :
    ∀ u : List Nat, wordER L E u p = wordE L E u p
  | [] => rfl
  | i :: u => by
    change wordFR L (E.getD i []) (wordER L E u p) = wordF L (E.getD i []) (wordE L E u p)
    rw [wordER_eq L E p u, wordFR_eq]

theorem eqLRc_beq (xs ys : List Nat) : eqLRc xs ys = (xs == ys) :=
  Bool.eq_iff_iff.2 (by rw [eqLRc_iff, beq_iff_eq])

section Checks

variable (C : DcCtx) (D : DcData)

theorem genLabR_eq (g : List Nat) : genLabR C g = genLab C g := by
  have h : wordFR C.L g = wordF C.L g := funext fun p => wordFR_eq C.L p g
  simp only [genLabR, genLab, labF, insNRc_eq, mapRc_eq, h]

theorem memWR_eq (E : List (List Nat)) (x : Wit) (T : List Nat) :
    memWR C E x T = memW C E x T := by
  simp only [memWR, memW, isS, labF, allRc_eq, insNRc_eq, mapRc_eq, wordFR_eq, wordER_eq,
    eqLRc_beq]

theorem topWR_eq (E : List (List Nat)) (ok : Nat → Bool) (ws : List Wit) :
    topWR C D E ok ws = topW C D E ok ws := by
  rcases ws with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩ <;> simp only [topWR, topW, memWR_eq, genLabR_eq]

theorem gensWR_eq (E : List (List Nat)) (ws : List Wit) (gs : List (List Nat)) :
    gensWR C E ws gs = gensW C E ws gs := by
  simp only [gensWR, gensW, memWR_eq, genLabR_eq]

theorem joinOKR_eq (e : Join) : joinOKR C D e = joinOK C D e := by
  simp only [joinOKR, joinOK, gensWR_eq, topWR_eq]

theorem globR_eq : globR C D = globalOK C D := by
  have h : joinOKR C D = joinOK C D := funext (joinOKR_eq C D)
  unfold globR globalOK
  rw [allRc_eq, h]

end Checks

end CFSG.KC.SLDc

end
