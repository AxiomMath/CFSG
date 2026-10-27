module

public import Certificates.Data.Kernel.McLMultK
public import CFSG.Certificates.Kernel.Spor.F3LaneSound
public import CFSG.Certificates.Kernel.Spor.F3R

public section

namespace CFSG.KC.McLMult

open CFSG.F3.Native CFSG.KS.F3L CFSG.KS.F3R CFSG.KC.Enum

theorem strictV_eq {α : Type} (X : V) (k : V → α) : strictV X k = k X := by
  unfold strictV
  rw [strictT_eq, strictT_eq]

theorem strictLs_eq {α : Type} (L : List V) (k : List V → α) : strictLs L k = k L := by
  induction L generalizing k with
  | nil => rfl
  | cons x xs ih =>
    change strictV x (fun x' => strictLs xs fun ys => k (x' :: ys)) = _
    rw [strictV_eq, ih]

theorem eqL_iff {X Y : V} : eqL X Y = true ↔ X = Y := by
  unfold eqL
  rw [bAnd_eq, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact V.ext' h1 h2
  · rintro rfl
    exact ⟨rfl, rfl⟩

theorem mulL_eq (d E : Nat) (X Y : V) : mulL d E X Y = mulLane d E X Y := strictV_eq _ _

theorem at6_eq (L : List V) {k : Nat} (hk : k < L.length) : at6 L k = L[k] := by
  unfold at6
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]

structure Canon (d : Nat) (X : V) : Prop where
  wf : X.wf = true
  p : X.p < 2 ^ (d * d)
  m : X.m < 2 ^ (d * d)

theorem canonL_spec {d : Nat} {X : V} (h : canonL d X = true) : Canon d X := by
  unfold canonL at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq,
    Nat.blt_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have e : Nat.shiftLeft 1 (d * d) = 2 ^ (d * d) := Nat.one_shiftLeft (d * d)
  refine ⟨?_, lt_of_lt_of_eq h2 e, lt_of_lt_of_eq h3 e⟩
  unfold V.wf
  rw [beq_iff_eq]
  exact h1

noncomputable abbrev mt (d : Nat) (X : V) : Matrix (Fin d) (Fin d) (ZMod 3) :=
  toMat d (unlane d X)

abbrev WF (d : Nat) (X : V) : Prop := RowsWF (unlane d X)

theorem Canon.wF {d : Nat} {X : V} (h : Canon d X) : WF d X :=
  RowsWF.of_canonM (canonM_unlane d h.wf)

theorem mt_ne {d : Nat} {X Y : V} (hX : Canon d X) (hY : Canon d Y) (h : X ≠ Y) :
    mt d X ≠ mt d Y := fun e =>
  h (unlane_inj hX.p hX.m hY.p hY.m (eq_of_canonM (canonM_unlane d hX.wf) (canonM_unlane d hY.wf) e))

variable {d : Nat}

theorem wf_mulL (hd : 0 < d) {X Y : V} (hX : WF d X) (hY : WF d Y) :
    WF d (mulL d (spreadE d d) X Y) := by
  unfold WF
  rw [mulL_eq, ← mul_unlane hd]
  exact RowsWF.mul _ d hX hY

theorem mt_mulL (hd : 0 < d) {X Y : V} (hX : WF d X) (hY : WF d Y) :
    mt d (mulL d (spreadE d d) X Y) = mt d X * mt d Y := by
  unfold mt
  rw [mulL_eq, ← mul_unlane hd]
  exact toMat_mul (unlane_size d X) hX hY

structure IdL (d : Nat) (I : V) : Prop where
  eq : idM d = unlane d I

theorem IdL.wF {I : V} (h : IdL d I) : WF d I := by
  unfold WF
  rw [← h.eq]
  exact RowsWF.idM d

theorem IdL.mt {I : V} (h : IdL d I) : mt d I = 1 := by
  unfold CFSG.KC.McLMult.mt
  rw [← h.eq, toMat_idM]

theorem idL_of {I : V} (h : bAnd(canonL d I, eqMK d (idM d) (unlane d I)) = true) : IdL d I := by
  rw [bAnd_eq, Bool.and_eq_true, ← CFSG.KS.F3R.eqM_eq] at h
  exact ⟨eq_of_canonM (canonM_idM d) (canonM_unlane d (canonL_spec h.1).wf)
    (toMat_eq_of_eqM h.2)⟩

theorem mt_powLane (hd : 0 < d) {I X : V} (hI : IdL d I) (hX : WF d X) (e : Nat) :
    WF d (powLane d (spreadE d d) I X e) ∧ mt d (powLane d (spreadE d d) I X e) = mt d X ^ e := by
  induction e with
  | zero => exact ⟨hI.wF, hI.mt⟩
  | succ e ih =>
    have h1 : WF d (mulL d (spreadE d d) (powLane d (spreadE d d) I X e) X) := wf_mulL hd ih.1 hX
    have h2 := mt_mulL hd ih.1 hX
    rw [mulL_eq] at h1 h2
    exact ⟨h1, by rw [powLane, h2, ih.2, pow_succ]⟩

theorem evalK_spec (hd : 0 < d) {I : V} (hI : IdL d I) {X Xi : Nat → V}
    (hX : ∀ k < 6, WF d (X k)) (hXi : ∀ k < 6, WF d (Xi k)) (w : List (Fin 6 × Bool)) :
    WF d (evalK d (spreadE d d) I X Xi w) ∧ mt d (evalK d (spreadE d d) I X Xi w) =
      (w.map fun l => if l.2 then mt d (X l.1.val) else mt d (Xi l.1.val)).prod := by
  induction w with
  | nil => exact ⟨hI.wF, hI.mt⟩
  | cons l w ih =>
    obtain ⟨⟨i, hi⟩, b⟩ := l
    cases b
    · exact ⟨wf_mulL hd (hXi i hi) ih.1, by
        rw [List.map_cons, List.prod_cons, ← ih.2]; exact mt_mulL hd (hXi i hi) ih.1⟩
    · exact ⟨wf_mulL hd (hX i hi) ih.1, by
        rw [List.map_cons, List.prod_cons, ← ih.2]; exact mt_mulL hd (hX i hi) ih.1⟩

theorem abL_eq (A B B4 : V) (z : Int) :
    abL A B B4 z = if z = 1 ∨ z = -1 then A else if z = 2 then B else B4 := by
  rcases z with (_ | _ | _ | k) | (_ | k)
  · rfl
  · rfl
  · rfl
  · change B4 = _
    rw [Int.ofNat_eq_coe, if_neg (by omega), if_neg (by omega)]
  · rfl
  · change B4 = _
    rw [Int.negSucc_eq, if_neg (by omega), if_neg (by omega)]

theorem abK_spec (hd : 0 < d) {I A B B4 : V} (hI : IdL d I) (hA : WF d A) (hB : WF d B)
    (hB4 : WF d B4) (w : List Int) :
    WF d (abK d (spreadE d d) I A B B4 w) ∧ mt d (abK d (spreadE d d) I A B B4 w) =
      (w.map fun z => if z = 1 ∨ z = -1 then mt d A else if z = 2 then mt d B else mt d B4).prod := by
  induction w with
  | nil => exact ⟨hI.wF, hI.mt⟩
  | cons z w ih =>
    have hz : WF d (abL A B B4 z) := by
      rw [abL_eq]
      split_ifs
      · exact hA
      · exact hB
      · exact hB4
    refine ⟨wf_mulL hd hz ih.1, ?_⟩
    change mt d (mulL d (spreadE d d) (abL A B B4 z) (abK d (spreadE d d) I A B B4 w)) = _
    rw [mt_mulL hd hz ih.1, ih.2, List.map_cons, List.prod_cons, abL_eq]
    split_ifs <;> rfl

theorem genCheck_spec {E : Nat} {I A B : V} {Y : List V} {rels : List (List (Fin 6 × Bool))}
    {comm : Fin 6 → List (Fin 6 × Bool)} {sa sb : List (Fin 6 × Bool)}
    (h : genCheck d E I A B Y rels comm sa sb = true) :
    (∀ r ∈ rels, evalK d E I (at6 Y) (at6 Y) r = I) ∧
      (∀ i : Fin 6, evalK d E I (at6 Y) (at6 Y) (comm i) = at6 Y i.val) ∧
      evalK d E I (at6 Y) (at6 Y) sa = A ∧ evalK d E I (at6 Y) (at6 Y) sb = B := by
  unfold genCheck at h
  simp only [bAnd_eq, Bool.and_eq_true, List.all_eq_true, eqL_iff, List.mem_finRange,
    true_implies] at h
  exact h

theorem coverCheck_spec {E : Nat} {I : V} {X Xi : List V} {rels : List (List (Fin 6 × Bool))}
    {comm : Fin 6 → List (Fin 6 × Bool)} {z : List (Fin 6 × Bool)}
    (h : coverCheck d E I X Xi rels comm z = true) :
    (∀ i < 6, Canon d (at6 X i) ∧ Canon d (at6 Xi i) ∧ mulL d E (at6 X i) (at6 Xi i) = I ∧
        mulL d E (at6 Xi i) (at6 X i) = I) ∧
      (∀ r ∈ rels, ∀ j < 6, mulL d E (at6 X j) (evalK d E I (at6 X) (at6 Xi) r) =
        mulL d E (evalK d E I (at6 X) (at6 Xi) r) (at6 X j)) ∧
      (∀ i : Fin 6, evalK d E I (at6 X) (at6 Xi) (comm i) = at6 X i.val) ∧
      Canon d (evalK d E I (at6 X) (at6 Xi) z) ∧ evalK d E I (at6 X) (at6 Xi) z ≠ I ∧
      mulL d E (evalK d E I (at6 X) (at6 Xi) z)
        (mulL d E (evalK d E I (at6 X) (at6 Xi) z) (evalK d E I (at6 X) (at6 Xi) z)) = I := by
  unfold coverCheck centralK orderThreeK at h
  simp only [bAnd_eq, Bool.and_eq_true, List.all_eq_true, eqL_iff, List.mem_finRange,
    List.mem_range, true_implies, Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun i hi => ?_, h2, h3, canonL_spec h4, ?_, h6⟩
  · obtain ⟨c1, c2, e1, e2⟩ := h1 i hi
    exact ⟨canonL_spec c1, canonL_spec c2, e1, e2⟩
  · intro e
    rw [eqL_iff.2 e] at h5
    cases h5

end CFSG.KC.McLMult

end
