module

public import CFSG.Certificates.Kernel.Th.Thirteen
public import CFSG.Certificates.Kernel.Th.ExprSound

public section

namespace CFSG.KC.Th.Thirteen

open CFSG.KC.Th.Expr CFSG.KC.Th.Spec CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.HardMathSupport.Dickson.Sec6.I1431.ThThirteenNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative

variable {k : K}

theorem pk_letK (c : Ctx k) {P Q Q2 : Nat} {RP RQ : Array V4} (hP : pkMat P = rowsMatrix RP)
    (hQ : pkMat Q = rowsMatrix RQ) (hQ2 : pkMat Q2 = rowsMatrix (Native.mulRows RQ RQ)) (l : Int) :
    pkMat (letK P Q Q2 l) =
      rowsMatrix (if l = 1 ∨ l = -1 then RP else if l = 2 then RQ else Native.mulRows RQ RQ) := by
  unfold letK
  split_ifs <;> assumption

theorem pk_foldl (c : Ctx k) {P Q Q2 : Nat} {RP RQ : Array V4} (hP : pkMat P = rowsMatrix RP)
    (hQ : pkMat Q = rowsMatrix RQ) (hQ2 : pkMat Q2 = rowsMatrix (Native.mulRows RQ RQ)) :
    ∀ (w : List Int) (acc : Nat) (A : Array V4), pkMat acc = rowsMatrix A →
      pkMat (w.foldl (fun acc l => k.mul acc (letK P Q Q2 l)) acc) =
        rowsMatrix (w.foldl (fun acc l => Native.mulRows acc
          (if l = 1 ∨ l = -1 then RP else if l = 2 then RQ else Native.mulRows RQ RQ)) A)
  | [], _, _, h => h
  | l :: w, acc, A, h => by
    rw [List.foldl_cons, List.foldl_cons]
    refine pk_foldl c hP hQ hQ2 w _ _ ?_
    rw [c.mul, h, pk_letK c hP hQ hQ2 l, rowsMatrix_mulRows]

theorem pk_wordK (c : Ctx k) {P Q Q2 : Nat} {RP RQ : Array V4} (hP : pkMat P = rowsMatrix RP)
    (hQ : pkMat Q = rowsMatrix RQ) (hQ2 : pkMat Q2 = rowsMatrix (Native.mulRows RQ RQ)) (w : List Int) :
    pkMat (wordK k P Q Q2 w) = rowsMatrix (wordRows RP RQ w) :=
  pk_foldl c hP hQ hQ2 w _ _ (c.one.trans rowsMatrix_idRows.symm)

theorem lay_foldl (c : Ctx k) (P Q Q2 : Nat) :
    ∀ (w : List Int) (acc : Nat), InLayout acc →
      InLayout (w.foldl (fun acc l => k.mul acc (letK P Q Q2 l)) acc)
  | [], _, h => h
  | l :: w, acc, _ => by
    rw [List.foldl_cons]
    exact lay_foldl c P Q Q2 w _ (c.lay _ _)

theorem lay_wordK (c : Ctx k) (P Q Q2 : Nat) (w : List Int) : InLayout (wordK k P Q Q2 w) :=
  lay_foldl c P Q Q2 w _ c.layOne

theorem wf_foldl {RP RQ : Array V4} (hP : WfRows RP) (hQ : WfRows RQ) :
    ∀ (w : List Int) (A : Array V4), WfRows A →
      WfRows (w.foldl (fun acc l => Native.mulRows acc
        (if l = 1 ∨ l = -1 then RP else if l = 2 then RQ else Native.mulRows RQ RQ)) A)
  | [], _, h => h
  | l :: w, A, h => by
    rw [List.foldl_cons]
    refine wf_foldl hP hQ w _ (wfRows_mulRows h ?_)
    split_ifs
    · exact hP
    · exact hQ
    · exact wfRows_mulRows hQ hQ

theorem wf_wordRows {RP RQ : Array V4} (hP : WfRows RP) (hQ : WfRows RQ) (w : List Int) :
    WfRows (wordRows RP RQ w) :=
  wf_foldl hP hQ w _ wfRows_idRows

theorem pk_powK (c : Ctx k) {P : Nat} {R : Array V4} (hP : pkMat P = rowsMatrix R) :
    ∀ e, pkMat (powK k P e) = rowsMatrix (powRowsN R e)
  | 0 => c.one.trans rowsMatrix_idRows.symm
  | e + 1 => by
    change pkMat (k.mul (powK k P e) P) = rowsMatrix (Native.mulRows (powRowsN R e) R)
    rw [c.mul, pk_powK c hP e, hP, rowsMatrix_mulRows]

theorem wf_powRowsN {R : Array V4} (hR : WfRows R) : ∀ e, WfRows (powRowsN R e)
  | 0 => wfRows_idRows
  | e + 1 => wfRows_mulRows (wf_powRowsN hR e) hR

theorem rowsDiffer_of_ne {X Y : Array V4} (h : rowsMatrix X ≠ rowsMatrix Y) :
    rowsDiffer X Y = true := by
  by_contra hne
  apply h
  have hall : ∀ k < 248, ∀ c < 248, (rowAt X k).testBit c = (rowAt Y k).testBit c := by
    intro k hk c hc
    by_contra e
    apply hne
    unfold rowsDiffer
    simp only [List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq]
    exact ⟨k, hk, c, hc, e⟩
  funext i j
  rw [rowsMatrix_apply, rowsMatrix_apply, V4.toVec_apply, V4.toVec_apply]
  have := hall i.val i.isLt j.val j.isLt
  unfold rowAt at this
  rw [this]

theorem th13OK_of (c : Ctx k) (h : th13K k = true) : th13OK () = true := by
  have wA : WfRows (rowsOf seedA) := wfRows_rowsOf _
  have wB : WfRows (rowsOf seedB) := wfRows_rowsOf _
  have hA : pkMat k.SA = rowsMatrix (rowsOf seedA) := c.sa
  have hB : pkMat k.SB = rowsMatrix (rowsOf seedB) := c.sb
  have hB2 : pkMat (k.mul k.SB k.SB) = rowsMatrix (Native.mulRows (rowsOf seedB) (rowsOf seedB)) := by
    rw [c.mul, hB, rowsMatrix_mulRows]
  have hX := pk_wordK c hA hB hB2 (xWord ())
  have hY0 := pk_wordK c hA hB hB2 (yWord ())
  have wX : WfRows (xRows ()) := wf_wordRows wA wB (xWord ())
  have wY0 : WfRows (yRows ()) := wf_wordRows wA wB (yWord ())
  have hY2 : pkMat (k.mul (wordK k k.SA k.SB (k.mul k.SB k.SB) (yWord ()))
      (wordK k k.SA k.SB (k.mul k.SB k.SB) (yWord ()))) =
      rowsMatrix (Native.mulRows (yRows ()) (yRows ())) := by
    rw [c.mul, hY0, rowsMatrix_mulRows]
    rfl
  have hY := pk_wordK c hX hY0 hY2 y13Word
  have hG := pk_wordK c hX hY0 hY2 g13Word
  have wY : WfRows (y13Rows ()) := wf_wordRows wX wY0 y13Word
  have wG : WfRows (g13Rows ()) := wf_wordRows wX wY0 g13Word
  have hYr : pkMat (wordK k (wordK k k.SA k.SB (k.mul k.SB k.SB) (xWord ()))
      (wordK k k.SA k.SB (k.mul k.SB k.SB) (yWord ()))
      (k.mul (wordK k k.SA k.SB (k.mul k.SB k.SB) (yWord ()))
        (wordK k k.SA k.SB (k.mul k.SB k.SB) (yWord ()))) y13Word) =
      rowsMatrix (y13Rows ()) := hY
  have hGr : pkMat (wordK k (wordK k k.SA k.SB (k.mul k.SB k.SB) (xWord ()))
      (wordK k k.SA k.SB (k.mul k.SB k.SB) (yWord ()))
      (k.mul (wordK k k.SA k.SB (k.mul k.SB k.SB) (yWord ()))
        (wordK k k.SA k.SB (k.mul k.SB k.SB) (yWord ()))) g13Word) =
      rowsMatrix (g13Rows ()) := hG
  have hone : pkMat k.ONE = rowsMatrix idRows := c.one.trans rowsMatrix_idRows.symm
  unfold th13K th13KW at h
  simp only [strictB_eq, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold th13OK
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact Max3S.eqRows_true_of_pk (wf_powRowsN wY 13) wfRows_idRows (pk_powK c hYr 13) hone
      (Nat.eq_of_beq_eq_true h1)
  · refine rowsDiffer_of_ne fun he => ?_
    cases hb : Nat.beq (wordK k (wordK k k.SA k.SB (k.mul k.SB k.SB) (xWord ()))
        (wordK k k.SA k.SB (k.mul k.SB k.SB) (yWord ()))
        (k.mul (wordK k k.SA k.SB (k.mul k.SB k.SB) (yWord ()))
          (wordK k k.SA k.SB (k.mul k.SB k.SB) (yWord ()))) y13Word) k.ONE
    · exact Nat.ne_of_beq_eq_false hb (pkMat_inj (lay_wordK c _ _ _ _) c.layOne
        (by rw [hYr, hone, he]))
    · rw [hb] at h2
      exact absurd h2 (by decide)
  · refine Max3S.eqRows_true_of_pk (wfRows_mulRows wY wG) (wfRows_mulRows wG (wf_powRowsN wY 2))
      ?_ ?_ (Nat.eq_of_beq_eq_true h3)
    · rw [c.mul, hYr, hGr, rowsMatrix_mulRows]
    · rw [c.mul, hGr, pk_powK c hYr 2, rowsMatrix_mulRows]

end CFSG.KC.Th.Thirteen

end
