
module

public import Certificates.Data.Kernel.SporSch.Co1Stab
public import CFSG.Certificates.Kernel.SporSch.Co1MatLemmas
import CFSG.Certificates.Kernel.SporSch.Co1ActLemmas

public section

namespace CFSG.KS.SporSch.M24

open CFSG.Sporadic.Co1Schreier.Native CFSG.KS.Raw CFSG.KS.Mathieu

@[expose] def witRowsP (W : List (List (List Int))) (rs is : List Rows) (m : Nat) : List Rows :=
  (W.getD m []).map fun w => word rs is w

@[expose] def witCheckP (W : List (List (List Int))) (rs is : List Rows) (sv : List Nat) : Bool :=
  (List.range 3).all fun m => (witRowsP W rs is m).all fun s =>
    act s (sv.getD 0 0) == sv.getD 0 0 && act s (sv.getD (m + 1) 0) == sv.getD (m + 1) 0 && wf s

@[expose] def fixCoefP (ws : List Rows) (c u : Nat) : Bool :=
  ((ws.getD (c / 24) one).getD (c % 24) 0 ^^^ (1 <<< (c % 24))).testBit u

@[expose] def fixCombP (ws : List Rows) (cs : List Nat) (v : Nat) : Bool :=
  cs.foldl (fun b c => b ^^ fixCoefP ws c v) false

@[expose] def fixCheckOfP (FF : List (Nat × Nat)) (FS : List (List (List Nat))) (sv : List Nat)
    (m : Nat) (ws : List Rows) : Bool :=
  decide ((FF.getD m (0, 0)).1 < 24) && decide ((FF.getD m (0, 0)).2 < 24) &&
    ((sv.getD 0 0).testBit (FF.getD m (0, 0)).1 &&
        (sv.getD (m + 1) 0).testBit (FF.getD m (0, 0)).2) !=
      ((sv.getD 0 0).testBit (FF.getD m (0, 0)).2 &&
        (sv.getD (m + 1) 0).testBit (FF.getD m (0, 0)).1) &&
    (List.range 24).all fun u =>
      !(u != (FF.getD m (0, 0)).1 && u != (FF.getD m (0, 0)).2) ||
      (fixCombP ws ((FS.getD m []).getD u []) u &&
        (List.range 24).all (fun v => v == u ||
          !(v != (FF.getD m (0, 0)).1 && v != (FF.getD m (0, 0)).2) ||
          !fixCombP ws ((FS.getD m []).getD u []) v) &&
        ((FS.getD m []).getD u []).all fun c => decide (c / 24 < ws.length))

@[expose] def fixCheckP (W : List (List (List Int))) (rs is : List Rows) (FF : List (Nat × Nat))
    (FS : List (List (List Nat))) (sv : List Nat) : Bool :=
  (List.range 3).all fun m => fixCheckOfP FF FS sv m (witRowsP W rs is m)

theorem bAnd_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

theorem shiftRight_one (c : Nat) : Nat.shiftRight c 1 = c / 2 :=
  (Nat.shiftRight_eq_div_pow c 1).trans (by norm_num)

theorem lettersIK_spec {k : Nat} {w : List Int} (h : lettersIK k w = true) :
    ∀ z ∈ w, 2 ≤ icode z ∧ icode z / 2 - 1 < k := by
  induction w with
  | nil => simp
  | cons z w ih =>
    have e : lettersIK k (z :: w) = CFSG.KC.Enum.strictB (icode z) (fun c => bAnd(Nat.ble (nat_lit 2) c,
        bAnd(Nat.blt (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)) k, lettersIK k w))) := rfl
    rw [e] at h
    simp only [MatL.strictB_eq, MatL.bAnd_eq, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq,
      shiftRight_one, Nat.sub_eq] at h
    intro z' hz'
    rcases List.mem_cons.1 hz' with rfl | hz'
    · exact ⟨h.1, h.2.1⟩
    · exact ih h.2.2 z' hz'

theorem letterK_eq (M MI : Nat → Nat) (c : Nat) :
    letterK M MI c = if c % 2 = 0 then M (c / 2 - 1) else MI (c / 2 - 1) := by
  have h1 : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
  unfold letterK
  rw [MatL.nIf_eq, h1, shiftRight_one]
  simp only [Nat.beq_eq, Nat.sub_eq]

theorem rowsL_getD (M : Nat → Nat) {k i : Nat} (hi : i < k) :
    (MatL.rowsL M k).getD i (one ()) = unpack 24 24 (M i) := by
  simp [MatL.rowsL, List.getD_eq_getElem?_getD, hi]

theorem letter_eq {M MI : Nat → Nat} {k : Nat} {z : Int} (h2 : 2 ≤ icode z)
    (hk : icode z / 2 - 1 < k) :
    letter (MatL.rowsL M k) (MatL.rowsL MI k) z = unpack 24 24 (letterK M MI (icode z)) := by
  rw [letterK_eq]
  cases z with
  | ofNat n =>
    have e : icode (Int.ofNat n) = n + n := rfl
    rw [e] at h2 hk ⊢
    have hn : (n + n) / 2 = n := by omega
    rw [hn] at hk ⊢
    have hpos : (0 : Int) < Int.ofNat n := by
      rw [Int.ofNat_eq_natCast]
      omega
    have hev : (n + n) % 2 = 0 := by omega
    unfold letter
    rw [ite_eq_left hpos, ite_eq_left hev, Int.ofNat_eq_natCast, Int.toNat_natCast]
    exact rowsL_getD M hk
  | negSucc n =>
    have e : icode (Int.negSucc n) = (n + 1) + (n + 1) + 1 := rfl
    rw [e] at hk ⊢
    have hn : ((n + 1) + (n + 1) + 1) / 2 - 1 = n := by omega
    rw [hn] at hk ⊢
    have hneg : ¬ (0 : Int) < Int.negSucc n := by
      have := Int.negSucc_lt_zero n
      omega
    have hod : ¬ ((n + 1) + (n + 1) + 1) % 2 = 0 := by omega
    unfold letter
    rw [ite_eq_right hneg, ite_eq_right hod, Int.neg_negSucc]
    have e2 : ((n + 1 : Nat) : Int).toNat - 1 = n := by
      rw [Int.toNat_natCast]
      omega
    rw [e2]
    exact rowsL_getD MI hk

theorem wordIK_eq (M MI : Nat → Nat) (w : List Int) :
    wordIK M MI w = w.foldl (fun acc z => mulK acc (letterK M MI (icode z))) idM := by
  unfold wordIK
  generalize idM = a
  induction w generalizing a with
  | nil => rfl
  | cons z w ih => exact (MatL.strictN_eq _ _).trans (ih _)

theorem word_unpack {rs is : List Rows} {M MI : Nat → Nat} (w : List Int) (a : Nat)
    (hl : ∀ z ∈ w, letter rs is z = unpack 24 24 (letterK M MI (icode z))) :
    w.foldl (fun A j => mul A (letter rs is j)) (unpack 24 24 a) =
      unpack 24 24 (w.foldl (fun acc z => mulK acc (letterK M MI (icode z))) a) := by
  induction w generalizing a with
  | nil => rfl
  | cons z w ih =>
    rw [List.foldl_cons, List.foldl_cons, hl z (by simp), ← MatL.unpack_mulK]
    exact ih _ (fun z' hz' => hl z' (List.mem_cons_of_mem z hz'))

theorem word_eq_wordIK {M MI : Nat → Nat} {k : Nat} {w : List Int} (h : lettersIK k w = true) :
    word (MatL.rowsL M k) (MatL.rowsL MI k) w = unpack 24 24 (wordIK M MI w) := by
  unfold word
  rw [← MatL.unpack_idM, wordIK_eq]
  exact word_unpack w idM fun z hz =>
    letter_eq (lettersIK_spec h z hz).1 (lettersIK_spec h z hz).2

theorem lenWI_eq (ws : List (List Int)) : lenWI ws = ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => exact congrArg Nat.succ ih

theorem dagIK_sound {M MI : Nat → Nat} {nb N : Nat} {ws : List (List Int)} {base : List Rows}
    (hb : base = (List.range nb).map fun i => unpack 24 24 (M i))
    (h : dagIK M MI nb N ws = true) :
    dag base ws = ((List.range N).map fun i => unpack 24 24 (M i),
      (List.range N).map fun i => unpack 24 24 (MI i), true) := by
  obtain ⟨hN, h⟩ := bAnd_true h
  obtain ⟨hall, hrec⟩ := bAnd_true h
  have hN' : nb + ws.length = N := by
    rw [← lenWI_eq]
    exact Nat.eq_of_beq_eq_true hN
  have hd := MatL.dag_sound (M := M) (MI := MI) lettersIK (wordIK M MI) (fun w => w) hb
    (fun _ _ hw => word_eq_wordIK hw) hN' (MatL.allN_iff.1 hall) hrec
  rw [List.map_id'] at hd
  exact hd

namespace StabL

open CFSG.KC.Enum

theorem nget_eq (l : List Nat) (i : Nat) : nget l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change nget l i = _
      rw [ih]
      simp

theorem ngetW_eq (l : List (List (List Int))) (i : Nat) : ngetW l i = l.getD i [] := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change ngetW l i = _
      rw [ih]
      simp

theorem ngetL_eq (l : List (List Nat)) (i : Nat) : ngetL l i = l.getD i [] := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change ngetL l i = _
      rw [ih]
      simp

theorem ngetLL_eq (l : List (List (List Nat))) (i : Nat) : Orb.ngetLL l i = l.getD i [] := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change Orb.ngetLL l i = _
      rw [ih]
      simp

theorem pairFst_eq (l : List (Nat × Nat)) (i : Nat) : pairFst l i = (l.getD i (0, 0)).1 := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero =>
      obtain ⟨a, b⟩ := x
      rfl
    | succ i =>
      change pairFst l i = _
      rw [ih]
      simp

theorem pairSnd_eq (l : List (Nat × Nat)) (i : Nat) : pairSnd l i = (l.getD i (0, 0)).2 := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero =>
      obtain ⟨a, b⟩ := x
      rfl
    | succ i =>
      change pairSnd l i = _
      rw [ih]
      simp

theorem lenN_eq (l : List Nat) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg Nat.succ ih

theorem valsK_eq (M MI : Nat → Nat) (ws : List (List Int)) :
    valsK M MI ws = ws.map (wordIK M MI) := by
  induction ws with
  | nil => rfl
  | cons w ws ih => exact congrArg (wordIK M MI w :: ·) ih

theorem bitK_eq (x i : Nat) : bitK x i = x.testBit i := by
  change Nat.beq ((x >>> i) &&& 1) 1 = _
  rw [ActL.and_one_beq, Nat.testBit_shiftRight, Nat.add_zero]

theorem wf_unpack' (R : Nat) : wf (unpack 24 24 R) = true := by
  unfold wf
  rw [Bool.and_eq_true]
  refine ⟨by simp [MatL.unpack_size], ?_⟩
  rw [Array.all_eq_true]
  intro i hi
  rw [MatL.unpack_getElem]
  exact decide_eq_true (MatL.rowV_lt R i)

theorem rows2 (F : Nat → Nat) : [unpack 24 24 (F 0), unpack 24 24 (F 1)] = MatL.rowsL F 2 := by
  simp [MatL.rowsL, List.range_succ]

theorem witL_iff (M MI : Nat → Nat) (z v : Nat) (ws : List (List Int)) :
    List.rec (motive := fun _ => Bool) true (fun w _ ih => bAnd(lettersIK (nat_lit 2) w,
        strictB (wordIK M MI w) (fun R => bAnd(Nat.beq (actK R z) z,
          bAnd(Nat.beq (actK R v) v, ih))))) ws = true ↔
      ∀ w ∈ ws, lettersIK 2 w = true ∧ actK (wordIK M MI w) z = z ∧
        actK (wordIK M MI w) v = v := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    have e : List.rec (motive := fun _ => Bool) true (fun w _ ih => bAnd(lettersIK (nat_lit 2) w,
        strictB (wordIK M MI w) (fun R => bAnd(Nat.beq (actK R z) z,
          bAnd(Nat.beq (actK R v) v, ih))))) (w :: ws) =
        bAnd(lettersIK (nat_lit 2) w, strictB (wordIK M MI w) (fun R => bAnd(Nat.beq (actK R z) z,
          bAnd(Nat.beq (actK R v) v, List.rec (motive := fun _ => Bool) true
            (fun w _ ih => bAnd(lettersIK (nat_lit 2) w,
              strictB (wordIK M MI w) (fun R => bAnd(Nat.beq (actK R z) z,
                bAnd(Nat.beq (actK R v) v, ih))))) ws)))) := rfl
    rw [e]
    simp only [MatL.bAnd_eq, MatL.strictB_eq] at ih ⊢
    simp only [Bool.and_eq_true, Nat.beq_eq, ih, List.mem_cons, forall_eq_or_imp, and_assoc]

theorem witK_spec {M MI : Nat → Nat} {W : List (List (List Int))} {sv : List Nat}
    (h : witK M MI W sv = true) {m : Nat} (hm : m < 3) :
    ∀ w ∈ W.getD m [], lettersIK 2 w = true ∧ actK (wordIK M MI w) (sv.getD 0 0) = sv.getD 0 0 ∧
      actK (wordIK M MI w) (sv.getD (m + 1) 0) = sv.getD (m + 1) 0 := by
  unfold witK at h
  rw [MatL.strictB_eq, MatL.allN_iff] at h
  have hm' := h m hm
  rw [MatL.strictB_eq, witL_iff, ngetW_eq, nget_eq, nget_eq] at hm'
  exact hm'

theorem witRows_eq {M MI : Nat → Nat} {W : List (List (List Int))} {sv : List Nat}
    (h : witK M MI W sv = true) {m : Nat} (hm : m < 3) :
    witRowsP W [unpack 24 24 (M 0), unpack 24 24 (M 1)] [unpack 24 24 (MI 0), unpack 24 24 (MI 1)] m =
      (valsK M MI (ngetW W m)).map (unpack 24 24) := by
  rw [valsK_eq, ngetW_eq, List.map_map, witRowsP, rows2 M, rows2 MI]
  apply List.map_congr_left
  intro w hw
  exact word_eq_wordIK (witK_spec h hm w hw).1

theorem wsRow_lt {Wl : List Nat} {c : Nat} (h : c / 24 < Wl.length) :
    wsRow Wl c = rowK (Wl.getD (c / 24) 0) (c % 24) := by
  have hb : Nat.blt (c / 24) (lenN Wl) = true := by
    rw [Nat.blt_eq, lenN_eq]
    exact h
  unfold wsRow
  rw [MatL.strictN_eq, MatL.strictN_eq]
  change nIf(Nat.blt (c / 24) (lenN Wl), rowK (nget Wl (c / 24)) (c % 24), 1 <<< (c % 24)) = _
  rw [hb, nget_eq]

theorem wsRow_ge {Wl : List Nat} {c : Nat} (h : ¬ c / 24 < Wl.length) :
    wsRow Wl c = 1 <<< (c % 24) := by
  have hb : Nat.blt (c / 24) (lenN Wl) = false := by
    rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq, lenN_eq]
    exact h
  unfold wsRow
  rw [MatL.strictN_eq, MatL.strictN_eq]
  change nIf(Nat.blt (c / 24) (lenN Wl), rowK (nget Wl (c / 24)) (c % 24), 1 <<< (c % 24)) = _
  rw [hb]

theorem fixCoef_eq (Wl : List Nat) (c u : Nat) :
    fixCoefP (Wl.map (unpack 24 24)) c u = coefK Wl c u := by
  have hr : c % 24 < 24 := Nat.mod_lt _ (by norm_num)
  have hrow : ((Wl.map (unpack 24 24)).getD (c / 24) one).getD (c % 24) 0 = wsRow Wl c := by
    by_cases h : c / 24 < Wl.length
    · rw [wsRow_lt h, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem h, Option.map_some, Option.getD_some, Array.getD_eq_getD_getElem?,
        MatL.unpack_getD _ _ hr, MatL.rowK_eq, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem h, Option.getD_some]
    · rw [wsRow_ge h, List.getD_eq_default _ _ (by rw [List.length_map]; omega)]
      simp [one, CFSG.Sporadic.SmallF2.Native.idRows, hr]
  unfold fixCoefP
  rw [hrow]
  change _ = Nat.beq (((wsRow Wl c ^^^ (1 <<< (c % 24))) >>> u) &&& 1) 1
  rw [ActL.and_one_beq, Nat.testBit_shiftRight, Nat.add_zero]

theorem combK_eq (Wl cs : List Nat) (v : Nat) :
    combK Wl cs v = cs.foldr (fun c b => coefK Wl c v ^^ b) false := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change Bool.rec (motive := fun _ => Bool) (combK Wl cs v) (bIf(combK Wl cs v, false, true))
      (coefK Wl c v) = _
    rw [List.foldr_cons, ← ih]
    cases coefK Wl c v <;> cases combK Wl cs v <;> rfl

theorem foldl_xor (f : Nat → Bool) (cs : List Nat) (b : Bool) :
    cs.foldl (fun b c => b ^^ f c) b = (b ^^ cs.foldr (fun c b => f c ^^ b) false) := by
  induction cs generalizing b with
  | nil => simp
  | cons c cs ih => rw [List.foldl_cons, ih, List.foldr_cons, Bool.xor_assoc]

theorem fixComb_eq (Wl cs : List Nat) (v : Nat) :
    fixCombP (Wl.map (unpack 24 24)) cs v = combK Wl cs v := by
  unfold fixCombP
  rw [foldl_xor, combK_eq, Bool.false_xor]
  simp only [fixCoef_eq]

theorem xorRec (c e : Bool) :
    Bool.rec (motive := fun _ => Bool) e (bIf(e, false, true)) c = (c != e) := by
  cases c <;> cases e <;> rfl

theorem orRec (c e : Bool) : Bool.rec (motive := fun _ => Bool) e true c = (c || e) := by
  cases c <;> rfl

theorem impRec (c t : Bool) : Bool.rec (motive := fun _ => Bool) true t c = (!c || t) := by
  cases c <;> rfl

theorem andNotRec (c e : Bool) : Bool.rec (motive := fun _ => Bool) e false c = (!c && e) := by
  cases c <;> rfl

theorem bltD (x y : Nat) : Nat.blt x y = decide (x < y) :=
  Bool.eq_iff_iff.2 (by rw [Nat.blt_eq, decide_eq_true_iff])

theorem beqD (x y : Nat) : Nat.beq x y = (x == y) :=
  Bool.eq_iff_iff.2 (by rw [Nat.beq_eq, beq_iff_eq])

theorem allDiv_eq (len : Nat) (l : List Nat) :
    List.rec (motive := fun _ => Bool) true
      (fun c _ ih => bAnd(Nat.blt (Nat.div c (nat_lit 24)) len, ih)) l =
      l.all fun c => decide (c / 24 < len) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [List.all_cons, ← ih, ← bltD]
    exact MatL.bAnd_eq _ _

theorem fixOne_eq (Wl : List Nat) (FF : List (Nat × Nat)) (FS : List (List (List Nat)))
    (sv : List Nat) (m : Nat) :
    fixOneK Wl FF FS sv m = fixCheckOfP FF FS sv m (Wl.map (unpack 24 24)) := by
  unfold fixOneK fixCheckOfP
  simp only [xorRec, allDiv_eq]
  simp only [MatL.strictB_eq, orRec, impRec, andNotRec, MatL.bAnd_eq, pairFst_eq,
    pairSnd_eq, nget_eq, ngetLL_eq, ngetL_eq, lenN_eq, bitK_eq, MatL.allN_eq, bltD,
    beqD, fixComb_eq, List.length_map, Nat.succ_eq_add_one, bne, Bool.and_assoc, Bool.or_assoc,
    Bool.and_true]

end StabL

theorem witK_sound {M MI : Nat → Nat} {W : List (List (List Int))} {sv : List Nat}
    (h : witK M MI W sv = true) :
    witCheckP W [unpack 24 24 (M 0), unpack 24 24 (M 1)] [unpack 24 24 (MI 0), unpack 24 24 (MI 1)]
      sv = true := by
  unfold witCheckP
  rw [List.all_eq_true]
  intro m hm
  rw [List.mem_range] at hm
  rw [StabL.witRows_eq h hm, List.all_eq_true]
  intro s hs
  rw [StabL.valsK_eq, StabL.ngetW_eq, List.map_map, List.mem_map] at hs
  obtain ⟨w, hw, rfl⟩ := hs
  obtain ⟨_, hz, hv⟩ := StabL.witK_spec h hm w hw
  simp only [Function.comp_apply, ActL.act_unpack, hz, hv, beq_self_eq_true, StabL.wf_unpack',
    Bool.and_self]

theorem fixK_sound {M MI : Nat → Nat} {W : List (List (List Int))} {FF : List (Nat × Nat)}
    {FS : List (List (List Nat))} {sv : List Nat} (hw : witK M MI W sv = true)
    (h : fixK M MI W FF FS sv = true) :
    fixCheckP W [unpack 24 24 (M 0), unpack 24 24 (M 1)] [unpack 24 24 (MI 0), unpack 24 24 (MI 1)]
      FF FS sv = true := by
  unfold fixK at h
  rw [MatL.allN_iff] at h
  unfold fixCheckP
  rw [List.all_eq_true]
  intro m hm
  rw [List.mem_range] at hm
  rw [StabL.witRows_eq hw hm, ← StabL.fixOne_eq]
  exact h m hm

end CFSG.KS.SporSch.M24

end
