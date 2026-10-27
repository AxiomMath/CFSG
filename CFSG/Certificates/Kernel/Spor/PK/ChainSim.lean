module

public import CFSG.Certificates.Kernel.Spor.PK.BFSSim

public section

namespace CFSG.KS.PK

open CFSG.KC.Enum CFSG.KS

@[expose] def GoodBS (n : Nat) (F : Nat → Nat → Nat) (s : BS) : Prop :=
  0 < s.pts.length ∧ s.pts.length ≤ n ∧ s.pts.Nodup ∧ (∀ p ∈ s.pts, p < n) ∧
    ∀ k < s.pts.length, IsPermN n (BS.trans F s k)

@[expose] def absSift (n : Nat) (F : Nat → Nat → Nat) : List BS → (Nat → Nat) → Bool
  | [], g => (List.range n).all fun x => g x == x
  | s :: L, g =>
    decide (g (s.pts.getD 0 0) ∈ s.pts) &&
      absSift n F L fun x => finv n (BS.trans F s (s.pts.idxOf (g (s.pts.getD 0 0)))) (g x)

@[expose] def absSch (n : Nat) (F : Nat → Nat → Nat) (lv : List Nat) (s : BS) (L : List BS) :
    Bool :=
  lv.all fun l => (List.range s.pts.length).all fun k =>
    decide (F l (s.pts.getD k 0) ∈ s.pts) &&
      absSift n F L fun x =>
        finv n (BS.trans F s (s.pts.idxOf (F l (s.pts.getD k 0)))) (F l (BS.trans F s k x))

@[expose] def absChain (n : Nat) (F : Nat → Nat → Nat) (NL : Nat) : List (BS × Nat) → Bool
  | [] => true
  | p :: ps => absSch n F (maskL NL p.2) p.1 (ps.map Prod.fst) && absChain n F NL ps

@[expose] noncomputable def levPairs (n w LT NL : Nat) : List Nat → Nat → List (BS × Nat)
  | [], _ => []
  | b :: bs, LV => (BS.run (letF n w LT) (maskL NL LV) n b, LV) ::
      levPairs n w LT NL bs (fixMask w (mask w) (n * w) (mask (n * w)) LT NL LV b)

@[expose] noncomputable def levLast (n w LT NL : Nat) : List Nat → Nat → Nat
  | [], LV => LV
  | b :: bs, LV => levLast n w LT NL bs (fixMask w (mask w) (n * w) (mask (n * w)) LT NL LV b)

variable {n w LT NL : Nat}

theorem maskL_mask (NL : Nat) : maskL NL (mask NL) = List.range NL := by
  unfold maskL
  rw [List.filter_eq_self]
  intro l hl
  have hl' : l < NL := List.mem_range.mp hl
  simp [mask_eq, Nat.testBit_two_pow_sub_one, hl']

private theorem foldl_testBit (P : Nat → Bool) (L : List Nat) (M l : Nat) :
    (L.foldl (fun M i => if P i = true then M ||| 1 <<< i else M) M).testBit l =
      (M.testBit l || (decide (l ∈ L) && P l)) := by
  induction L generalizing M with
  | nil => simp
  | cons a L ih =>
    rw [List.foldl_cons, ih]
    by_cases hla : l = a
    · subst hla
      by_cases hP : P l = true
      · simp [hP, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
      · simp [hP]
    · have hal : a ≠ l := fun h => hla h.symm
      by_cases hP : P a = true
      · simp [hP, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, hal, hla]
      · simp [hP, hla]

private theorem pg_blk_eq (n w LT l b : Nat) :
    pg w (mask w) (blk LT (n * w) (mask (n * w)) l) b = letF n w LT l b := by
  rw [pg_eq, blk_eq]
  rfl

private theorem fixMask_testBit (LV b l : Nat) :
    (fixMask w (mask w) (n * w) (mask (n * w)) LT NL LV b).testBit l =
      (decide (l < NL) && (LV.testBit l && (letF n w LT l b == b))) := by
  unfold fixMask
  rw [foldUp_eq]
  have hf : (fun (s i : Nat) =>
      nIf(bAnd(hasBit LV i, Nat.beq (pg w (mask w) (blk LT (n * w) (mask (n * w)) i) b) b),
        Nat.lor s (Nat.shiftLeft 1 i), s)) =
      fun s i => if (LV.testBit i && (letF n w LT i b == b)) = true then s ||| 1 <<< i else s := by
    funext s i
    rw [nIf_eq, bAnd_eq, hasBit_eq, pg_blk_eq]
    have hb : Nat.beq (letF n w LT i b) b = (letF n w LT i b == b) := by
      apply Bool.eq_iff_iff.mpr
      rw [Nat.beq_eq, beq_iff_eq]
    rw [hb]
    rfl
  rw [hf, foldl_testBit (fun i => LV.testBit i && (letF n w LT i b == b)) (List.range NL) 0 l]
  simp [List.mem_range]

theorem maskL_fixMask (LV b : Nat) :
    maskL NL (fixMask w (mask w) (n * w) (mask (n * w)) LT NL LV b) =
      (maskL NL LV).filter fun l => letF n w LT l b == b := by
  unfold maskL
  rw [List.filter_filter]
  apply List.filter_congr
  intro l hl
  have hlt : l < NL := List.mem_range.mp hl
  rw [fixMask_testBit]
  simp [hlt, Bool.and_comm]

theorem goodBS_run {F : Nat → Nat → Nat} {lv : List Nat} {r : Nat} (hr : r < n)
    (hF : ∀ l ∈ lv, IsPermN n (F l)) : GoodBS n F (BS.run F lv n r) := by
  have hok := run_ok (n := n) (F := F) (lv := lv) (r := r) (fun l hl => (hF l hl).1) hr
  exact ⟨hok.pos, hok.le, hok.nodup, hok.lt, fun k hk => trans_isPermN hok hF hk⟩

theorem levels_eq (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w)
    (hL : ∀ l < NL, IsPermN n (letF n w LT l)) {bs : List Nat} (hbs : ∀ b ∈ bs, b < n) (LV : Nat)
    (k : List Nat → Nat → Bool) :
    levels n w (mask w) (n * w) (mask (n * w)) (pidn n w) LT NL bs LV k =
      k ((levPairs n w LT NL bs LV).map fun p => recBS n w (letF n w LT) p.1 p.2)
        (levLast n w LT NL bs LV) := by
  induction bs generalizing LV k with
  | nil => rfl
  | cons b bs ih =>
    have hb : b < n := hbs b List.mem_cons_self
    have hbs' : ∀ c ∈ bs, c < n := fun c hc => hbs c (List.mem_cons_of_mem _ hc)
    have hLV : ∀ l ∈ maskL NL LV, IsPermN n (letF n w LT l) := fun l hl =>
      hL l (List.mem_range.mp (List.mem_filter.mp hl).1)
    show strictB (bfs n w (mask w) (n * w) (mask (n * w)) (pidn n w) LT NL LV b) (fun S =>
      strictB (fixMask w (mask w) (n * w) (mask (n * w)) LT NL LV b) (fun LV' =>
        levels n w (mask w) (n * w) (mask (n * w)) (pidn n w) LT NL bs LV'
          (fun Ls LVt => k (S :: Ls) LVt))) = _
    rw [strictB_eq, bfs_eq hn16 hw hb hLV, strictB_eq, ih hbs']
    rfl

private theorem recBS_ok {F : Nat → Nat → Nat} {s : BS} (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w)
    (hs : GoodBS n F s) :
    RecOK n w s.pts.length (fun k => s.pts.getD k 0) (posBS w s)
      (fun k => if k < s.pts.length then enc w (BS.trans F s k) n else 0)
      (fun k => if k < s.pts.length then enc w (finv n (BS.trans F s k)) n else 0) := by
  obtain ⟨hpos, hle, -, hlt, hperm⟩ := hs
  have hnw : n < 2 ^ w := by omega
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · intro k _
    show s.pts.getD k 0 < 2 ^ w
    by_cases h : k < s.pts.length
    · rw [← List.getElem_eq_getD 0 (h := h)]
      exact Nat.lt_trans (hlt _ (List.getElem_mem h)) hnw
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      exact Nat.two_pow_pos w
  · intro x _
    show posBS w s x < 2 ^ w
    unfold posBS
    split
    · rename_i hx
      have := List.idxOf_lt_length_iff.mpr hx
      omega
    · rw [mask_eq]
      have := Nat.two_pow_pos w
      omega
  · intro k _
    show (if k < s.pts.length then enc w (BS.trans F s k) n else 0) < 2 ^ (n * w)
    split
    · rename_i hk
      rw [Nat.mul_comm n w]
      exact enc_lt fun i hi => Nat.lt_trans ((hperm k hk).1 i hi) hnw
    · exact Nat.two_pow_pos _
  · intro k _
    show (if k < s.pts.length then enc w (finv n (BS.trans F s k)) n else 0) < 2 ^ (n * w)
    split
    · rw [Nat.mul_comm n w]
      exact enc_lt fun i hi => Nat.lt_trans (finv_lt (by omega) _ _) hnw
    · exact Nat.two_pow_pos _

theorem lcnt_recBS {F : Nat → Nat → Nat} {s : BS} (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w)
    (hs : GoodBS n F s) (LV : Nat) : lcnt (recBS n w F s LV) = s.pts.length :=
  lcnt_recOf (recBS_ok hn16 hw hs)

private theorem lpos_recBS {F : Nat → Nat → Nat} {s : BS} (hn16 : n < 2 ^ 16)
    (hw : n + 1 < 2 ^ w) (hs : GoodBS n F s) (LV : Nat) {p : Nat} (hp : p < n) :
    lpos w (mask w) (n * w) (recBS n w F s LV) p = posBS w s p :=
  lpos_recOf (recBS_ok hn16 hw hs) hp

private theorem lpt_recBS {F : Nat → Nat → Nat} {s : BS} (hn16 : n < 2 ^ 16)
    (hw : n + 1 < 2 ^ w) (hs : GoodBS n F s) (LV : Nat) {k : Nat} (hk : k < n) :
    lpt w (mask w) (recBS n w F s LV) k = s.pts.getD k 0 :=
  lpt_recOf (recBS_ok hn16 hw hs) hk

theorem maskId_iff (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w) (LV : Nat) :
    maskId (n * w) (mask (n * w)) (pidn n w) LT NL LV = true ↔
      ∀ l ∈ maskL NL LV, ∀ x < n, letF n w LT l x = x := by
  have hidn : pidn n w = enc w (fun i => i) n := pidn_eq (by omega) (by omega)
  have hnw : n < 2 ^ w := by omega
  have hid : ∀ x < n, fd w (enc w (fun i => i) n) x = x := fun x hx =>
    fd_enc (fun i hi => Nat.lt_trans hi hnw) hx
  have key : ∀ l, Nat.beq (blk LT (n * w) (mask (n * w)) l) (pidn n w) = true ↔
      ∀ x < n, letF n w LT l x = x := by
    intro l
    rw [Nat.beq_eq, hidn, blk_eq]
    constructor
    · intro h x hx
      have h1 : fd w (LT / 2 ^ (n * w * l) % 2 ^ (n * w)) x = fd w (enc w (fun i => i) n) x := by
        rw [h]
      rw [hid x hx] at h1
      exact h1
    · intro h
      apply eq_of_fd_eq (w := w) (len := n)
      · rw [Nat.mul_comm w n]
        exact Nat.mod_lt _ (Nat.two_pow_pos _)
      · exact enc_lt fun i hi => Nat.lt_trans hi hnw
      · intro x hx
        rw [hid x hx]
        exact h x hx
  unfold maskId
  rw [allN_iff]
  constructor
  · intro h l hl x hx
    obtain ⟨hlmem, hbit⟩ := List.mem_filter.mp hl
    have h1 := h l (List.mem_range.mp hlmem)
    rw [bIf_eq, hasBit_eq, if_pos hbit] at h1
    exact (key l).mp h1 x hx
  · intro h l hlt
    rw [bIf_eq, hasBit_eq]
    split
    · rename_i hbit
      exact (key l).mpr (h l (List.mem_filter.mpr ⟨List.mem_range.mpr hlt, hbit⟩))
    · rfl

theorem sizesEq_iff (Ls L : List Nat) : sizesEq Ls L = true ↔ Ls.map lcnt = L := by
  induction Ls generalizing L with
  | nil =>
    cases L with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons x xs => exact ⟨fun h => Bool.noConfusion h, fun h => by simp at h⟩
  | cons S Ls ih =>
    cases L with
    | nil => exact ⟨fun h => Bool.noConfusion h, fun h => by simp at h⟩
    | cons x xs =>
      have h : sizesEq (S :: Ls) (x :: xs) = (Nat.beq (lcnt S) x && sizesEq Ls xs) := by
        rw [← bAnd_eq]
        rfl
      rw [h, Bool.and_eq_true, Nat.beq_eq, ih xs, List.map_cons, List.cons.injEq]

theorem coverOK_iff {F : Nat → Nat → Nat} {s : BS} (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w)
    (hs : GoodBS n F s) (LV i : Nat) :
    CFSG.KS.Mathieu.coverOK n w (mask w) (n * w) (recBS n w F s LV) i = true ↔ ∀ p < n, i ≤ p → p ∈ s.pts := by
  have hcnt := lcnt_recBS hn16 hw hs LV
  have hle : s.pts.length ≤ n := hs.2.1
  have key : ∀ p < n,
      (Nat.blt (lpos w (mask w) (n * w) (recBS n w F s LV) p) (lcnt (recBS n w F s LV)) &&
        Nat.beq (lpt w (mask w) (recBS n w F s LV)
          (lpos w (mask w) (n * w) (recBS n w F s LV) p)) p) = true ↔ p ∈ s.pts := by
    intro p hp
    rw [lpos_recBS hn16 hw hs LV hp, hcnt]
    unfold posBS
    split
    · rename_i hmem
      have hidx : s.pts.idxOf p < s.pts.length := List.idxOf_lt_length_iff.mpr hmem
      rw [lpt_recBS hn16 hw hs LV (Nat.lt_of_lt_of_le hidx hle),
        ← List.getElem_eq_getD 0 (h := hidx), List.getElem_idxOf]
      rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]
      exact ⟨fun _ => hmem, fun _ => ⟨hidx, rfl⟩⟩
    · rename_i hmem
      have h2 : ¬ (mask w < s.pts.length) := by
        rw [mask_eq]
        have := Nat.two_pow_pos w
        omega
      rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]
      exact ⟨fun h => absurd h.1 h2, fun h => absurd h hmem⟩
  unfold CFSG.KS.Mathieu.coverOK
  rw [allN_iff]
  constructor
  · intro h p hp hip
    have h1 := h p hp
    rw [bIf_eq, if_neg (by rw [Nat.blt_eq]; omega), strictB_eq, bAnd_eq] at h1
    exact (key p hp).mp h1
  · intro h p hp
    rw [bIf_eq]
    split
    · rfl
    · rename_i hnl
      have hip : i ≤ p := by
        rw [Nat.blt_eq] at hnl
        omega
      rw [strictB_eq, bAnd_eq]
      exact (key p hp).mpr (h p hp hip)

theorem lget_eq (Ls : List Nat) (i : Nat) : lget Ls i = Ls.getD i 0 := by
  induction Ls generalizing i with
  | nil => simp [lget]
  | cons S Ls ih =>
    cases i with
    | zero => rfl
    | succ j => exact (ih j).trans List.getD_cons_succ.symm

end CFSG.KS.PK

end
