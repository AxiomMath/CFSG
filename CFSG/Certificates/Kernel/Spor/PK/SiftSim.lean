module

public import CFSG.Certificates.Kernel.Spor.PK.ChainSim

public section

namespace CFSG.KS.PK

open CFSG.KC.Enum CFSG.KS

variable {n w LT NL : Nat}

namespace SiftSim

private theorem fd_enc_lt {f : Nat → Nat} (hw : n < 2 ^ w) (hf : ∀ x < n, f x < n) {j : Nat}
    (hj : j < n) : fd w (enc w f n) j = f j :=
  fd_enc (fun i hi => Nat.lt_trans (hf i hi) hw) hj

private theorem pg_enc {f : Nat → Nat} (hw : n < 2 ^ w) (hf : ∀ x < n, f x < n) {j : Nat}
    (hj : j < n) : pg w (mask w) (enc w f n) j = f j := by
  rw [pg_eq]
  exact fd_enc_lt hw hf hj

private theorem enc_lt_pow {f : Nat → Nat} (hw : n < 2 ^ w) (hf : ∀ x < n, f x < n) :
    enc w f n < 2 ^ (n * w) := by
  rw [Nat.mul_comm]
  exact enc_lt fun i hi => Nat.lt_trans (hf i hi) hw

private theorem pcomp_enc (hn32 : n < 2 ^ 32) (hw : n < 2 ^ w) {p q : Nat → Nat}
    (hp : ∀ x < n, p x < n) (hq : ∀ x < n, q x < n) :
    pcomp n w (mask w) (enc w p n) (enc w q n) = enc w (fun x => p (q x)) n := by
  rw [pcomp_eq hn32]
  exact enc_congr fun i hi => by rw [fd_enc_lt hw hq hi, fd_enc_lt hw hp (hq i hi)]

private theorem pcomp_blk (hn32 : n < 2 ^ 32) (hw : n < 2 ^ w) (LT l : Nat) {q : Nat → Nat}
    (hq : ∀ x < n, q x < n) :
    pcomp n w (mask w) (blk LT (n * w) (mask (n * w)) l) (enc w q n) =
      enc w (fun x => letF n w LT l (q x)) n := by
  rw [pcomp_eq hn32]
  refine enc_congr fun i hi => ?_
  rw [fd_enc_lt hw hq hi, blk_eq]
  rfl

private theorem pg_blk (LT l x : Nat) :
    pg w (mask w) (blk LT (n * w) (mask (n * w)) l) x = letF n w LT l x := by
  rw [pg_eq, blk_eq]
  rfl

private theorem getD_mem {l : List Nat} {k : Nat} (h : k < l.length) : l.getD k 0 ∈ l := by
  simp [List.getD_eq_getElem?_getD, h]

section Rec

variable {F : Nat → Nat → Nat} {s : BS}

private theorem recBS_ok (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w) (hs : GoodBS n F s) :
    RecOK n w s.pts.length (fun k => s.pts.getD k 0) (posBS w s)
      (fun k => if k < s.pts.length then enc w (BS.trans F s k) n else 0)
      (fun k => if k < s.pts.length then enc w (finv n (BS.trans F s k)) n else 0) := by
  obtain ⟨hpos, hle, -, hlt, hperm⟩ := hs
  have hn0 : 0 < n := Nat.lt_of_lt_of_le hpos hle
  unfold RecOK
  refine ⟨Nat.lt_of_le_of_lt hle hn16, fun k _ => ?_, fun x _ => ?_, fun k _ => ?_,
    fun k _ => ?_⟩
  · show s.pts.getD k 0 < 2 ^ w
    by_cases h : k < s.pts.length
    · have := hlt _ (getD_mem h)
      omega
    · simpa [List.getD_eq_getElem?_getD, h] using Nat.two_pow_pos w
  · show posBS w s x < 2 ^ w
    unfold posBS
    split
    · have := List.idxOf_lt_length_of_mem ‹x ∈ s.pts›
      omega
    · rw [mask_eq]
      have := Nat.two_pow_pos w
      omega
  · show (if k < s.pts.length then enc w (BS.trans F s k) n else 0) < 2 ^ (n * w)
    split
    · exact enc_lt_pow (by omega) fun x hx => (hperm k ‹_›).1 x hx
    · exact Nat.two_pow_pos _
  · show (if k < s.pts.length then enc w (finv n (BS.trans F s k)) n else 0) < 2 ^ (n * w)
    split
    · exact enc_lt_pow (by omega) fun x _ => finv_lt hn0 _ _
    · exact Nat.two_pow_pos _

private theorem rec_lcnt (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w) (hs : GoodBS n F s) (LV : Nat) :
    lcnt (recBS n w F s LV) = s.pts.length :=
  lcnt_recOf (recBS_ok hn16 hw hs)

private theorem rec_lpt (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w) (hs : GoodBS n F s) (LV : Nat)
    {k : Nat} (hk : k < n) : lpt w (mask w) (recBS n w F s LV) k = s.pts.getD k 0 :=
  lpt_recOf (recBS_ok hn16 hw hs) hk

private theorem rec_lpos (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w) (hs : GoodBS n F s) (LV : Nat)
    {x : Nat} (hx : x < n) : lpos w (mask w) (n * w) (recBS n w F s LV) x = posBS w s x :=
  lpos_recOf (recBS_ok hn16 hw hs) hx

private theorem rec_ltr (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w) (hs : GoodBS n F s) (LV : Nat)
    {k : Nat} (hk : k < s.pts.length) :
    ltr (n * w) (mask (n * w)) (recBS n w F s LV) k = enc w (BS.trans F s k) n := by
  have h : ltr (n * w) (mask (n * w)) (recBS n w F s LV) k =
      if k < s.pts.length then enc w (BS.trans F s k) n else 0 :=
    ltr_recOf (recBS_ok hn16 hw hs) (Nat.lt_of_lt_of_le hk hs.2.1)
  rw [h, if_pos hk]

private theorem rec_ltri (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w) (hs : GoodBS n F s) (LV : Nat)
    {k : Nat} (hk : k < s.pts.length) :
    ltri n (n * w) (mask (n * w)) (recBS n w F s LV) k = enc w (finv n (BS.trans F s k)) n := by
  have h : ltri n (n * w) (mask (n * w)) (recBS n w F s LV) k =
      if k < s.pts.length then enc w (finv n (BS.trans F s k)) n else 0 :=
    ltri_recOf (recBS_ok hn16 hw hs) (Nat.lt_of_lt_of_le hk hs.2.1)
  rw [h, if_pos hk]

private theorem rec_llv (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w) (hs : GoodBS n F s) (LV : Nat) :
    llv n (n * w) (recBS n w F s LV) = LV :=
  llv_recOf (recBS_ok hn16 hw hs)

private theorem posBS_lt_iff (hw : n + 1 < 2 ^ w) (hs : GoodBS n F s) (x : Nat) :
    posBS w s x < s.pts.length ↔ x ∈ s.pts := by
  unfold posBS
  by_cases hx : x ∈ s.pts
  · rw [if_pos hx]
    exact ⟨fun _ => hx, fun _ => List.idxOf_lt_length_of_mem hx⟩
  · rw [if_neg hx]
    refine ⟨fun h => ?_, fun h => absurd h hx⟩
    rw [mask_eq] at h
    have := hs.2.1
    have := Nat.two_pow_pos w
    omega

private theorem posBS_of_mem {x : Nat} (hx : x ∈ s.pts) : posBS w s x = s.pts.idxOf x := by
  unfold posBS
  rw [if_pos hx]

end Rec

private theorem sift_nil (n w m nw pm idn g : Nat) : sift n w m nw pm idn [] g = Nat.beq g idn :=
  rfl

private theorem sift_cons (n w m nw pm idn S : Nat) (Ls : List Nat) (g : Nat) :
    sift n w m nw pm idn (S :: Ls) g =
      if Nat.blt (lpos w m nw S (pg w m g (lpt w m S 0))) (lcnt S) = true then
        sift n w m nw pm idn Ls
          (pcomp n w m (ltri n nw pm S (lpos w m nw S (pg w m g (lpt w m S 0)))) g)
      else false := by
  simp only [sift, strictB_eq, bIf_eq]

private theorem schreierOK_def (n w m nw pm idn LT NL S : Nat) (rest : List Nat) :
    schreierOK n w m nw pm idn LT NL S rest =
      (List.range NL).all fun l =>
        if hasBit (llv n nw S) l = true then
          (List.range (lcnt S)).all fun k =>
            if Nat.blt (lpos w m nw S (pg w m (blk LT nw pm l) (lpt w m S k))) (lcnt S) = true then
              sift n w m nw pm idn rest
                (pcomp n w m
                  (ltri n nw pm S (lpos w m nw S (pg w m (blk LT nw pm l) (lpt w m S k))))
                  (pcomp n w m (blk LT nw pm l) (ltr nw pm S k)))
            else false
        else true := by
  simp only [schreierOK, strictB_eq, bIf_eq, allN_eq]

private theorem chainSch_cons (n w m nw pm idn LT NL S : Nat) (rest : List Nat) :
    chainSch n w m nw pm idn LT NL (S :: rest) =
      (schreierOK n w m nw pm idn LT NL S rest && chainSch n w m nw pm idn LT NL rest) := by
  simp only [chainSch, bAnd_eq]

end SiftSim

theorem sift_eq {F : Nat → Nat → Nat} (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w)
    {ps : List (BS × Nat)} (hps : ∀ p ∈ ps, GoodBS n F p.1) {g : Nat → Nat} (hg : ∀ x < n, g x < n) :
    sift n w (mask w) (n * w) (mask (n * w)) (pidn n w) (ps.map fun p => recBS n w F p.1 p.2)
      (enc w g n) = absSift n F (ps.map Prod.fst) g := by
  have hw' : n < 2 ^ w := by omega
  have hn32 : n < 2 ^ 32 := by omega
  induction ps generalizing g with
  | nil =>
    rw [List.map_nil, List.map_nil, SiftSim.sift_nil, absSift, pidn_eq (by omega) (by omega)]
    rw [Bool.eq_iff_iff, Nat.beq_eq, List.all_eq_true]
    constructor
    · intro h x hx
      have hxn := List.mem_range.1 hx
      have h1 := congrArg (fd w · x) h
      rw [SiftSim.fd_enc_lt hw' hg hxn, SiftSim.fd_enc_lt hw' (fun x hx => hx) hxn] at h1
      simpa using h1
    · intro h
      exact enc_congr fun x hx => beq_iff_eq.1 (h x (List.mem_range.2 hx))
  | cons p ps ih =>
    obtain ⟨s, LV⟩ := p
    have hs : GoodBS n F s := hps (s, LV) List.mem_cons_self
    have hps' : ∀ q ∈ ps, GoodBS n F q.1 := fun q hq => hps q (List.mem_cons_of_mem _ hq)
    have hpos : 0 < s.pts.length := hs.1
    have hn0 : 0 < n := Nat.lt_of_lt_of_le hpos hs.2.1
    have hr : s.pts.getD 0 0 < n := hs.2.2.2.1 _ (SiftSim.getD_mem hpos)
    rw [List.map_cons, List.map_cons, SiftSim.sift_cons, absSift]
    rw [SiftSim.rec_lpt hn16 hw hs LV hn0, SiftSim.pg_enc hw' hg hr,
      SiftSim.rec_lpos hn16 hw hs LV (hg _ hr), SiftSim.rec_lcnt hn16 hw hs LV]
    by_cases hm : g (s.pts.getD 0 0) ∈ s.pts
    · have hlt := List.idxOf_lt_length_of_mem hm
      have hc : Nat.blt (posBS w s (g (s.pts.getD 0 0))) s.pts.length = true := by
        rw [Nat.blt_eq, SiftSim.posBS_of_mem hm]
        exact hlt
      rw [if_pos hc, decide_eq_true hm, Bool.true_and, SiftSim.posBS_of_mem hm,
        SiftSim.rec_ltri hn16 hw hs LV hlt,
        SiftSim.pcomp_enc hn32 hw' (fun x _ => finv_lt hn0 _ _) hg]
      exact ih hps' (fun x _ => finv_lt hn0 _ _)
    · have hc : ¬ Nat.blt (posBS w s (g (s.pts.getD 0 0))) s.pts.length = true := by
        rw [Nat.blt_eq]
        exact fun h => hm ((SiftSim.posBS_lt_iff hw hs _).1 h)
      rw [if_neg hc, decide_eq_false hm, Bool.false_and]

theorem schreierOK_eq (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w)
    (hL : ∀ l < NL, IsPermN n (letF n w LT l)) {s : BS} (hs : GoodBS n (letF n w LT) s) (LV : Nat)
    {ps : List (BS × Nat)} (hps : ∀ p ∈ ps, GoodBS n (letF n w LT) p.1) :
    schreierOK n w (mask w) (n * w) (mask (n * w)) (pidn n w) LT NL (recBS n w (letF n w LT) s LV)
        (ps.map fun p => recBS n w (letF n w LT) p.1 p.2) =
      absSch n (letF n w LT) (maskL NL LV) s (ps.map Prod.fst) := by
  have hw' : n < 2 ^ w := by omega
  have hn32 : n < 2 ^ 32 := by omega
  have hpos : 0 < s.pts.length := hs.1
  have hle : s.pts.length ≤ n := hs.2.1
  have hn0 : 0 < n := Nat.lt_of_lt_of_le hpos hle
  rw [SiftSim.schreierOK_def, SiftSim.rec_llv hn16 hw hs LV, SiftSim.rec_lcnt hn16 hw hs LV]
  unfold absSch maskL
  rw [List.all_filter, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine forall_congr' fun l => imp_congr_right fun hl => ?_
  have hl' : l < NL := List.mem_range.1 hl
  by_cases hb : LV.testBit l = true
  · have hb' : hasBit LV l = true := by rw [hasBit_eq]; exact hb
    rw [if_pos hb', hb, Bool.not_true, Bool.false_or, List.all_eq_true, List.all_eq_true]
    refine forall_congr' fun k => imp_congr_right fun hk => ?_
    have hk' : k < s.pts.length := List.mem_range.1 hk
    have hkn : k < n := Nat.lt_of_lt_of_le hk' hle
    have hx : s.pts.getD k 0 < n := hs.2.2.2.1 _ (SiftSim.getD_mem hk')
    have hy : letF n w LT l (s.pts.getD k 0) < n := (hL l hl').1 _ hx
    have hk2 := hs.2.2.2.2 k hk'
    rw [SiftSim.pg_blk, SiftSim.rec_lpt hn16 hw hs LV hkn, SiftSim.rec_lpos hn16 hw hs LV hy]
    by_cases hm : letF n w LT l (s.pts.getD k 0) ∈ s.pts
    · have hlt := List.idxOf_lt_length_of_mem hm
      have hc : Nat.blt (posBS w s (letF n w LT l (s.pts.getD k 0))) s.pts.length = true := by
        rw [Nat.blt_eq, SiftSim.posBS_of_mem hm]
        exact hlt
      rw [if_pos hc, decide_eq_true hm, Bool.true_and, SiftSim.posBS_of_mem hm,
        SiftSim.rec_ltri hn16 hw hs LV hlt, SiftSim.rec_ltr hn16 hw hs LV hk',
        SiftSim.pcomp_blk hn32 hw' LT l hk2.1,
        SiftSim.pcomp_enc hn32 hw' (fun x _ => finv_lt hn0 _ _) fun x hx =>
          (hL l hl').1 _ (hk2.1 x hx)]
      rw [sift_eq hn16 hw hps fun x _ => finv_lt hn0 _ _]
    · have hc : ¬ Nat.blt (posBS w s (letF n w LT l (s.pts.getD k 0))) s.pts.length = true := by
        rw [Nat.blt_eq]
        exact fun h => hm ((SiftSim.posBS_lt_iff hw hs _).1 h)
      rw [if_neg hc, decide_eq_false hm, Bool.false_and]
  · have hb' : ¬ hasBit LV l = true := by rw [hasBit_eq]; exact hb
    have hb'' : LV.testBit l = false := by simpa using hb
    rw [if_neg hb', hb'']
    simp

theorem chainSch_eq (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w)
    (hL : ∀ l < NL, IsPermN n (letF n w LT l)) {ps : List (BS × Nat)}
    (hps : ∀ p ∈ ps, GoodBS n (letF n w LT) p.1) :
    chainSch n w (mask w) (n * w) (mask (n * w)) (pidn n w) LT NL
        (ps.map fun p => recBS n w (letF n w LT) p.1 p.2) = absChain n (letF n w LT) NL ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨s, LV⟩ := p
    have hs : GoodBS n (letF n w LT) s := hps (s, LV) List.mem_cons_self
    have hps' : ∀ q ∈ ps, GoodBS n (letF n w LT) q.1 := fun q hq =>
      hps q (List.mem_cons_of_mem _ hq)
    rw [List.map_cons, SiftSim.chainSch_cons, absChain, schreierOK_eq hn16 hw hL hs LV hps',
      ih hps']

end CFSG.KS.PK

end
