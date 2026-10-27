module

public import CFSG.Certificates.Kernel.Spor.PK.Rec
public import CFSG.Certificates.Kernel.Spor.PK.BFS
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Inv

public section

namespace CFSG.KS.PK

open CFSG.KC.Enum CFSG.KS

@[expose] def letF (n w LT : Nat) (l x : Nat) : Nat := fd w (fd (n * w) LT l) x

@[expose] def maskL (NL LV : Nat) : List Nat := (List.range NL).filter fun l => LV.testBit l

@[expose] noncomputable def posBS (w : Nat) (s : BS) (x : Nat) : Nat := if x ∈ s.pts then s.pts.idxOf x else mask w

@[expose] noncomputable def recBS (n w : Nat) (F : Nat → Nat → Nat) (s : BS) (LV : Nat) : Nat :=
  recOf n w s.pts.length (fun k => s.pts.getD k 0) (posBS w s)
    (fun k => if k < s.pts.length then enc w (BS.trans F s k) n else 0)
    (fun k => if k < s.pts.length then enc w (finv n (BS.trans F s k)) n else 0) LV

private theorem bs_nfacts {n w : Nat} (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w) :
    n ≤ 2 ^ 24 ∧ n < 2 ^ 32 ∧ n < 2 ^ w ∧ n < mask w := by
  have h1 : 2 ^ 16 ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) (by decide)
  have h2 : 2 ^ 16 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by decide)
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [mask_eq]
  omega

private theorem bs_getD_mem {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 ∈ l := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

private theorem bs_getD_of_le {l : List Nat} {i : Nat} (h : l.length ≤ i) : l.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

private structure BSInv (n : Nat) (lv : List Nat) (s : BS) : Prop where
  len_par : s.par.length = s.pts.length
  len_lab : s.lab.length = s.pts.length
  pos : 0 < s.pts.length
  nodup : s.pts.Nodup
  lt : ∀ p ∈ s.pts, p < n
  lab_mem : ∀ k, 0 < k → k < s.pts.length → s.lab.getD k 0 ∈ lv

private theorem BSInv.le {n : Nat} {lv : List Nat} {s : BS} (hs : BSInv n lv s) :
    s.pts.length ≤ n := by
  have := hs.nodup.length_le_of_subset (l₂ := List.range n)
    (fun x hx => List.mem_range.2 (hs.lt x hx))
  simpa using this

private theorem BSInv.perm {n : Nat} {F : Nat → Nat → Nat} {lv : List Nat} {s : BS}
    (hs : BSInv n lv s) (hF : ∀ l ∈ lv, IsPermN n (F l)) :
    ∀ k, k < s.pts.length → IsPermN n (BS.trans F s k) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk
    by_cases hc : 0 < k ∧ s.par.getD k 0 < k
    · have e : BS.trans F s k = fun x => F (s.lab.getD k 0) (BS.trans F s (s.par.getD k 0) x) := by
        funext x
        rw [BS.trans.eq_1, dif_pos hc]
      rw [e]
      exact (hF _ (hs.lab_mem k hc.1 hk)).comp (ih _ hc.2 (by omega))
    · have e : BS.trans F s k = fun x => x := by
        funext x
        rw [BS.trans.eq_1, dif_neg hc]
      rw [e]
      exact isPermN_id n

private theorem bs_trans_congr {F : Nat → Nat → Nat} {s s' : BS} :
    ∀ k, (∀ j ≤ k, s'.par.getD j 0 = s.par.getD j 0 ∧ s'.lab.getD j 0 = s.lab.getD j 0) →
      BS.trans F s' k = BS.trans F s k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk
    funext x
    have h1 := hk k (Nat.le_refl k)
    rw [BS.trans.eq_1 F s', BS.trans.eq_1 F s, h1.1, h1.2]
    by_cases hc : 0 < k ∧ s.par.getD k 0 < k
    · rw [dif_pos hc, dif_pos hc, ih _ hc.2 (fun j hj => hk j (by omega))]
    · rw [dif_neg hc, dif_neg hc]

private theorem bs_letter_of_mem {F : Nat → Nat → Nat} {h p l : Nat} {s : BS} (hm : F l p ∈ s.pts) :
    BS.letter F h p s l = s := by
  unfold BS.letter
  rw [if_pos hm]

private theorem bs_letter_of_not_mem {F : Nat → Nat → Nat} {h p l : Nat} {s : BS}
    (hm : F l p ∉ s.pts) :
    BS.letter F h p s l = ⟨s.pts ++ [F l p], s.par ++ [h], s.lab ++ [l]⟩ := by
  unfold BS.letter
  rw [if_neg hm]

private theorem bs_letter_inv {n : Nat} {F : Nat → Nat → Nat} {lv : List Nat} {s : BS} {h p l : Nat}
    (hs : BSInv n lv s) (hl : l ∈ lv) (hq : F l p < n) : BSInv n lv (BS.letter F h p s l) := by
  by_cases hm : F l p ∈ s.pts
  · rw [bs_letter_of_mem hm]
    exact hs
  · rw [bs_letter_of_not_mem hm]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hs.len_par]
    · simp [hs.len_lab]
    · simp
    · refine List.nodup_append.2
        ⟨hs.nodup, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      exact fun e => hm (e ▸ ha)
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · exact hs.lt x hx
      · rw [hx]
        exact hq
    · intro k hk hk'
      simp only [List.length_append, List.length_singleton] at hk'
      by_cases hkc : k < s.pts.length
      · have : s.lab.getD k 0 ∈ lv := hs.lab_mem k hk hkc
        simp only [List.getD_eq_getElem?_getD] at this ⊢
        rwa [List.getElem?_append_left (by rw [hs.len_lab]; exact hkc)]
      · have hk2 : k = s.pts.length := by omega
        subst hk2
        simp [List.getD_eq_getElem?_getD, hs.len_lab, hl]

private theorem bs_foldl_letter_inv {n : Nat} {F : Nat → Nat → Nat} {lv : List Nat} {h p : Nat}
    (hp : ∀ l ∈ lv, F l p < n) :
    ∀ (ls : List Nat), (∀ l ∈ ls, l ∈ lv) → ∀ {s : BS}, BSInv n lv s →
      BSInv n lv (ls.foldl (BS.letter F h p) s)
  | [], _, _, hs => hs
  | l :: ls, hls, s, hs => by
      simp only [List.foldl_cons]
      exact bs_foldl_letter_inv hp ls (fun x hx => hls x (List.mem_cons_of_mem _ hx))
        (bs_letter_inv hs (hls l List.mem_cons_self) (hp l (hls l List.mem_cons_self)))

private theorem bs_step_inv {n : Nat} {F : Nat → Nat → Nat} {lv : List Nat} {s : BS}
    (hF : ∀ l ∈ lv, ∀ x < n, F l x < n) (hs : BSInv n lv s) (h : Nat) :
    BSInv n lv (BS.step F lv s h) := by
  unfold BS.step
  split
  · rename_i hh
    exact bs_foldl_letter_inv (fun l hl => hF l hl _ (hs.lt _ (bs_getD_mem hh))) lv
      (fun l hl => hl) hs
  · exact hs

private theorem bs_letter_length_le {F : Nat → Nat → Nat} {h p l : Nat} {s : BS} :
    s.pts.length ≤ (BS.letter F h p s l).pts.length := by
  unfold BS.letter
  split
  · exact Nat.le_refl _
  · simp

private theorem bs_letter_getD {F : Nat → Nat → Nat} {h p l : Nat} {s : BS} {k : Nat}
    (hk : k < s.pts.length) : (BS.letter F h p s l).pts.getD k 0 = s.pts.getD k 0 := by
  unfold BS.letter
  split
  · rfl
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]

private theorem bs_letter_trans {n : Nat} {F : Nat → Nat → Nat} {lv : List Nat} {s : BS}
    {h p l k : Nat} (hs : BSInv n lv s) (hk : k < s.pts.length) :
    BS.trans F (BS.letter F h p s l) k = BS.trans F s k := by
  unfold BS.letter
  split
  · rfl
  · refine bs_trans_congr k fun j hj => ?_
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by rw [hs.len_par]; omega),
      List.getElem?_append_left (by rw [hs.len_lab]; omega)]
    exact ⟨rfl, rfl⟩

private theorem bs_posBS_lt {w : Nat} {s : BS} {x : Nat} (hx : x ∈ s.pts) :
    posBS w s x < s.pts.length := by
  unfold posBS
  rw [if_pos hx]
  exact List.idxOf_lt_length_of_mem hx

private theorem bs_recOK_recBS {n w : Nat} {F : Nat → Nat → Nat} {lv : List Nat} {s : BS}
    (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w) (hF : ∀ l ∈ lv, IsPermN n (F l)) (hs : BSInv n lv s) :
    RecOK n w s.pts.length (fun k => s.pts.getD k 0) (posBS w s)
      (fun k => if k < s.pts.length then enc w (BS.trans F s k) n else 0)
      (fun k => if k < s.pts.length then enc w (finv n (BS.trans F s k)) n else 0) := by
  obtain ⟨-, -, hnw, hnm⟩ := bs_nfacts hn16 hw
  have hle := hs.le
  have hw0 : 0 < 2 ^ w := Nat.two_pow_pos w
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · intro k _
    show s.pts.getD k 0 < 2 ^ w
    by_cases hk : k < s.pts.length
    · have := hs.lt _ (bs_getD_mem hk)
      omega
    · rw [bs_getD_of_le (by omega)]
      exact hw0
  · intro x _
    by_cases hx : x ∈ s.pts
    · have := bs_posBS_lt (w := w) hx
      omega
    · unfold posBS
      rw [if_neg hx, mask_eq]
      omega
  · intro k _
    show (if k < s.pts.length then enc w (BS.trans F s k) n else 0) < 2 ^ (n * w)
    by_cases hk : k < s.pts.length
    · rw [if_pos hk, Nat.mul_comm n w]
      refine enc_lt fun i hi => ?_
      have := (hs.perm hF k hk).1 i hi
      omega
    · rw [if_neg hk]
      exact Nat.two_pow_pos _
  · intro k _
    show (if k < s.pts.length then enc w (finv n (BS.trans F s k)) n else 0) < 2 ^ (n * w)
    by_cases hk : k < s.pts.length
    · rw [if_pos hk, Nat.mul_comm n w]
      refine enc_lt fun i hi => ?_
      have := (hs.perm hF k hk).finv.1 i hi
      omega
    · rw [if_neg hk]
      exact Nat.two_pow_pos _

private theorem bs_recOf_congr {n w c : Nat} {P P' Pos Pos' T T' Ti Ti' : Nat → Nat} {LV : Nat}
    (hP : ∀ k < n, P k = P' k) (hPos : ∀ x < n, Pos x = Pos' x) (hT : ∀ k < n, T k = T' k)
    (hTi : ∀ k < n, Ti k = Ti' k) :
    recOf n w c P Pos T Ti LV = recOf n w c P' Pos' T' Ti' LV := by
  unfold recOf
  rw [enc_congr hP, enc_congr hPos, enc_congr hT, enc_congr hTi]

private abbrev bsSnoc (s : BS) (q h l : Nat) : BS := ⟨s.pts ++ [q], s.par ++ [h], s.lab ++ [l]⟩

private theorem bs_getD_append_single (l : List Nat) (q k : Nat) :
    (l ++ [q]).getD k 0 = if k = l.length then q else l.getD k 0 := by
  by_cases h1 : k < l.length
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left h1]
  · by_cases h2 : k = l.length
    · subst h2
      simp [List.getD_eq_getElem?_getD]
    · rw [if_neg h2]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by simp; omega),
        List.getElem?_eq_none (by omega)]

private theorem bs_snoc_trans_old {F : Nat → Nat → Nat} {s : BS}
    (hpar : s.par.length = s.pts.length) (hlab : s.lab.length = s.pts.length) {q h l k : Nat}
    (hk : k < s.pts.length) :
    BS.trans F (bsSnoc s q h l) k = BS.trans F s k := by
  refine bs_trans_congr k fun j hj => ?_
  show (s.par ++ [h]).getD j 0 = s.par.getD j 0 ∧ (s.lab ++ [l]).getD j 0 = s.lab.getD j 0
  rw [bs_getD_append_single, bs_getD_append_single, if_neg (by omega), if_neg (by omega)]
  exact ⟨rfl, rfl⟩

private theorem bs_snoc_trans_new {F : Nat → Nat → Nat} {s : BS}
    (hpar : s.par.length = s.pts.length) (hlab : s.lab.length = s.pts.length)
    (hpos : 0 < s.pts.length) {q h l : Nat} (hh : h < s.pts.length) :
    BS.trans F (bsSnoc s q h l) s.pts.length = fun x => F l (BS.trans F s h x) := by
  funext x
  rw [BS.trans.eq_1]
  have h1 : (bsSnoc s q h l).par.getD s.pts.length 0 = h := by
    show (s.par ++ [h]).getD s.pts.length 0 = h
    rw [bs_getD_append_single, if_pos hpar.symm]
  have h2 : (bsSnoc s q h l).lab.getD s.pts.length 0 = l := by
    show (s.lab ++ [l]).getD s.pts.length 0 = l
    rw [bs_getD_append_single, if_pos hlab.symm]
  have hc : 0 < s.pts.length ∧ (bsSnoc s q h l).par.getD s.pts.length 0 < s.pts.length :=
    ⟨hpos, by rw [h1]; exact hh⟩
  rw [dif_pos hc, h1, h2, bs_snoc_trans_old hpar hlab hh]

private theorem bs_upd_same (f : Nat → Nat) (i v : Nat) : upd f i v i = v := by
  unfold upd
  rw [if_pos rfl]

private theorem bs_upd_other {f : Nat → Nat} {i v j : Nat} (h : j ≠ i) : upd f i v j = f j := by
  unfold upd
  rw [if_neg h]

private theorem bs_posBS_snoc {w : Nat} {s : BS} {q h l : Nat} (hm : q ∉ s.pts) (x : Nat) :
    posBS w (bsSnoc s q h l) x = upd (posBS w s) q s.pts.length x := by
  by_cases hx : x = q
  · subst hx
    rw [bs_upd_same]
    unfold posBS
    rw [if_pos (by simp)]
    show (s.pts ++ [x]).idxOf x = _
    rw [List.idxOf_append, if_neg hm]
    simp
  · rw [bs_upd_other hx]
    unfold posBS
    by_cases hxs : x ∈ s.pts
    · rw [if_pos (by simp [hxs]), if_pos hxs]
      show (s.pts ++ [q]).idxOf x = _
      rw [List.idxOf_append, if_pos hxs]
    · rw [if_neg (by simp [hxs, hx]), if_neg hxs]

private theorem bs_recBS_snoc {n w : Nat} {F : Nat → Nat → Nat} {lv : List Nat} {s : BS}
    (hs : BSInv n lv s) {q h l : Nat} (hm : q ∉ s.pts) (hh : h < s.pts.length) (LV : Nat) :
    recBS n w F (bsSnoc s q h l) LV =
      recOf n w (s.pts.length + 1) (upd (fun k => s.pts.getD k 0) s.pts.length q)
        (upd (posBS w s) q s.pts.length)
        (upd (fun k => if k < s.pts.length then enc w (BS.trans F s k) n else 0) s.pts.length
          (enc w (fun x => F l (BS.trans F s h x)) n))
        (upd (fun k => if k < s.pts.length then enc w (finv n (BS.trans F s k)) n else 0)
          s.pts.length (enc w (finv n (fun x => F l (BS.trans F s h x))) n)) LV := by
  have hlen : (bsSnoc s q h l).pts.length = s.pts.length + 1 := by simp
  unfold recBS
  rw [hlen]
  refine bs_recOf_congr ?_ ?_ ?_ ?_
  · intro k _
    show (s.pts ++ [q]).getD k 0 = upd (fun k => s.pts.getD k 0) s.pts.length q k
    rw [bs_getD_append_single]
    rfl
  · intro x _
    exact bs_posBS_snoc hm x
  · intro k _
    show (if k < s.pts.length + 1 then enc w (BS.trans F (bsSnoc s q h l) k) n else 0) = _
    by_cases hk : k < s.pts.length
    · rw [if_pos (by omega), bs_upd_other (by omega), if_pos hk,
        bs_snoc_trans_old hs.len_par hs.len_lab hk]
    · by_cases hkc : k = s.pts.length
      · subst hkc
        rw [if_pos (by omega), bs_upd_same, bs_snoc_trans_new hs.len_par hs.len_lab hs.pos hh]
      · rw [if_neg (by omega), bs_upd_other hkc, if_neg hk]
  · intro k _
    show (if k < s.pts.length + 1 then enc w (finv n (BS.trans F (bsSnoc s q h l) k)) n else 0) = _
    by_cases hk : k < s.pts.length
    · rw [if_pos (by omega), bs_upd_other (by omega), if_pos hk,
        bs_snoc_trans_old hs.len_par hs.len_lab hk]
    · by_cases hkc : k = s.pts.length
      · subst hkc
        rw [if_pos (by omega), bs_upd_same, bs_snoc_trans_new hs.len_par hs.len_lab hs.pos hh]
      · rw [if_neg (by omega), bs_upd_other hkc, if_neg hk]

private theorem bs_fd_blk (LT n w l x : Nat) :
    fd w (blk LT (n * w) (mask (n * w)) l) x = letF n w LT l x := by
  rw [blk_eq]
  rfl

private theorem bs_pg_blk (LT n w l p : Nat) :
    pg w (mask w) (blk LT (n * w) (mask (n * w)) l) p = letF n w LT l p := by
  rw [pg_eq]
  exact bs_fd_blk LT n w l p

private theorem bs_pcomp_new {n w LT l tp : Nat} {G : Nat → Nat} (hn16 : n < 2 ^ 16)
    (hw : n + 1 < 2 ^ w) (hG : IsPermN n G) (hGtp : enc w G n = tp) :
    pcomp n w (mask w) (blk LT (n * w) (mask (n * w)) l) tp =
      enc w (fun x => letF n w LT l (G x)) n := by
  obtain ⟨-, hn32, hnw, -⟩ := bs_nfacts hn16 hw
  rw [pcomp_eq hn32]
  refine enc_congr fun i hi => ?_
  rw [bs_fd_blk, ← hGtp, fd_enc (fun j hj => by have := hG.1 j hj; omega) hi]

private theorem bs_pinvS_new {n w : Nat} {G : Nat → Nat} (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w)
    (hG : IsPermN n G) : pinvS n w (mask w) (enc w G n) = enc w (finv n G) n := by
  obtain ⟨-, -, hnw, -⟩ := bs_nfacts hn16 hw
  have hGw : ∀ i < n, G i < 2 ^ w := fun i hi => by have := hG.1 i hi; omega
  refine pinvS_eq (Nat.le_of_lt hnw) (fun i hi => ?_) (fun j hj => ?_) (fun i hi => ?_)
  · rw [fd_enc hGw hi]
    exact hG.1 i hi
  · obtain ⟨h1, h2⟩ := finv_spec hG hj
    rw [fd_enc hGw h1]
    exact ⟨h1, h2⟩
  · rw [fd_enc hGw hi]
    exact finv_apply hG hi

private theorem bs_enc_lt_perm {n w : Nat} {G : Nat → Nat} (hnw : n < 2 ^ w) (hG : IsPermN n G) :
    enc w G n < 2 ^ (n * w) := by
  rw [Nat.mul_comm n w]
  exact enc_lt fun i hi => by have := hG.1 i hi; omega

private theorem bs_bfsLetter_eq {n w LT NL LV h p tp l : Nat} {s : BS}
    (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w)
    (hL : ∀ l ∈ maskL NL LV, IsPermN n (letF n w LT l))
    (hs : BSInv n (maskL NL LV) s) (hh : h < s.pts.length) (hp : s.pts.getD h 0 = p)
    (htp : enc w (BS.trans (letF n w LT) s h) n = tp) (hl : l ∈ maskL NL LV) :
    bfsLetter n w (mask w) (n * w) (mask (n * w)) LT p tp l (recBS n w (letF n w LT) s LV) =
      recBS n w (letF n w LT) (BS.letter (letF n w LT) h p s l) LV := by
  obtain ⟨-, -, hnw, hnm⟩ := bs_nfacts hn16 hw
  have hOK := bs_recOK_recBS hn16 hw hL hs
  have hF := hL l hl
  have hpn : p < n := by rw [← hp]; exact hs.lt _ (bs_getD_mem hh)
  have hq : letF n w LT l p < n := hF.1 p hpn
  unfold bfsLetter
  simp only [strictN_eq, nIf_eq]
  have hpos : lpos w (mask w) (n * w) (recBS n w (letF n w LT) s LV) (letF n w LT l p) =
      posBS w s (letF n w LT l p) := lpos_recOf hOK hq
  rw [bs_pg_blk, hpos]
  by_cases hm : letF n w LT l p ∈ s.pts
  · have h1 := bs_posBS_lt (w := w) hm
    have h2 := hs.le
    simp only [Nat.beq_eq]
    rw [if_neg (by omega), bs_letter_of_mem hm]
  · have hposq : posBS w s (letF n w LT l p) = mask w := by
      unfold posBS
      rw [if_neg hm]
    have hinv' := bs_letter_inv (h := h) (p := p) hs hl hq
    rw [bs_letter_of_not_mem hm] at hinv'
    have hle' := hinv'.le
    simp only [List.length_append, List.length_singleton] at hle'
    have hG := (hL l hl).comp (hs.perm hL h hh)
    rw [hposq, Nat.beq_refl, if_pos rfl, bs_letter_of_not_mem hm]
    show _ = recBS n w (letF n w LT) (bsSnoc s (letF n w LT l p) h l) LV
    rw [bs_recBS_snoc hs hm hh, bs_pcomp_new hn16 hw (hs.perm hL h hh) htp, bs_pinvS_new hn16 hw hG]
    unfold recBS
    rw [lAdd_eq hOK (by omega) (by omega) hq hnw (bs_getD_of_le (Nat.le_refl _))
      (if_neg (Nat.lt_irrefl _)) (if_neg (Nat.lt_irrefl _)) hposq (bs_enc_lt_perm hnw hG)
      (bs_enc_lt_perm hnw hG.finv)]

private theorem bs_loop_eq {n w LT NL LV h p tp : Nat} (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w)
    (hL : ∀ l ∈ maskL NL LV, IsPermN n (letF n w LT l)) :
    ∀ (ls : List Nat), (∀ l ∈ ls, l ∈ maskL NL LV) → ∀ {s : BS}, BSInv n (maskL NL LV) s →
      h < s.pts.length → s.pts.getD h 0 = p → enc w (BS.trans (letF n w LT) s h) n = tp →
      ls.foldl (fun S l => bfsLetter n w (mask w) (n * w) (mask (n * w)) LT p tp l S)
          (recBS n w (letF n w LT) s LV) =
        recBS n w (letF n w LT) (ls.foldl (BS.letter (letF n w LT) h p) s) LV
  | [], _, _, _, _, _, _ => rfl
  | l :: ls, hls, s, hs, hh, hp, htp => by
      simp only [List.foldl_cons]
      have hl := hls l List.mem_cons_self
      rw [bs_bfsLetter_eq hn16 hw hL hs hh hp htp hl]
      have hpn : p < n := by rw [← hp]; exact hs.lt _ (bs_getD_mem hh)
      refine bs_loop_eq hn16 hw hL ls (fun x hx => hls x (List.mem_cons_of_mem _ hx))
        (bs_letter_inv hs hl ((hL l hl).1 p hpn)) (Nat.lt_of_lt_of_le hh bs_letter_length_le) ?_ ?_
      · rw [bs_letter_getD hh, hp]
      · rw [bs_letter_trans hs hh, htp]

private theorem bs_foldl_mask {β : Type} (NL LV : Nat) (g : Nat → β → β) (b : β) :
    (List.range NL).foldl (fun S l => if hasBit LV l = true then g l S else S) b =
      (maskL NL LV).foldl (fun S l => g l S) b := by
  unfold maskL
  rw [List.foldl_filter]
  simp only [hasBit_eq]

private theorem bs_bfsStep_eq {n w LT NL LV : Nat} {s : BS} (hn16 : n < 2 ^ 16)
    (hw : n + 1 < 2 ^ w) (hL : ∀ l ∈ maskL NL LV, IsPermN n (letF n w LT l))
    (hs : BSInv n (maskL NL LV) s) (h : Nat) :
    bfsStep n w (mask w) (n * w) (mask (n * w)) LT NL LV h (recBS n w (letF n w LT) s LV) =
      recBS n w (letF n w LT) (BS.step (letF n w LT) (maskL NL LV) s h) LV := by
  have hOK := bs_recOK_recBS hn16 hw hL hs
  have hcnt : lcnt (recBS n w (letF n w LT) s LV) = s.pts.length := lcnt_recOf hOK
  unfold bfsStep BS.step
  simp only [strictN_eq, nIf_eq, hcnt, Nat.blt_eq]
  by_cases hh : h < s.pts.length
  · simp only [if_pos hh]
    have hhn : h < n := Nat.lt_of_lt_of_le hh hs.le
    have hpt : lpt w (mask w) (recBS n w (letF n w LT) s LV) h = s.pts.getD h 0 :=
      lpt_recOf hOK hhn
    have htr : ltr (n * w) (mask (n * w)) (recBS n w (letF n w LT) s LV) h =
        enc w (BS.trans (letF n w LT) s h) n := by
      have := ltr_recOf (LV := LV) hOK hhn
      rw [if_pos hh] at this
      exact this
    rw [hpt, htr, foldUp_eq, bs_foldl_mask]
    exact bs_loop_eq hn16 hw hL (maskL NL LV) (fun l hl => hl) hs hh rfl rfl
  · simp only [if_neg hh]

private theorem bs_outer_eq {n w LT NL LV : Nat} (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w)
    (hL : ∀ l ∈ maskL NL LV, IsPermN n (letF n w LT l)) :
    ∀ (hl : List Nat) {s : BS}, BSInv n (maskL NL LV) s →
      hl.foldl (fun S h => bfsStep n w (mask w) (n * w) (mask (n * w)) LT NL LV h S)
          (recBS n w (letF n w LT) s LV) =
        recBS n w (letF n w LT) (hl.foldl (BS.step (letF n w LT) (maskL NL LV)) s) LV
  | [], _, _ => rfl
  | h :: hl, s, hs => by
      simp only [List.foldl_cons]
      rw [bs_bfsStep_eq hn16 hw hL hs h]
      exact bs_outer_eq hn16 hw hL hl (bs_step_inv (fun l hl => (hL l hl).1) hs h)

private theorem bs_sinv_init {n r : Nat} {lv : List Nat} (hr : r < n) :
    BSInv n lv ⟨[r], [0], [0]⟩ := by
  refine ⟨rfl, rfl, by simp, by simp, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_singleton] at hp
    rw [hp]
    exact hr
  · intro k hk hk'
    simp at hk'
    omega

private theorem bs_trans_zero {F : Nat → Nat → Nat} {s : BS} : BS.trans F s 0 = fun x => x := by
  funext x
  rw [BS.trans.eq_1, dif_neg (by simp)]

private theorem bs_init_eq {n w LV r : Nat} {F : Nat → Nat → Nat} (hn16 : n < 2 ^ 16)
    (hw : n + 1 < 2 ^ w) (hr : r < n) :
    lInit n w (mask w) (n * w) (mask (n * w)) (pidn n w) r LV =
      recBS n w F ⟨[r], [0], [0]⟩ LV := by
  obtain ⟨hn24, -, hnw, -⟩ := bs_nfacts hn16 hw
  have hid : pidn n w = enc w (fun i => i) n := pidn_eq hn24 (Nat.le_of_lt hnw)
  have hidlt : pidn n w < 2 ^ (n * w) := by
    rw [hid]
    exact bs_enc_lt_perm hnw (isPermN_id n)
  have hfi : enc w (finv n fun x => x) n = pidn n w :=
    (enc_congr fun i hi => finv_apply (isPermN_id n) hi).trans hid.symm
  rw [lInit_eq hr hnw hidlt]
  unfold recBS
  refine bs_recOf_congr ?_ ?_ ?_ ?_
  · intro k _
    cases k with
    | zero => simp
    | succ k => simp [List.getD_eq_getElem?_getD]
  · intro x _
    by_cases hx : x = r
    · subst hx
      simp [posBS]
    · simp [posBS, hx]
  · intro k _
    by_cases hk : k = 0
    · subst hk
      simp only [bs_trans_zero]
      simp [hid]
    · simp [hk]
  · intro k _
    by_cases hk : k = 0
    · subst hk
      simp only [bs_trans_zero]
      simp [hfi]
    · simp [hk]

theorem bfs_eq {n w LT NL LV r : Nat} (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w) (hr : r < n)
    (hL : ∀ l ∈ maskL NL LV, IsPermN n (letF n w LT l)) :
    bfs n w (mask w) (n * w) (mask (n * w)) (pidn n w) LT NL LV r =
      recBS n w (letF n w LT) (BS.run (letF n w LT) (maskL NL LV) n r) LV := by
  unfold bfs
  rw [foldUp_eq, bs_init_eq hn16 hw hr (F := letF n w LT)]
  exact bs_outer_eq hn16 hw hL (List.range n) (bs_sinv_init hr)

end CFSG.KS.PK

end
