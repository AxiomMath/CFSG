module

public import CFSG.Certificates.Kernel.Spor.PK.PermOf
public import CFSG.Certificates.Kernel.Spor.PK.NatChain
public import CFSG.Certificates.SchreierChainOrder

public section

namespace CFSG.KS.PK

open CFSG.Certificates CFSG.Perm.Native

@[expose] noncomputable def rawOf (n : Nat) (hn : 1 ≤ n) (F : Nat → Nat → Nat) (NL : Nat) {k : Nat}
    (bs : Vector (Fin n) k) (hbs : bs.toList.Nodup) : RawSchreierDatum n where
  degree_pos := hn
  originalCount := NL
  strongCount := NL
  baseCount := k
  originalCount_le := Nat.le_refl NL
  original := Vector.ofFn fun l => permOf n (F l.val)
  strong := Vector.ofFn fun l => permOf n (F l.val)
  base := bs
  base_distinct := hbs
  derivation := fun _ _ => []

@[expose] def PairsOK (n : Nat) (F : Nat → Nat → Nat) (NL : Nat) : Prop :=
  NL % 2 = 0 ∧ ∀ l < NL, IsPermN n (F l) ∧ ∀ x < n, F (invL l) x = finv n (F l) x

variable {n : Nat} {hn : 1 ≤ n} {F : Nat → Nat → Nat} {NL k : Nat} {bs : Vector (Fin n) k}
  {hbs : bs.toList.Nodup}

private theorem rs_lookup_eq {α : Type} (es : List (Fin n × α)) (x : Fin n) :
    es.lookup x = (es.map Prod.snd)[(es.map Prod.fst).idxOf x]? := by
  induction es with
  | nil => simp
  | cons e es ih =>
    obtain ⟨a, v⟩ := e
    rw [List.lookup_cons]
    by_cases hax : x = a
    · subst hax
      simp
    · have h1 : (x == a) = false := beq_eq_false_iff_ne.2 hax
      have h2 : (a == x) = false := beq_eq_false_iff_ne.2 (Ne.symm hax)
      rw [h1]
      simp only [List.map_cons, List.idxOf_cons, h2]
      simpa using ih

private theorem rs_idxOf_map_val (ks : List (Fin n)) (x : Fin n) :
    (ks.map Fin.val).idxOf x.val = ks.idxOf x := by
  induction ks with
  | nil => simp
  | cons a ks ih =>
    simp only [List.map_cons, List.idxOf_cons, ih]
    simp [Fin.val_inj]

private theorem rs_lvAt_eq_filter (F : Nat → Nat → Nat) (NL : Nat) (bs : List Nat) (i : Nat) :
    lvAt F NL bs i = (List.range NL).filter fun l =>
      decide (∀ j < i, F l (bs.getD j 0) = bs.getD j 0) := by
  induction i with
  | zero => simp [lvAt]
  | succ i ih =>
    rw [lvAt, ih, List.filter_filter]
    apply List.filter_congr
    intro l _
    apply Bool.eq_iff_iff.2
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact h2 j hj
      · exact h1
    · intro h
      exact ⟨h i (by omega), fun j hj => h j (by omega)⟩

private theorem rs_mem_lvAt {F : Nat → Nat → Nat} {NL : Nat} {bs : List Nat} {i l : Nat} :
    l ∈ lvAt F NL bs i ↔ l < NL ∧ ∀ j < i, F l (bs.getD j 0) = bs.getD j 0 := by
  rw [rs_lvAt_eq_filter, List.mem_filter, List.mem_range, decide_eq_true_eq]

private theorem rs_invL_lt {NL l : Nat} (hNL : NL % 2 = 0) (hl : l < NL) : invL l < NL := by
  unfold invL
  split <;> omega

private theorem rs_getD_lt {bs : List Nat} {n : Nat} (hn : 0 < n) (hbs : ∀ b ∈ bs, b < n)
    (i : Nat) : bs.getD i 0 < n := by
  by_cases hi : i < bs.length
  · exact hbs _ (by simp [List.getD_eq_getElem?_getD, hi])
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact hn

private theorem rs_lvAt_inv (hF : PairsOK n F NL) {bs : List Nat} (hn : 0 < n)
    (hbs : ∀ b ∈ bs, b < n) {i l : Nat} (hl : l ∈ lvAt F NL bs i) : invL l ∈ lvAt F NL bs i := by
  rw [rs_mem_lvAt] at hl ⊢
  obtain ⟨hlt, hfix⟩ := hl
  refine ⟨rs_invL_lt hF.1 hlt, fun j hj => ?_⟩
  have hx := rs_getD_lt hn hbs j
  have hfj := hfix j hj
  rw [(hF.2 l hlt).2 _ hx]
  conv_lhs => rw [← hfj]
  exact finv_apply (hF.2 l hlt).1 hx

theorem rawOf_levelGenerators (hF : PairsOK n F NL) (i : Nat) (hi : i ≤ k) :
    (rawOf n hn F NL bs hbs).levelGenerators i =
      (lvAt F NL (bs.toList.map Fin.val) i).map fun l => permOf n (F l) := by
  have hs : (rawOf n hn F NL bs hbs).strong.toList =
      (List.range NL).map fun l => permOf n (F l) := by
    have hr : List.range NL = (List.finRange NL).map Fin.val := by simp
    simp only [rawOf, Vector.toList_ofFn, List.ofFn_eq_map]
    rw [hr, List.map_map]
    rfl
  unfold RawSchreierDatum.levelGenerators
  rw [hs, List.filter_map, rs_lvAt_eq_filter]
  congr 1
  apply List.filter_congr
  intro l hl
  have hlt : l < NL := List.mem_range.1 hl
  have hp := (hF.2 l hlt).1
  apply Bool.eq_iff_iff.2
  simp only [Function.comp_apply, List.all_eq_true, decide_eq_true_eq]
  change (∀ b ∈ bs.toList.take i, permOf n (F l) b = b) ↔ _
  constructor
  · intro h j hj
    have hjk : j < k := by omega
    have h1 := h (bs.toList[j]'(by simpa using hjk)) (by
      rw [List.mem_take_iff_getElem]
      exact ⟨j, by simp; omega, rfl⟩)
    have h2 := congrArg Fin.val h1
    rw [permOf_apply hp] at h2
    simpa [List.getD_eq_getElem?_getD, hjk] using h2
  · intro h b hb
    rw [List.mem_take_iff_getElem] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    apply Fin.ext
    rw [permOf_apply hp]
    have hjk : j < k := by simp at hj; omega
    have := h j (by simp at hj; omega)
    simpa [List.getD_eq_getElem?_getD, hjk] using this

private structure RsInv (lv : List Nat) (s : BS) : Prop where
  len_par : s.par.length = s.pts.length
  len_lab : s.lab.length = s.pts.length
  pos : 0 < s.pts.length
  nodup : s.pts.Nodup
  par_lt : ∀ k, 0 < k → k < s.pts.length → s.par.getD k 0 < k
  lab_mem : ∀ k, 0 < k → k < s.pts.length → s.lab.getD k 0 ∈ lv

private theorem rs_getD_append_single (l : List Nat) (q k : Nat) :
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

private theorem rs_trans_congr {F : Nat → Nat → Nat} {s s' : BS} :
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

private abbrev rsSnoc (s : BS) (q h l : Nat) : BS := ⟨s.pts ++ [q], s.par ++ [h], s.lab ++ [l]⟩

private theorem rs_snoc_trans_old {F : Nat → Nat → Nat} {s : BS}
    (hpar : s.par.length = s.pts.length) (hlab : s.lab.length = s.pts.length) {q h l k : Nat}
    (hk : k < s.pts.length) :
    BS.trans F (rsSnoc s q h l) k = BS.trans F s k := by
  refine rs_trans_congr k fun j hj => ?_
  show (s.par ++ [h]).getD j 0 = s.par.getD j 0 ∧ (s.lab ++ [l]).getD j 0 = s.lab.getD j 0
  rw [rs_getD_append_single, rs_getD_append_single, if_neg (by omega), if_neg (by omega)]
  exact ⟨rfl, rfl⟩

private theorem rs_snoc_trans_new {F : Nat → Nat → Nat} {s : BS}
    (hpar : s.par.length = s.pts.length) (hlab : s.lab.length = s.pts.length)
    (hpos : 0 < s.pts.length) {q h l : Nat} (hh : h < s.pts.length) :
    BS.trans F (rsSnoc s q h l) s.pts.length = fun x => F l (BS.trans F s h x) := by
  funext x
  rw [BS.trans.eq_1]
  have h1 : (rsSnoc s q h l).par.getD s.pts.length 0 = h := by
    show (s.par ++ [h]).getD s.pts.length 0 = h
    rw [rs_getD_append_single, if_pos hpar.symm]
  have h2 : (rsSnoc s q h l).lab.getD s.pts.length 0 = l := by
    show (s.lab ++ [l]).getD s.pts.length 0 = l
    rw [rs_getD_append_single, if_pos hlab.symm]
  have hc : 0 < s.pts.length ∧ (rsSnoc s q h l).par.getD s.pts.length 0 < s.pts.length :=
    ⟨hpos, by rw [h1]; exact hh⟩
  rw [dif_pos hc, h1, h2, rs_snoc_trans_old hpar hlab hh]

private theorem rs_inv_init {lv : List Nat} (r : Nat) : RsInv lv ⟨[r], [0], [0]⟩ := by
  refine ⟨rfl, rfl, by simp, by simp, ?_, ?_⟩
  · intro k hk hk'
    simp at hk'
    omega
  · intro k hk hk'
    simp at hk'
    omega

private theorem rs_inv_snoc {lv : List Nat} {s : BS} (hs : RsInv lv s) {q h l : Nat}
    (hm : q ∉ s.pts) (hh : h < s.pts.length) (hl : l ∈ lv) : RsInv lv (rsSnoc s q h l) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [rsSnoc, hs.len_par]
  · simp [rsSnoc, hs.len_lab]
  · simp [rsSnoc]
  · refine List.nodup_append.2 ⟨hs.nodup, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact fun e => hm (e ▸ ha)
  · intro k hk hk'
    simp only [rsSnoc, List.length_append, List.length_singleton] at hk'
    have hlp := hs.len_par
    show (s.par ++ [h]).getD k 0 < k
    rw [rs_getD_append_single]
    by_cases hkc : k = s.par.length
    · rw [if_pos hkc]
      omega
    · rw [if_neg hkc]
      exact hs.par_lt k hk (by omega)
  · intro k hk hk'
    simp only [rsSnoc, List.length_append, List.length_singleton] at hk'
    have hlp := hs.len_lab
    show (s.lab ++ [l]).getD k 0 ∈ lv
    rw [rs_getD_append_single]
    by_cases hkc : k = s.lab.length
    · rw [if_pos hkc]
      exact hl
    · rw [if_neg hkc]
      exact hs.lab_mem k hk (by omega)

private theorem rs_letter_of_mem {F : Nat → Nat → Nat} {h p l : Nat} {s : BS} (hm : F l p ∈ s.pts) :
    BS.letter F h p s l = s := by
  unfold BS.letter
  rw [if_pos hm]

private theorem rs_letter_of_not_mem {F : Nat → Nat → Nat} {h p l : Nat} {s : BS}
    (hm : F l p ∉ s.pts) : BS.letter F h p s l = rsSnoc s (F l p) h l := by
  unfold BS.letter
  rw [if_neg hm]

private theorem rs_letter_inv {F : Nat → Nat → Nat} {lv : List Nat} {s : BS} (hs : RsInv lv s)
    {h p l : Nat} (hh : h < s.pts.length) (hl : l ∈ lv) : RsInv lv (BS.letter F h p s l) := by
  by_cases hm : F l p ∈ s.pts
  · rw [rs_letter_of_mem hm]
    exact hs
  · rw [rs_letter_of_not_mem hm]
    exact rs_inv_snoc hs hm hh hl

private theorem rs_letter_pts (F : Nat → Nat → Nat) (h p l : Nat) (s : BS) :
    ∃ u, (BS.letter F h p s l).pts = s.pts ++ u := by
  by_cases hm : F l p ∈ s.pts
  · exact ⟨[], by rw [rs_letter_of_mem hm, List.append_nil]⟩
  · exact ⟨[F l p], by rw [rs_letter_of_not_mem hm]⟩

private theorem rs_letter_mem (F : Nat → Nat → Nat) (h p l : Nat) (s : BS) :
    F l p ∈ (BS.letter F h p s l).pts := by
  by_cases hm : F l p ∈ s.pts
  · rw [rs_letter_of_mem hm]
    exact hm
  · rw [rs_letter_of_not_mem hm]
    simp [rsSnoc]

private theorem rs_letter_getD {F : Nat → Nat → Nat} {h p l : Nat} {s : BS} {k : Nat}
    (hk : k < s.pts.length) : (BS.letter F h p s l).pts.getD k 0 = s.pts.getD k 0 := by
  by_cases hm : F l p ∈ s.pts
  · rw [rs_letter_of_mem hm]
  · rw [rs_letter_of_not_mem hm]
    simp only [rsSnoc, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]

private theorem rs_letter_trans {F : Nat → Nat → Nat} {lv : List Nat} {s : BS} {h p l k : Nat}
    (hs : RsInv lv s) (hk : k < s.pts.length) :
    BS.trans F (BS.letter F h p s l) k = BS.trans F s k := by
  by_cases hm : F l p ∈ s.pts
  · rw [rs_letter_of_mem hm]
  · rw [rs_letter_of_not_mem hm]
    exact rs_snoc_trans_old hs.len_par hs.len_lab hk

private theorem rs_trans_perm {F : Nat → Nat → Nat} {lv : List Nat} {s : BS} (hs : RsInv lv s)
    (hF : ∀ l ∈ lv, IsPermN n (F l)) : ∀ k, k < s.pts.length → IsPermN n (BS.trans F s k) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk
    by_cases hc : 0 < k ∧ s.par.getD k 0 < k
    · have e : BS.trans F s k = fun x => F (s.lab.getD k 0) (BS.trans F s (s.par.getD k 0) x) := by
        funext x
        rw [BS.trans, dif_pos hc]
      rw [e]
      exact (hF _ (hs.lab_mem k hc.1 hk)).comp (ih _ hc.2 (by omega))
    · have e : BS.trans F s k = fun x => x := by
        funext x
        rw [BS.trans, dif_neg hc]
      rw [e]
      exact isPermN_id n

private theorem rs_trans_zero {F : Nat → Nat → Nat} {s : BS} : BS.trans F s 0 = fun x => x := by
  funext x
  rw [BS.trans, dif_neg (by simp)]

private structure RsRep (n : Nat) (F : Nat → Nat → Nat) (s : BS) (h : Nat)
    (q : SchreierOrbitState n) : Prop where
  keys : q.keys.map Fin.val = s.pts
  perms : q.entries.map Prod.snd = (List.range s.pts.length).map fun j => permOf n (BS.trans F s j)
  queue : q.queue.map Fin.val = s.pts.drop h

private theorem rs_rep_isSome {F : Nat → Nat → Nat} {s : BS} {h : Nat} {q : SchreierOrbitState n}
    (hr : RsRep n F s h q) (y : Fin n) : (q.transversal? y).isSome = true ↔ y.val ∈ s.pts := by
  have h1 : (q.transversal? y).isSome = true ↔ y ∈ q.keys :=
    SchreierOrbitState.mem_points_iff_mem_keys q y
  rw [h1, ← hr.keys]
  exact (List.mem_map_of_injective Fin.val_injective).symm

private theorem rs_rep_lookup {F : Nat → Nat → Nat} {s : BS} {h : Nat} {q : SchreierOrbitState n}
    (hr : RsRep n F s h q) (y : Fin n) :
    q.transversal? y =
      ((List.range s.pts.length).map fun j => permOf n (BS.trans F s j))[s.pts.idxOf y.val]? := by
  show q.entries.lookup y = _
  rw [rs_lookup_eq, hr.perms]
  have : (q.entries.map Prod.fst).idxOf y = s.pts.idxOf y.val := by
    rw [← hr.keys, rs_idxOf_map_val]
    rfl
  rw [this]

private theorem rs_rep_lookup_of_mem {F : Nat → Nat → Nat} {s : BS} {h : Nat}
    {q : SchreierOrbitState n} (hr : RsRep n F s h q) {y : Fin n} (hy : y.val ∈ s.pts) :
    q.transversal? y = some (permOf n (BS.trans F s (s.pts.idxOf y.val))) := by
  rw [rs_rep_lookup hr, List.getElem?_map, List.getElem?_range (List.idxOf_lt_length_of_mem hy)]
  rfl

private theorem rs_rep_lookup_of_not_mem {F : Nat → Nat → Nat} {s : BS} {h : Nat}
    {q : SchreierOrbitState n} (hr : RsRep n F s h q) {y : Fin n} (hy : y.val ∉ s.pts) :
    q.transversal? y = none := by
  rw [rs_rep_lookup hr, List.idxOf_eq_length hy]
  simp

private theorem rs_rep_init (F : Nat → Nat → Nat) (b : Fin n) :
    RsRep n F ⟨[b.val], [0], [0]⟩ 0 (SchreierOrbitState.initial b) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [SchreierOrbitState.keys, SchreierOrbitState.initial]
  · have : permOf n (BS.trans F (⟨[b.val], [0], [0]⟩ : BS) 0) = 1 := by
      rw [rs_trans_zero]
      exact (permOf_eq_one_iff (isPermN_id n)).2 (fun _ _ => rfl)
    simp [SchreierOrbitState.initial, this]
  · simp [SchreierOrbitState.initial]

private theorem rs_letter_rep {lv : List Nat} (hF : ∀ l ∈ lv, IsPermN n (F l)) {s : BS}
    {q : SchreierOrbitState n} (hs : RsInv lv s) {h : Nat} (hr : RsRep n F s (h + 1) q)
    (hh : h < s.pts.length) {l : Nat} (hl : l ∈ lv) {p : Nat} (x : Fin n) (hx : x.val = p)
    {T : Nat → Nat} (hT : BS.trans F s h = T) :
    RsRep n F (BS.letter F h p s l) (h + 1)
      (q.discover (permOf n (F l) x) (permOf n (F l) * permOf n T)) := by
  have hFl := hF l hl
  have hy : (permOf n (F l) x).val = F l p := by rw [permOf_apply hFl, hx]
  by_cases hm : F l p ∈ s.pts
  · rw [rs_letter_of_mem hm]
    have hsome : (q.transversal? (permOf n (F l) x)).isSome = true :=
      (rs_rep_isSome hr _).2 (by rw [hy]; exact hm)
    rw [SchreierOrbitState.discover_of_assigned _ _ _ hsome]
    exact hr
  · rw [rs_letter_of_not_mem hm]
    have hnone : q.transversal? (permOf n (F l) x) = none :=
      rs_rep_lookup_of_not_mem hr (by rw [hy]; exact hm)
    rw [SchreierOrbitState.discover_of_unassigned _ _ _ hnone]
    have hlen : (rsSnoc s (F l p) h l).pts.length = s.pts.length + 1 := by simp [rsSnoc]
    refine ⟨?_, ?_, ?_⟩
    · have hk := hr.keys
      unfold SchreierOrbitState.keys at hk ⊢
      simp only [rsSnoc, List.map_append, List.map_cons, List.map_nil, hk, hy]
    · have hp := hr.perms
      have htp : permOf n (F l) * permOf n T =
          permOf n (BS.trans F (rsSnoc s (F l p) h l) s.pts.length) := by
        rw [rs_snoc_trans_new hs.len_par hs.len_lab hs.pos hh, ← hT,
          permOf_mul hFl (rs_trans_perm hs hF h hh)]
      rw [hlen, List.range_succ, List.map_append, List.map_append, List.map_cons, List.map_nil,
        List.map_cons, List.map_nil, htp, hp]
      congr 1
      apply List.map_congr_left
      intro j hj
      rw [rs_snoc_trans_old hs.len_par hs.len_lab (List.mem_range.1 hj)]
    · have hq := hr.queue
      simp only [List.map_append, List.map_cons, List.map_nil, hq, hy, rsSnoc]
      rw [List.drop_append_of_le_length (by omega)]

private theorem rs_letters_rep {lv : List Nat} (hF : ∀ l ∈ lv, IsPermN n (F l)) {h p : Nat}
    (x : Fin n) (hx : x.val = p) {T : Nat → Nat} :
    ∀ (lv' : List Nat), (∀ l ∈ lv', l ∈ lv) → ∀ (s : BS) (q : SchreierOrbitState n),
      RsInv lv s → RsRep n F s (h + 1) q → h < s.pts.length → s.pts.getD h 0 = p →
      BS.trans F s h = T →
      RsInv lv (lv'.foldl (BS.letter F h p) s) ∧
      (∃ u, (lv'.foldl (BS.letter F h p) s).pts = s.pts ++ u) ∧
      (∀ l ∈ lv', F l p ∈ (lv'.foldl (BS.letter F h p) s).pts) ∧
      RsRep n F (lv'.foldl (BS.letter F h p) s) (h + 1)
        (lv'.foldl (fun st l => st.discover (permOf n (F l) x)
          (permOf n (F l) * permOf n T)) q) := by
  intro lv'
  induction lv' with
  | nil =>
    intro _ s q hs hr _ _ _
    exact ⟨hs, ⟨[], by simp⟩, by simp, hr⟩
  | cons l lv' ih =>
    intro hsub s q hs hr hh hp hT
    have hl : l ∈ lv := hsub l List.mem_cons_self
    have hsub' : ∀ l' ∈ lv', l' ∈ lv := fun l' hl' => hsub l' (List.mem_cons_of_mem _ hl')
    obtain ⟨u0, hu0⟩ := rs_letter_pts F h p l s
    have hh' : h < (BS.letter F h p s l).pts.length := by
      rw [hu0]
      simp only [List.length_append]
      omega
    have hp' : (BS.letter F h p s l).pts.getD h 0 = p := by
      rw [rs_letter_getD hh, hp]
    have hT' : BS.trans F (BS.letter F h p s l) h = T := by
      rw [rs_letter_trans hs hh, hT]
    obtain ⟨hI, ⟨u1, hu1⟩, hmem, hR⟩ := ih hsub' _ _ (rs_letter_inv hs hh hl)
      (rs_letter_rep hF hs hr hh hl x hx hT) hh' hp' hT'
    simp only [List.foldl_cons]
    refine ⟨hI, ⟨u0 ++ u1, by rw [hu1, hu0, List.append_assoc]⟩, ?_, hR⟩
    intro l' hl'
    rcases List.mem_cons.1 hl' with rfl | hl'
    · rw [hu1]
      exact List.mem_append.2 (Or.inl (rs_letter_mem F h p l' s))
    · exact hmem l' hl'

private theorem rs_discovers_noop (x : Fin n) (tx : Equiv.Perm (Fin n)) :
    ∀ (L : List (Equiv.Perm (Fin n))) (q : SchreierOrbitState n),
      (∀ σ ∈ L, (q.transversal? (σ x)).isSome = true) →
      L.foldl (fun st σ => st.discover (σ x) (σ * tx)) q = q := by
  intro L
  induction L with
  | nil => intro q _; rfl
  | cons σ L ih =>
    intro q hL
    rw [List.foldl_cons, SchreierOrbitState.discover_of_assigned _ _ _ (hL σ List.mem_cons_self)]
    exact ih q fun σ' hσ' => hL σ' (List.mem_cons_of_mem _ hσ')

private noncomputable abbrev rsSteps (n : Nat) (F : Nat → Nat → Nat) (lv : List Nat) :
    List (Equiv.Perm (Fin n)) :=
  lv.map (fun l => permOf n (F l)) ++ (lv.map fun l => permOf n (F l)).map fun σ => σ⁻¹

private theorem rs_step_rep {lv : List Nat} (hF : ∀ l ∈ lv, IsPermN n (F l))
    (hinv : ∀ l ∈ lv, invL l ∈ lv ∧ ∀ x < n, F (invL l) x = finv n (F l) x)
    {s : BS} {q : SchreierOrbitState n} (hs : RsInv lv s) {h : Nat} (hr : RsRep n F s h q) :
    RsInv lv (BS.step F lv s h) ∧
      RsRep n F (BS.step F lv s h) (h + 1) (SchreierOrbitState.step (rsSteps n F lv) q) := by
  by_cases hh : h < s.pts.length
  · have hq := hr.queue
    rw [List.drop_eq_getElem_cons hh] at hq
    cases hqq : q.queue with
    | nil =>
      rw [hqq] at hq
      simp at hq
      omega
    | cons x pending =>
      rw [hqq] at hq
      simp only [List.map_cons, List.cons.injEq] at hq
      obtain ⟨hx, hpend⟩ := hq
      have hxmem : x.val ∈ s.pts := hx ▸ List.getElem_mem hh
      have hidx : s.pts.idxOf x.val = h := hx ▸ List.Nodup.idxOf_getElem hs.nodup h hh
      have htx : q.transversal? x = some (permOf n (BS.trans F s h)) := by
        rw [rs_rep_lookup_of_mem hr hxmem, hidx]
      have hxp : x.val = s.pts.getD h 0 := by
        rw [hx]
        simp [List.getD_eq_getElem?_getD, hh]
      have hpop : RsRep n F s (h + 1) ⟨q.entries, pending⟩ := ⟨hr.keys, hr.perms, hpend⟩
      obtain ⟨hI, ⟨u, hu⟩, hmem, hR⟩ := rs_letters_rep hF x hxp lv (fun l hl => hl) s
        ⟨q.entries, pending⟩ hs hpop hh rfl rfl
      have hstep : BS.step F lv s h = lv.foldl (BS.letter F h (s.pts.getD h 0)) s := by
        unfold BS.step
        rw [if_pos hh]
      have hfold : (rsSteps n F lv).foldl
          (fun (st : SchreierOrbitState n) σ => st.discover (σ x) (σ * permOf n (BS.trans F s h)))
            (⟨q.entries, pending⟩ : SchreierOrbitState n) =
          lv.foldl (fun (st : SchreierOrbitState n) l => st.discover (permOf n (F l) x)
            (permOf n (F l) * permOf n (BS.trans F s h)))
            (⟨q.entries, pending⟩ : SchreierOrbitState n) := by
        rw [List.foldl_append]
        refine (rs_discovers_noop x _ _ _ ?_).trans List.foldl_map
        intro σ hσ
        simp only [List.mem_map] at hσ
        obtain ⟨σ', ⟨l, hl, rfl⟩, rfl⟩ := hσ
        rw [List.foldl_map, rs_rep_isSome hR, permOf_inv_apply (hF l hl) x,
          ← (hinv l hl).2 x.val x.isLt, hxp]
        exact hmem (invL l) (hinv l hl).1
      simp only [SchreierOrbitState.step, hqq, htx, Option.getD_some]
      rw [hstep, hfold]
      exact ⟨hI, hR⟩
  · have hq := hr.queue
    rw [List.drop_eq_nil_of_le (by omega)] at hq
    have hqe : q.queue = [] := List.map_eq_nil_iff.1 hq
    have hstep : BS.step F lv s h = s := by
      unfold BS.step
      rw [if_neg hh]
    rw [hstep, SchreierOrbitState.step_of_queue_empty _ q hqe]
    refine ⟨hs, hr.keys, hr.perms, ?_⟩
    rw [hqe, List.drop_eq_nil_of_le (by omega)]
    rfl

private theorem rs_run_succ (steps : List (Equiv.Perm (Fin n))) (j : Nat)
    (q : SchreierOrbitState n) :
    SchreierOrbitState.run steps (j + 1) q =
      SchreierOrbitState.step steps (SchreierOrbitState.run steps j q) := by
  rw [SchreierOrbitState.run_append_iterations steps j 1 q]
  rfl

private theorem rs_run_rep {lv : List Nat} (hF : ∀ l ∈ lv, IsPermN n (F l))
    (hinv : ∀ l ∈ lv, invL l ∈ lv ∧ ∀ x < n, F (invL l) x = finv n (F l) x) (b : Fin n)
    (j : Nat) :
    RsInv lv ((List.range j).foldl (BS.step F lv) ⟨[b.val], [0], [0]⟩) ∧
      RsRep n F ((List.range j).foldl (BS.step F lv) ⟨[b.val], [0], [0]⟩) j
        (SchreierOrbitState.run (rsSteps n F lv) j (SchreierOrbitState.initial b)) := by
  induction j with
  | zero => exact ⟨rs_inv_init _, rs_rep_init F b⟩
  | succ j ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, rs_run_succ]
    exact rs_step_rep hF hinv ih.1 ih.2

private theorem rs_letters (hF : PairsOK n F NL) {bs : List Nat} (hn : 0 < n)
    (hbs : ∀ b ∈ bs, b < n) (i : Nat) :
    (∀ l ∈ lvAt F NL bs i, IsPermN n (F l)) ∧
      ∀ l ∈ lvAt F NL bs i, invL l ∈ lvAt F NL bs i ∧
        ∀ x < n, F (invL l) x = finv n (F l) x := by
  refine ⟨fun l hl => (hF.2 l (lvAt_sub F NL bs i l hl)).1,
    fun l hl => ⟨rs_lvAt_inv hF hn hbs hl, ?_⟩⟩
  exact (hF.2 l (lvAt_sub F NL bs i l hl)).2

private theorem rs_base_lt (bs : Vector (Fin n) k) :
    ∀ b ∈ bs.toList.map Fin.val, b < n := by
  intro b hb
  obtain ⟨c, _, rfl⟩ := List.mem_map.1 hb
  exact c.isLt

private theorem rs_getD_base (bs : Vector (Fin n) k) (i : Fin k) :
    (bs.toList.map Fin.val).getD i.val 0 = (bs.get i).val := by
  simp [List.getD_eq_getElem?_getD, Vector.get]

private theorem rs_levelSteps (hF : PairsOK n F NL) (i : Nat) (hi : i ≤ k) :
    (rawOf n hn F NL bs hbs).levelSteps i =
      rsSteps n F (lvAt F NL (bs.toList.map Fin.val) i) := by
  unfold RawSchreierDatum.levelSteps
  rw [rawOf_levelGenerators hF i hi]

private theorem rs_orbit_rep (hF : PairsOK n F NL) (i : Fin k) :
    RsRep n F (BS.run F (lvAt F NL (bs.toList.map Fin.val) i.val) n (bs.get i).val) n
      ((rawOf n hn F NL bs hbs).orbitSearch i) := by
  have hl := rs_letters hF (bs := bs.toList.map Fin.val) hn (rs_base_lt bs) i.val
  have h1 := (rs_run_rep (F := F) hl.1 hl.2 (bs.get i) n).2
  unfold RawSchreierDatum.orbitSearch
  rw [rs_levelSteps hF i.val i.isLt.le]
  exact h1

theorem rawOf_keys (hF : PairsOK n F NL) (i : Fin k) :
    ((rawOf n hn F NL bs hbs).orbitSearch i).keys.map Fin.val =
      (BS.run F (lvAt F NL (bs.toList.map Fin.val) i.val) n (bs.get i).val).pts :=
  (rs_orbit_rep hF i).keys

theorem rawOf_transversal (hF : PairsOK n F NL) (i : Fin k) (x : Fin n) :
    (rawOf n hn F NL bs hbs).transversal? i x =
      let s := BS.run F (lvAt F NL (bs.toList.map Fin.val) i.val) n (bs.get i).val
      if x.val ∈ s.pts then some (permOf n (BS.trans F s (s.pts.idxOf x.val))) else none := by
  have hr := rs_orbit_rep (hn := hn) (bs := bs) (hbs := hbs) hF i
  show ((rawOf n hn F NL bs hbs).orbitSearch i).transversal? x = _
  by_cases hx : x.val ∈ (BS.run F (lvAt F NL (bs.toList.map Fin.val) i.val) n (bs.get i).val).pts
  · simp only [if_pos hx]
    exact rs_rep_lookup_of_mem hr hx
  · simp only [if_neg hx]
    exact rs_rep_lookup_of_not_mem hr hx

private theorem rs_runOK (hF : PairsOK n F NL) (i : Fin k) :
    RunOK n F (lvAt F NL (bs.toList.map Fin.val) i.val) (bs.get i).val
      (BS.run F (lvAt F NL (bs.toList.map Fin.val) i.val) n (bs.get i).val) :=
  run_ok (fun l hl => (rs_letters hF (bs := bs.toList.map Fin.val) (bs.get i).pos (rs_base_lt bs)
    i.val).1 l hl |>.1) (bs.get i).isLt

private theorem rs_sift_step {lv : List Nat} {r : Nat} {s : BS} {q : SchreierOrbitState n}
    (hr : RsRep n F s n q) (hok : RunOK n F lv r s) (hF : ∀ l ∈ lv, IsPermN n (F l))
    (b : Fin n) (hb : b.val = r) {rest : List (Fin n × SchreierOrbitState n)} {L : List BS}
    (ih : ∀ g : Nat → Nat, IsPermN n g →
      schreierSiftSucceeds rest (permOf n g) = absSift n F L g)
    {g : Nat → Nat} (hg : IsPermN n g) :
    schreierSiftSucceeds ((b, q) :: rest) (permOf n g) = absSift n F (s :: L) g := by
  have hroot : s.pts.getD 0 0 = b.val := by rw [hok.root, hb]
  have hgb : (permOf n g b).val = g b.val := permOf_apply hg b
  simp only [absSift, hroot]
  by_cases hmem : g b.val ∈ s.pts
  · have hsome := rs_rep_lookup_of_mem hr (y := permOf n g b) (by rw [hgb]; exact hmem)
    rw [hgb] at hsome
    have hTp : IsPermN n (BS.trans F s (s.pts.idxOf (g b.val))) :=
      trans_isPermN hok hF (List.idxOf_lt_length_of_mem hmem)
    unfold schreierSiftSucceeds
    rw [schreierSiftResidual_available _ _ _ _ _ hsome, decide_eq_true hmem, Bool.true_and,
      permOf_inv hTp, permOf_mul hTp.finv hg]
    exact ih _ (hTp.finv.comp hg)
  · have hnone := rs_rep_lookup_of_not_mem hr (y := permOf n g b) (by rw [hgb]; exact hmem)
    unfold schreierSiftSucceeds
    rw [schreierSiftResidual_unavailable _ _ _ _ hnone, decide_eq_false hmem, Bool.false_and]

private theorem rs_sift (hF : PairsOK n F NL) :
    ∀ (js : List (Fin k)) (g : Nat → Nat), IsPermN n g →
      schreierSiftSucceeds
          (js.map fun j => (bs.get j, (rawOf n hn F NL bs hbs).orbitSearch j)) (permOf n g) =
        absSift n F (js.map fun j =>
          BS.run F (lvAt F NL (bs.toList.map Fin.val) j.val) n (bs.get j).val) g := by
  intro js
  induction js with
  | nil =>
    intro g hg
    apply Bool.eq_iff_iff.2
    rw [List.map_nil, List.map_nil, schreierSiftSucceeds_nil, permOf_eq_one_iff hg]
    simp [absSift]
  | cons j js ih =>
    intro g hg
    have hr := rs_orbit_rep (hn := hn) (bs := bs) (hbs := hbs) hF j
    have hok := rs_runOK (bs := bs) hF j
    have hl := rs_letters hF (bs := bs.toList.map Fin.val) (bs.get j).pos (rs_base_lt bs) j.val
    simp only [List.map_cons]
    exact rs_sift_step hr hok hl.1 (bs.get j) rfl ih hg

private theorem rs_check_step {lv : List Nat} {r : Nat} {s : BS} {q : SchreierOrbitState n}
    {L : List BS} (hr : RsRep n F s n q) (hok : RunOK n F lv r s)
    (hF : ∀ l ∈ lv, IsPermN n (F l))
    (hinv : ∀ l ∈ lv, invL l ∈ lv ∧ ∀ x < n, F (invL l) x = finv n (F l) x)
    {rest : List (Fin n × SchreierOrbitState n)}
    (ih : ∀ g : Nat → Nat, IsPermN n g →
      schreierSiftSucceeds rest (permOf n g) = absSift n F L g)
    (hsch : absSch n F lv s L = true) :
    ∀ (x : Fin n) (tx : Equiv.Perm (Fin n)), q.transversal? x = some tx →
      ∀ σ ∈ rsSteps n F lv, ∃ ty : Equiv.Perm (Fin n),
        q.transversal? (σ x) = some ty ∧ schreierSiftSucceeds rest (ty⁻¹ * σ * tx) = true := by
  intro x tx htx σ hσ
  have hx : x.val ∈ s.pts := by
    by_contra hxn
    rw [rs_rep_lookup_of_not_mem hr hxn] at htx
    exact absurd htx (by simp)
  rw [rs_rep_lookup_of_mem hr hx] at htx
  have htx' : tx = permOf n (BS.trans F s (s.pts.idxOf x.val)) := (Option.some.inj htx).symm
  obtain ⟨l', hl', hσl⟩ : ∃ l' ∈ lv, σ = permOf n (F l') := by
    rcases List.mem_append.1 hσ with h1 | h1
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 h1
      exact ⟨l, hl, rfl⟩
    · obtain ⟨σ0, h2, rfl⟩ := List.mem_map.1 h1
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 h2
      refine ⟨invL l, (hinv l hl).1, ?_⟩
      rw [permOf_inv (hF l hl)]
      exact permOf_congr (fun y hy => ((hinv l hl).2 y hy).symm)
  subst hσl
  have hplt : s.pts.idxOf x.val < s.pts.length := List.idxOf_lt_length_of_mem hx
  have hpx : s.pts.getD (s.pts.idxOf x.val) 0 = x.val := by
    simp [List.getD_eq_getElem?_getD, hplt]
  have hsch' := List.all_eq_true.1 (List.all_eq_true.1 hsch l' hl') (s.pts.idxOf x.val)
    (List.mem_range.2 hplt)
  rw [Bool.and_eq_true, decide_eq_true_eq, hpx] at hsch'
  obtain ⟨hmem', hsift⟩ := hsch'
  have hσx : (permOf n (F l') x).val = F l' x.val := permOf_apply (hF l' hl') x
  have hty : q.transversal? (permOf n (F l') x) =
      some (permOf n (BS.trans F s (s.pts.idxOf (F l' x.val)))) := by
    have := rs_rep_lookup_of_mem hr (y := permOf n (F l') x) (by rw [hσx]; exact hmem')
    rwa [hσx] at this
  refine ⟨_, hty, ?_⟩
  have hTp : IsPermN n (BS.trans F s (s.pts.idxOf x.val)) := trans_isPermN hok hF hplt
  have hTq : IsPermN n (BS.trans F s (s.pts.idxOf (F l' x.val))) :=
    trans_isPermN hok hF (List.idxOf_lt_length_of_mem hmem')
  have hprod : (permOf n (BS.trans F s (s.pts.idxOf (F l' x.val))))⁻¹ * permOf n (F l') * tx =
      permOf n (fun y => finv n (BS.trans F s (s.pts.idxOf (F l' x.val)))
        (F l' (BS.trans F s (s.pts.idxOf x.val) y))) := by
    rw [htx', permOf_inv hTq, permOf_mul hTq.finv (hF l' hl'),
      permOf_mul (hTq.finv.comp (hF l' hl')) hTp]
  rw [hprod, ih _ ((hTq.finv.comp (hF l' hl')).comp hTp)]
  exact hsift

private theorem rs_levels_eq (bs : Vector (Fin n) k) (j : Nat) :
    ((natLevels n F NL (bs.toList.map Fin.val)).drop j).map (fun e => e.2.2) =
      ((List.finRange k).drop j).map fun j' =>
        BS.run F (lvAt F NL (bs.toList.map Fin.val) j'.val) n (bs.get j').val := by
  unfold natLevels
  rw [← List.map_drop, List.map_map]
  have h1 : (List.map Fin.val bs.toList).length = k := by simp
  have h2 : List.range k = (List.finRange k).map Fin.val := by simp
  rw [h1, h2, ← List.map_drop, List.map_map]
  apply List.map_congr_left
  intro j' _
  simp only [Function.comp_def]
  rw [rs_getD_base]

private theorem rs_tables_get (i : Fin k) :
    (rawOf n hn F NL bs hbs).orbitTables.get i = (rawOf n hn F NL bs hbs).orbitSearch i :=
  RawSchreierDatum.orbitTables_get (rawOf n hn F NL bs hbs) i

private theorem rs_siftLevels (j : Nat) :
    (rawOf n hn F NL bs hbs).siftLevels (rawOf n hn F NL bs hbs).orbitTables j =
      ((List.finRange k).drop j).map fun j' =>
        (bs.get j', (rawOf n hn F NL bs hbs).orbitSearch j') := by
  simp only [RawSchreierDatum.siftLevels, RawSchreierDatum.orbitTables_get]
  rfl

theorem rawOf_check (hF : PairsOK n F NL)
    (hsch : ∀ i (h : i < (natLevels n F NL (bs.toList.map Fin.val)).length),
      absSch n F (natLevels n F NL (bs.toList.map Fin.val))[i].1
        (natLevels n F NL (bs.toList.map Fin.val))[i].2.2
        (((natLevels n F NL (bs.toList.map Fin.val)).drop (i + 1)).map fun e => e.2.2) = true)
    (hterm : ∀ l ∈ lvAt F NL (bs.toList.map Fin.val) k, ∀ x < n, F l x = x) :
    (rawOf n hn F NL bs hbs).check = true := by
  rw [RawSchreierDatum.check_eq_true_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    simp [rawOf, Vector.get]
    rfl
  · intro j hj
    exact absurd j.isLt (Nat.not_lt.2 hj)
  · intro σ hσ
    have hσ' : σ ∈ (rawOf n hn F NL bs hbs).levelGenerators k := hσ
    rw [rawOf_levelGenerators hF k le_rfl] at hσ'
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hσ'
    exact (permOf_eq_one_iff (hF.2 l (lvAt_sub F NL _ k l hl)).1).2 (hterm l hl)
  · intro (i : Fin k) x tx htx σ hσ
    have hr := rs_orbit_rep (hn := hn) (bs := bs) (hbs := hbs) hF i
    have hok := rs_runOK (bs := bs) hF i
    have hl := rs_letters hF (bs := bs.toList.map Fin.val) (bs.get i).pos (rs_base_lt bs) i.val
    have hlen : i.val < (natLevels n F NL (bs.toList.map Fin.val)).length := by
      simp only [natLevels, List.length_map, List.length_range, Vector.length_toList]
      exact i.isLt
    have hget : (natLevels n F NL (bs.toList.map Fin.val))[i.val]'hlen =
        (lvAt F NL (bs.toList.map Fin.val) i.val, (bs.get i).val,
          BS.run F (lvAt F NL (bs.toList.map Fin.val) i.val) n (bs.get i).val) := by
      simp only [natLevels, List.getElem_map, List.getElem_range, rs_getD_base]
    have habs : absSch n F (lvAt F NL (bs.toList.map Fin.val) i.val)
        (BS.run F (lvAt F NL (bs.toList.map Fin.val) i.val) n (bs.get i).val)
        (((natLevels n F NL (bs.toList.map Fin.val)).drop (i.val + 1)).map fun e => e.2.2) =
          true := by
      have := hsch i.val hlen
      rw [hget] at this
      exact this
    rw [rs_levels_eq] at habs
    rw [rs_tables_get] at htx ⊢
    rw [rs_siftLevels]
    exact rs_check_step hr hok hl.1 hl.2 (rs_sift (hn := hn) (hbs := hbs) hF _) habs x tx htx σ
      (by rw [← rs_levelSteps (hn := hn) (hbs := hbs) hF i.val i.isLt.le]; exact hσ)

theorem rawOf_orbitSize (hF : PairsOK n F NL) (i : Fin k) :
    (rawOf n hn F NL bs hbs).orbitSize i =
      (BS.run F (lvAt F NL (bs.toList.map Fin.val) i.val) n (bs.get i).val).pts.length := by
  unfold RawSchreierDatum.orbitSize
  have := congrArg List.length (rawOf_keys (hn := hn) (hbs := hbs) hF i)
  simpa using this

end CFSG.KS.PK

end
