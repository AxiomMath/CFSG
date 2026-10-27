module

public import CFSG.Certificates.Kernel.Spor.PK.NatBFS
public import CFSG.Certificates.Kernel.Spor.PK.Congr
public import CFSG.Certificates.Kernel.Spor.TabWords

public section

namespace CFSG.KS.PK

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.KS.TW

@[expose] def natLevels (n : Nat) (F : Nat → Nat → Nat) (NL : Nat) (bs : List Nat) :
    List (List Nat × Nat × BS) :=
  (List.range bs.length).map fun i =>
    (lvAt F NL bs i, bs.getD i 0, BS.run F (lvAt F NL bs i) n (bs.getD i 0))

@[expose] def LettersOK (n : Nat) (letters : Array Table) : Prop :=
  letters.size % 2 = 0 ∧ letters.size < 2 ^ 32 ∧ ∀ l < letters.size, (letters[l]!).size = n ∧
    IsPermN n (tabF letters l) ∧ ∀ x < n, tabF letters (invL l) x = finv n (tabF letters l) x

variable {n : Nat} {letters : Array Table}

private theorem getD_mem_of_lt {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 ∈ l := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem ap_map_toArray {l : List Nat} (hl : ∀ x ∈ l, x < 2 ^ 32) (k : Nat) :
    ap (l.map UInt32.ofNat).toArray k = l.getD k 0 := by
  unfold ap
  by_cases hk : k < l.length
  · rw [getElem!_pos _ k (by simpa using hk)]
    simp only [List.getElem_toArray, List.getElem_map, UInt32.toNat_ofNat']
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    exact Nat.mod_eq_of_lt (hl _ (List.getElem_mem hk))
  · rw [getElem!_neg _ k (by simpa using hk)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

private theorem ap_treeOf_pos_mem {s : BS} (hle : s.pts.length ≤ n) (hn : n < 2 ^ 32)
    {p : Nat} (hp : p < n) (hm : p ∈ s.pts) :
    ap (treeOf n s).pos p = s.pts.idxOf p := by
  unfold ap treeOf
  rw [getElem!_pos _ p (by simpa using hp)]
  simp only [Array.getElem_ofFn, hm, if_true, UInt32.toNat_ofNat']
  have := List.idxOf_lt_length_iff.mpr hm
  exact Nat.mod_eq_of_lt (by omega)

private theorem ap_treeOf_pos_nmem {s : BS} {p : Nat} (hp : p < n) (hm : p ∉ s.pts) :
    ap (treeOf n s).pos p = 2 ^ 32 - 1 := by
  unfold ap treeOf
  rw [getElem!_pos _ p (by simpa using hp)]
  simp only [Array.getElem_ofFn, hm, if_false]
  rfl

private theorem ap_treeOf_pts_of {s : BS} (hn : n < 2 ^ 32) (hs : ∀ p ∈ s.pts, p < n) (k : Nat) :
    ap (treeOf n s).pts k = s.pts.getD k 0 :=
  ap_map_toArray (fun p hp => Nat.lt_trans (hs p hp) hn) k

private theorem ap_treeOf_pts {F : Nat → Nat → Nat} {lv : List Nat} {r : Nat} {s : BS}
    (hn : n < 2 ^ 32) (hs : RunOK n F lv r s) (k : Nat) :
    ap (treeOf n s).pts k = s.pts.getD k 0 :=
  ap_treeOf_pts_of hn hs.lt k

private theorem ap_treeOf_par {F : Nat → Nat → Nat} {lv : List Nat} {r : Nat} {s : BS}
    (hn : n < 2 ^ 32) (hs : RunOK n F lv r s) (k : Nat) :
    ap (treeOf n s).par k = s.par.getD k 0 := by
  refine ap_map_toArray (fun x hx => ?_) k
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  have hi' : i < s.pts.length := hs.len_par ▸ hi
  have hgd : s.par[i] = s.par.getD i 0 := List.getElem_eq_getD 0 (h := hi)
  rw [hgd]
  by_cases h0 : 0 < i
  · have := hs.par_lt i h0 hi'
    have := hs.le
    omega
  · have : i = 0 := by omega
    subst this
    rw [hs.par0]
    omega

private theorem ap_treeOf_lab {F : Nat → Nat → Nat} {lv : List Nat} {r : Nat} {s : BS}
    (hs : RunOK n F lv r s) (hlv : ∀ l ∈ lv, l < 2 ^ 32) (k : Nat) :
    ap (treeOf n s).lab k = s.lab.getD k 0 := by
  refine ap_map_toArray (fun x hx => ?_) k
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  have hi' : i < s.pts.length := hs.len_lab ▸ hi
  have hgd : s.lab[i] = s.lab.getD i 0 := List.getElem_eq_getD 0 (h := hi)
  rw [hgd]
  by_cases h0 : 0 < i
  · exact hlv _ (hs.lab_mem i h0 hi')
  · have : i = 0 := by omega
    subst this
    rw [hs.lab0]
    omega

private theorem idxOf_getD_of_nodup {l : List Nat} (hnd : l.Nodup) {k : Nat} (hk : k < l.length) :
    l.idxOf (l.getD k 0) = k := by
  have hmem : l.getD k 0 ∈ l := getD_mem_of_lt hk
  have hlt := List.idxOf_lt_length_of_mem hmem
  have h1 : l[l.idxOf (l.getD k 0)] = l.getD k 0 := List.getElem_idxOf hlt
  have h2 : l[k] = l.getD k 0 := List.getElem_eq_getD 0
  exact hnd.eq_of_getElem_eq hlt hk (h1.trans h2.symm)

private theorem getD_idxOf_of_mem {l : List Nat} {q : Nat} (hq : q ∈ l) :
    l.getD (l.idxOf q) 0 = q := by
  have hlt := List.idxOf_lt_length_of_mem hq
  rw [← List.getElem_eq_getD 0 (h := hlt)]
  exact List.getElem_idxOf hlt

private theorem treeOf_pts_size (s : BS) : (treeOf n s).pts.size = s.pts.length := by
  simp [treeOf]

private theorem getElem!_eq_toList_getD (base : Array Nat) (i : Nat) :
    base[i]! = base.toList.getD i 0 := by
  rw [← Array.getElem!_toList, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rfl

private theorem getElem!_map_range_of_lt {n : Nat} (g : Nat → Nat) {t : Nat} (ht : t < n) :
    ((Array.range n).map g)[t]! = g t := by
  rw [getElem!_pos _ t (by simpa using ht)]
  simp

private theorem getElem!_range_of_lt {n t : Nat} (ht : t < n) : (Array.range n)[t]! = t := by
  rw [getElem!_pos _ t (by simpa using ht)]
  simp

private theorem tupleEq_map_range {n : Nat} (g : Nat → Nat) :
    tupleEq ((Array.range n).map g) (Array.range n) = (List.range n).all fun x => g x == x := by
  apply Bool.eq_iff_iff.2
  rw [tupleEq_iff, List.all_eq_true]
  constructor
  · rintro ⟨-, h⟩ x hx
    have hx' := List.mem_range.1 hx
    have h1 := h x (by simpa using hx')
    rw [getElem!_map_range_of_lt g hx', getElem!_range_of_lt hx'] at h1
    simpa using h1
  · intro h
    refine ⟨by simp, fun t ht => ?_⟩
    have ht' : t < n := by simpa using ht
    rw [getElem!_map_range_of_lt g ht', getElem!_range_of_lt ht']
    simpa using h t (List.mem_range.2 ht')

private theorem allStep_zero_one_iff {m : Nat} {p : Nat → Bool} :
    allStep 0 1 m p = true ↔ ∀ k < m, p k = true := by
  unfold allStep
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h k hk
    have := h ⟨k, by omega⟩ (List.mem_finRange _)
    simpa using this
  · rintro h ⟨k, hk⟩ _
    simpa using h k (by omega)

private theorem parAll_zero_chunks_iff {m : Nat} {p : Nat → Bool} :
    parAll m 0 p = true ↔ ∀ k < m, p k = true := by
  rw [← allStep_zero_one_iff]
  unfold parAll
  simp only [Nat.zero_add, List.range_one, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, Bool.and_true]
  rfl

theorem treeOK_treeOf {root : Nat} {lv : List Nat} {s : BS} (hn : n < 2 ^ 32)
    (hs : RunOK n (tabF letters) lv root s) (hcl : ∀ p ∈ s.pts, ∀ l ∈ lv, tabF letters l p ∈ s.pts)
    (hlv : ∀ l ∈ lv, l < 2 ^ 32) :
    CFSG.Perm.Native.treeOK n root (treeOf n s) letters lv.toArray = true := by
  have hpts := ap_treeOf_pts hn hs
  have hpar := ap_treeOf_par hn hs
  have hlab := ap_treeOf_lab hs hlv
  unfold CFSG.Perm.Native.treeOK
  rw [Bool.and_eq_true, Bool.and_eq_true, allIn_iff, beq_iff_eq, treeOf_pts_size, decide_eq_true_eq]
  refine ⟨⟨hs.pos, by rw [hpts]; exact hs.root⟩, ?_⟩
  intro k hk
  have hkmem : s.pts.getD k 0 ∈ s.pts := getD_mem_of_lt hk
  have hkn : s.pts.getD k 0 < n := hs.lt _ hkmem
  have hidx : s.pts.idxOf (s.pts.getD k 0) = k := idxOf_getD_of_nodup hs.nodup hk
  unfold CFSG.Perm.Native.treeAt
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true, List.all_toArray,
    List.all_eq_true, Array.contains_iff, List.mem_toArray, treeOf_pts_size, hpts, hpar, hlab]
  refine ⟨⟨⟨hkn, ?_⟩, ?_⟩, ?_⟩
  · rw [ap_treeOf_pos_mem hs.le hn hkn hkmem, hidx]
  · intro l hl
    have hq : ap letters[l]! (s.pts.getD k 0) ∈ s.pts := hcl _ hkmem l hl
    have hqn := hs.lt _ hq
    rw [ap_treeOf_pos_mem hs.le hn hqn hq]
    exact ⟨List.idxOf_lt_length_of_mem hq, getD_idxOf_of_mem hq⟩
  · by_cases hk0 : k = 0
    · exact Or.inl hk0
    · have hk0' : 0 < k := Nat.pos_of_ne_zero hk0
      exact Or.inr ⟨⟨hs.par_lt k hk0' hk, hs.lab_mem k hk0' hk⟩, hs.edge k hk0' hk⟩

theorem walk_treeOf {lv : List Nat} {r : Nat} {s : BS} (hn : n < 2 ^ 32)
    (hs : RunOK n (tabF letters) lv r s) (hlv : ∀ l ∈ lv, l < 2 ^ 32) (k : Nat) (q : Array Nat) :
    CFSG.Perm.Native.walk (treeOf n s) letters k q = q.map (BS.trans (tabF letters) s k) := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    have hp := ap_treeOf_par hn hs k
    have hl := ap_treeOf_lab hs hlv k
    by_cases h : 0 < k ∧ s.par.getD k 0 < k
    · have h' : 0 < k ∧ ap (treeOf n s).par k < k := by rw [hp]; exact h
      have htr : BS.trans (tabF letters) s k = fun x => tabF letters (s.lab.getD k 0)
          (BS.trans (tabF letters) s (s.par.getD k 0) x) := by
        funext x
        rw [BS.trans.eq_def, dif_pos h]
      rw [CFSG.Perm.Native.walk.eq_def, dif_pos h', htr, hp, hl, apT_map, ih _ h.2, Array.map_map]
      rfl
    · have h' : ¬ (0 < k ∧ ap (treeOf n s).par k < k) := by rw [hp]; exact h
      have htr : BS.trans (tabF letters) s k = fun x => x := by
        funext x
        rw [BS.trans.eq_def, dif_neg h]
      rw [CFSG.Perm.Native.walk.eq_def, dif_neg h', htr, Array.map_id']

theorem walkInv_treeOf {lv : List Nat} {r : Nat} {s : BS} (hn : n < 2 ^ 32)
    (hs : RunOK n (tabF letters) lv r s) (hlv : ∀ l ∈ lv, l < 2 ^ 32 ∧ IsPermN n (tabF letters l) ∧
      ∀ x < n, tabF letters (invL l) x = finv n (tabF letters l) x)
    {k : Nat} (hk : k < s.pts.length) {q : Array Nat} (hq : ∀ x ∈ q.toList, x < n) :
    CFSG.Perm.Native.walkInv (treeOf n s) letters k q = q.map (finv n (BS.trans (tabF letters) s k)) := by
  induction k using Nat.strongRecOn generalizing q with
  | _ k ih =>
    have hp := ap_treeOf_par hn hs k
    have hl := ap_treeOf_lab hs (fun l hl => (hlv l hl).1) k
    by_cases h : 0 < k ∧ s.par.getD k 0 < k
    · have h' : 0 < k ∧ ap (treeOf n s).par k < k := by rw [hp]; exact h
      have hlab : s.lab.getD k 0 ∈ lv := hs.lab_mem k h.1 hk
      obtain ⟨_, hperm, hinv⟩ := hlv _ hlab
      have hpk : s.par.getD k 0 < s.pts.length := by omega
      have hq' : ∀ x ∈ (apT letters[invL (s.lab.getD k 0)]! q).toList, x < n := by
        rw [apT_map]
        intro x hx
        rw [Array.toList_map, List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        have hyn := hq y hy
        have h1 : ap letters[invL (s.lab.getD k 0)]! y = finv n (tabF letters (s.lab.getD k 0)) y :=
          hinv y hyn
        rw [h1]
        exact finv_lt (by omega) _ _
      rw [CFSG.Perm.Native.walkInv.eq_def, dif_pos h', hp, hl, ih _ h.2 hpk hq', apT_map,
        Array.map_map]
      apply Array.map_congr_left
      intro y hy
      have hyn := hq y (Array.mem_def.1 hy)
      have h1 : ap letters[invL (s.lab.getD k 0)]! y = finv n (tabF letters (s.lab.getD k 0)) y :=
        hinv y hyn
      have htr : BS.trans (tabF letters) s k = fun x => tabF letters (s.lab.getD k 0)
          (BS.trans (tabF letters) s (s.par.getD k 0) x) := by
        funext x
        rw [BS.trans.eq_def, dif_pos h]
      show finv n (BS.trans (tabF letters) s (s.par.getD k 0))
          (ap letters[invL (s.lab.getD k 0)]! y) = _
      rw [h1, htr, finv_comp hperm (trans_isPermN hs (fun l hl => (hlv l hl).2.1) hpk) hyn]
    · have h' : ¬ (0 < k ∧ ap (treeOf n s).par k < k) := by rw [hp]; exact h
      have htr : BS.trans (tabF letters) s k = fun x => x := by
        funext x
        rw [BS.trans.eq_def, dif_neg h]
      rw [CFSG.Perm.Native.walkInv.eq_def, dif_neg h', htr]
      calc q = q.map (fun x => x) := (Array.map_id' q).symm
        _ = q.map (finv n fun x => x) :=
          Array.map_congr_left fun y hy =>
            (finv_apply (isPermN_id n) (hq y (Array.mem_def.1 hy))).symm

@[expose] def NatLevelsOK (n : Nat) (letters : Array Table) (L : List (List Nat × Nat × BS)) : Prop :=
  ∀ e ∈ L, LevelOK n (tabF letters) e.1 e.2.1 e.2.2 ∧
    ∀ l ∈ e.1, l < 2 ^ 32 ∧ ∀ x < n, tabF letters (invL l) x = finv n (tabF letters l) x

theorem sift_treeOf {L : List (List Nat × Nat × BS)} (hn : n < 2 ^ 32) (hL : NatLevelsOK n letters L)
    {qb : Array Nat} (hqb : ∀ i (h : i < L.length), qb[i]! = L[i].2.1) {g : Nat → Nat}
    (hg : ∀ x < n, g x < n) (l : Nat) :
    CFSG.Perm.Native.sift (L.map fun e => treeOf n e.2.2).toArray letters qb (Array.range n) l
        ((Array.range n).map g) = absSift n (tabF letters) ((L.drop l).map fun e => e.2.2) g := by
  have key : ∀ d (l : Nat) (g : Nat → Nat), L.length - l = d → (∀ x < n, g x < n) →
      CFSG.Perm.Native.sift (L.map fun e => treeOf n e.2.2).toArray letters qb (Array.range n) l
        ((Array.range n).map g) = absSift n (tabF letters) ((L.drop l).map fun e => e.2.2) g := by
    intro d
    induction d with
    | zero =>
      intro l g hd hg
      have hl : ¬ l < L.length := by omega
      rw [CFSG.Perm.Native.sift.eq_def, dif_neg (by simpa using hl),
        List.drop_eq_nil_of_le (by omega), List.map_nil]
      exact tupleEq_map_range g
    | succ d ih =>
      intro l g hd hg
      have hl : l < L.length := by omega
      have hmem := List.getElem_mem hl
      have hLl := hL _ hmem
      have hT : (List.map (fun e => treeOf n e.snd.snd) L).toArray[l]'(by simpa using hl) =
          treeOf n L[l].2.2 := by simp
      have hqbl := hqb l hl
      rw [CFSG.Perm.Native.sift.eq_def, dif_pos (by simpa using hl),
        List.drop_eq_getElem_cons hl, List.map_cons]
      dsimp only
      rw [hT, hqbl]
      generalize L[l] = e at *
      obtain ⟨lv, b, s⟩ := e
      obtain ⟨⟨hrun, hperm⟩, hlv⟩ := hLl
      dsimp only at hrun hperm hlv ⊢
      have hbn : b < n := by
        have := getD_mem_of_lt hrun.pos
        rw [hrun.root] at this
        exact hrun.lt b this
      have himg : (Array.map g (Array.range n))[b]! = g b := getElem!_map_range_of_lt g hbn
      have hlv' : ∀ l ∈ lv, l < 2 ^ 32 ∧ IsPermN n (tabF letters l) ∧
          ∀ x < n, tabF letters (invL l) x = finv n (tabF letters l) x :=
        fun l hl' => ⟨(hlv l hl').1, hperm l hl', (hlv l hl').2⟩
      rw [absSift, hrun.root, himg]
      by_cases hm : g b ∈ s.pts
      · have hk := ap_treeOf_pos_mem hrun.le hn (hg b hbn) hm
        have hkl : s.pts.idxOf (g b) < s.pts.length := List.idxOf_lt_length_of_mem hm
        have hq : ∀ x ∈ (Array.map g (Array.range n)).toList, x < n := by
          intro x hx
          rw [Array.toList_map, List.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          exact hg y (List.mem_range.1 (by simpa using hy))
        rw [hk, walkInv_treeOf hn hrun hlv' hkl hq, Array.map_map, treeOf_pts_size,
          decide_eq_true hkl, decide_eq_true hm, Bool.true_and, Bool.true_and]
        exact ih (l + 1) (fun x => finv n (BS.trans (tabF letters) s (s.pts.idxOf (g b))) (g x))
          (by omega) (fun x hx => finv_lt (by omega) _ _)
      · have hk := ap_treeOf_pos_nmem (s := s) (hg b hbn) hm
        rw [hk, treeOf_pts_size]
        have : ¬ (2 ^ 32 - 1 < s.pts.length) := by
          have := hrun.le
          omega
        simp [this, hm]
  exact key _ l g rfl hg

theorem schreierAt_treeOf {L : List (List Nat × Nat × BS)} (hn : n < 2 ^ 32)
    (hL : NatLevelsOK n letters L) {qb : Array Nat} (hqb : ∀ i (h : i < L.length), qb[i]! = L[i].2.1)
    {i : Nat} (hi : i < L.length) {l : Nat} (hl : l ∈ L[i].1) {k : Nat}
    (hk : k < L[i].2.2.pts.length) :
    CFSG.Perm.Native.schreierAt (L.map fun e => treeOf n e.2.2).toArray letters qb (Array.range n) i l k =
      (decide (tabF letters l (L[i].2.2.pts.getD k 0) ∈ L[i].2.2.pts) &&
        absSift n (tabF letters) ((L.drop (i + 1)).map fun e => e.2.2) fun x =>
          finv n (BS.trans (tabF letters) L[i].2.2
            (L[i].2.2.pts.idxOf (tabF letters l (L[i].2.2.pts.getD k 0))))
            (tabF letters l (BS.trans (tabF letters) L[i].2.2 k x))) := by
  have hmem := List.getElem_mem hi
  have hLi := hL _ hmem
  have hT : (L.map fun e => treeOf n e.2.2).toArray[i]! = treeOf n L[i].2.2 := by
    rw [getElem!_pos _ i (by simpa using hi)]
    simp
  unfold CFSG.Perm.Native.schreierAt
  dsimp only
  rw [hT]
  generalize L[i] = e at *
  obtain ⟨lv, b, s⟩ := e
  obtain ⟨⟨hrun, hperm⟩, hlv⟩ := hLi
  dsimp only at *
  have hlv32 : ∀ l ∈ lv, l < 2 ^ 32 := fun l hl' => (hlv l hl').1
  have hlv' : ∀ l ∈ lv, l < 2 ^ 32 ∧ IsPermN n (tabF letters l) ∧
      ∀ x < n, tabF letters (invL l) x = finv n (tabF letters l) x :=
    fun l hl' => ⟨(hlv l hl').1, hperm l hl', (hlv l hl').2⟩
  have hkmem : s.pts.getD k 0 ∈ s.pts := getD_mem_of_lt hk
  have hpn : s.pts.getD k 0 < n := hrun.lt _ hkmem
  have hy : tabF letters l (s.pts.getD k 0) < n := (hperm l hl).1 _ hpn
  have hpk : ap (treeOf n s).pts k = s.pts.getD k 0 := ap_treeOf_pts hn hrun k
  have htab : ap letters[l]! (s.pts.getD k 0) = tabF letters l (s.pts.getD k 0) := rfl
  rw [hpk, htab]
  by_cases hm : tabF letters l (s.pts.getD k 0) ∈ s.pts
  · have hky := ap_treeOf_pos_mem hrun.le hn hy hm
    have hkl : s.pts.idxOf (tabF letters l (s.pts.getD k 0)) < s.pts.length :=
      List.idxOf_lt_length_of_mem hm
    have hq : ∀ x ∈ (apT letters[l]! (walk (treeOf n s) letters k (Array.range n))).toList,
        x < n := by
      rw [walk_treeOf hn hrun hlv32, apT_map]
      intro x hx
      rw [Array.toList_map, List.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      rw [Array.toList_map, List.mem_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      have hwn : w < n := List.mem_range.1 (by simpa using hw)
      exact (hperm l hl).1 _ ((trans_isPermN hrun hperm hk).1 w hwn)
    have hg' : ∀ x < n, finv n (BS.trans (tabF letters) s
        (s.pts.idxOf (tabF letters l (s.pts.getD k 0))))
        (tabF letters l (BS.trans (tabF letters) s k x)) < n := fun x hx =>
      finv_lt (by omega) _ _
    have hmap : Array.map (finv n (BS.trans (tabF letters) s
        (s.pts.idxOf (tabF letters l (s.pts.getD k 0)))))
        (apT letters[l]! (walk (treeOf n s) letters k (Array.range n))) =
        Array.map (fun x => finv n (BS.trans (tabF letters) s
          (s.pts.idxOf (tabF letters l (s.pts.getD k 0))))
          (tabF letters l (BS.trans (tabF letters) s k x))) (Array.range n) := by
      rw [walk_treeOf hn hrun hlv32, apT_map, Array.map_map, Array.map_map]
      rfl
    rw [hky, walkInv_treeOf hn hrun hlv' hkl hq, hmap, sift_treeOf hn hL hqb hg' (i + 1),
      treeOf_pts_size, decide_eq_true hkl, decide_eq_true hm, Bool.true_and]
  · have hky := ap_treeOf_pos_nmem (s := s) hy hm
    rw [hky, treeOf_pts_size]
    have : ¬ (2 ^ 32 - 1 < s.pts.length) := by
      have := hrun.le
      omega
    rw [decide_eq_false this, decide_eq_false hm, Bool.false_and, Bool.false_and]

theorem levelLetters_eq (letters : Array Table) (base : Array Nat) (i : Nat) :
    (CFSG.Perm.Native.levelLetters letters base i).toList = lvAt (tabF letters) letters.size base.toList i := by
  induction i with
  | zero =>
    show (Array.range letters.size).toList = List.range letters.size
    exact Array.toList_range
  | succ i ih =>
    have e : CFSG.Perm.Native.levelLetters letters base (i + 1) =
        (CFSG.Perm.Native.levelLetters letters base i).filter
          fun l => ap letters[l]! base[i]! == base[i]! := rfl
    rw [e, Array.toList_filter, ih, getElem!_eq_toList_getD]
    rfl

theorem chainTrees_eq {base : Array Nat} (hn : n < 2 ^ 32) (hbase : ∀ b ∈ base.toList, b < n)
    (hF : ∀ l < letters.size, ∀ x < n, tabF letters l x < n) :
    CFSG.Perm.Native.chainTrees n letters base =
      ((natLevels n (tabF letters) letters.size base.toList).map fun e => treeOf n e.2.2).toArray := by
  unfold CFSG.Perm.Native.chainTrees
  apply Array.ext
  · simp [natLevels]
  · intro i hi1 hi2
    rw [Array.getElem_ofFn]
    simp only [natLevels, List.getElem_toArray, List.getElem_map, List.getElem_range]
    have hi : i < base.size := by simpa using hi1
    have hbi : base[i]! = base.toList.getD i 0 := getElem!_eq_toList_getD base i
    have hlt : base.toList.getD i 0 < n := hbase _ (getD_mem_of_lt (by simpa using hi))
    have hlv := levelLetters_eq letters base i
    rw [treeBFS_eq hn (hbi ▸ hlt)
      (fun l hl x hx => hF l (lvAt_sub _ _ _ _ l (hlv ▸ hl)) x hx), hlv, hbi]

theorem natLevelsOK {base : Array Nat} (hn : n < 2 ^ 32) (hL : LettersOK n letters)
    (hbase : ∀ b ∈ base.toList, b < n) :
    NatLevelsOK n letters (natLevels n (tabF letters) letters.size base.toList) := by
  intro e he
  unfold natLevels at he
  rw [List.mem_map] at he
  obtain ⟨i, hi, rfl⟩ := he
  have hi' : i < base.toList.length := List.mem_range.1 hi
  have hbi : base.toList.getD i 0 < n := hbase _ (getD_mem_of_lt hi')
  obtain ⟨-, hsz32, hl⟩ := hL
  have hF : ∀ l ∈ lvAt (tabF letters) letters.size base.toList i, ∀ x < n,
      tabF letters l x < n := fun l hl' x hx =>
    (hl l (lvAt_sub _ _ _ _ l hl')).2.1.1 x hx
  refine ⟨⟨run_ok hF hbi, fun l hl' => (hl l (lvAt_sub _ _ _ _ l hl')).2.1⟩, fun l hl' => ⟨?_, ?_⟩⟩
  · have := lvAt_sub _ _ _ _ l hl'
    omega
  · intro x hx
    exact (hl l (lvAt_sub _ _ _ _ l hl')).2.2 x hx

theorem chainOK_of {base : Array Nat} (hn : n < 2 ^ 32) (hn0 : 0 < n) (hL : LettersOK n letters)
    (hbase : ∀ b ∈ base.toList, b < n)
    (hsch : ∀ i (h : i < (natLevels n (tabF letters) letters.size base.toList).length),
      absSch n (tabF letters) (natLevels n (tabF letters) letters.size base.toList)[i].1
        (natLevels n (tabF letters) letters.size base.toList)[i].2.2
        (((natLevels n (tabF letters) letters.size base.toList).drop (i + 1)).map fun e => e.2.2) = true)
    (hterm : ∀ l ∈ lvAt (tabF letters) letters.size base.toList base.size, ∀ x < n,
      tabF letters l x = x) :
    CFSG.Perm.Native.chainOK n letters base (Array.range n) base (CFSG.Perm.Native.chainTrees n letters base) 0 = true := by
  have hF : ∀ l < letters.size, ∀ x < n, tabF letters l x < n := fun l hl x hx =>
    (hL.2.2 l hl).2.1.1 x hx
  rw [chainTrees_eq hn hbase hF]
  unfold CFSG.Perm.Native.chainOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, allIn_iff, Array.all_eq_true',
    parAll_zero_chunks_iff]
  have hbase' : ∀ i < base.size, base[i]! < n := fun i hi => by
    rw [getElem!_eq_toList_getD]
    exact hbase _ (getD_mem_of_lt (by simpa using hi))
  have hLOK := natLevelsOK hn hL hbase
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, trivial⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact hL.1
  · intro j hj
    have h2 : 2 * j < letters.size := by omega
    have h21 : 2 * j + 1 < letters.size := by omega
    obtain ⟨-, hperm, hinv⟩ := hL.2.2 (2 * j) h2
    unfold invOK
    rw [allIn_iff]
    intro x hx
    have hinvL : invL (2 * j) = 2 * j + 1 := by unfold invL; simp
    have hy : tabF letters (2 * j) x < n := hperm.1 x hx
    have h1 := hinv _ hy
    rw [hinvL] at h1
    have h3 : ap letters[2 * j + 1]! (ap letters[2 * j]! x) = x := by
      have h4 : tabF letters (2 * j + 1) (tabF letters (2 * j) x) = x := by
        rw [h1]
        exact finv_apply hperm hx
      exact h4
    rw [h3]
    exact beq_self_eq_true x
  · simp [natLevels]
  · intro t ht
    rw [Array.size_range] at ht
    rw [getElem!_range_of_lt ht]
    exact ht
  · intro i hi
    have := hbase' i hi
    exact ⟨by rw [Array.size_range]; exact this, getElem!_range_of_lt this⟩
  · intro i hi
    have hi' : i < base.toList.length := by simpa using hi
    have hbi : base[i]! = base.toList.getD i 0 := getElem!_eq_toList_getD base i
    have hT : (List.map (fun e => treeOf n e.snd.snd)
        (natLevels n (tabF letters) letters.size base.toList)).toArray[i]! =
        treeOf n (BS.run (tabF letters) (lvAt (tabF letters) letters.size base.toList i) n
          (base.toList.getD i 0)) := by
      rw [getElem!_pos _ i (by simpa [natLevels] using hi')]
      simp [natLevels]
    have hlv := levelLetters_eq letters base i
    have hlvArr : levelLetters letters base i =
        (lvAt (tabF letters) letters.size base.toList i).toArray := by
      rw [← hlv, Array.toArray_toList]
    rw [hT, hbi, hlvArr]
    have hr : base.toList.getD i 0 < n := hbase _ (getD_mem_of_lt hi')
    have hF' : ∀ l ∈ lvAt (tabF letters) letters.size base.toList i, ∀ x < n,
        tabF letters l x < n := fun l hl x hx => hF l (lvAt_sub _ _ _ _ l hl) x hx
    exact treeOK_treeOf hn (run_ok hF' hr) (run_closed hF' hr) (fun l hl => by
      have := lvAt_sub _ _ _ _ l hl
      have := hL.2.1
      omega)
  · intro i hi l hl k hk
    have hi' : i < base.toList.length := by simpa using hi
    have hiLV : i < (natLevels n (tabF letters) letters.size base.toList).length := by
      simpa [natLevels] using hi'
    have hqb : ∀ i (h : i < (natLevels n (tabF letters) letters.size base.toList).length),
        base[i]! = (natLevels n (tabF letters) letters.size base.toList)[i].2.1 := by
      intro i h
      rw [getElem!_eq_toList_getD]
      simp [natLevels]
    have hT : (List.map (fun e => treeOf n e.snd.snd)
        (natLevels n (tabF letters) letters.size base.toList)).toArray[i]! =
        treeOf n (natLevels n (tabF letters) letters.size base.toList)[i].2.2 := by
      rw [getElem!_pos _ i (by simpa using hiLV)]
      simp
    rw [hT, treeOf_pts_size] at hk
    have hl' : l ∈ (natLevels n (tabF letters) letters.size base.toList)[i].1 := by
      have := levelLetters_eq letters base i
      have hl2 : l ∈ lvAt (tabF letters) letters.size base.toList i := by
        rw [← this]
        simpa using hl
      simpa [natLevels] using hl2
    rw [schreierAt_treeOf hn hLOK hqb hiLV hl' hk]
    have h1 := hsch i hiLV
    unfold absSch at h1
    rw [List.all_eq_true] at h1
    have h2 := h1 l hl'
    rw [List.all_eq_true] at h2
    exact h2 k (List.mem_range.2 hk)
  · intro l hl
    have hl' : l ∈ lvAt (tabF letters) letters.size base.toList base.size := by
      have := levelLetters_eq letters base base.size
      rw [← this]
      simpa using hl
    rw [apT_map, tupleEq_map_range, List.all_eq_true]
    intro x hx
    exact beq_iff_eq.2 (hterm l hl' x (List.mem_range.1 hx))

theorem orbitSizes_eq {base : Array Nat} (hn : n < 2 ^ 32) (hbase : ∀ b ∈ base.toList, b < n)
    (hF : ∀ l < letters.size, ∀ x < n, tabF letters l x < n) :
    CFSG.Perm.Native.orbitSizes (CFSG.Perm.Native.chainTrees n letters base) =
      (natLevels n (tabF letters) letters.size base.toList).map fun e => e.2.2.pts.length := by
  unfold CFSG.Perm.Native.orbitSizes
  rw [chainTrees_eq hn hbase hF]
  simp only [List.toList_toArray, List.map_map, Function.comp_def, treeOf_pts_size]

theorem inTreeB_treeOf {s : BS} (hn : n < 2 ^ 32) (hs : ∀ p ∈ s.pts, p < n) (hnd : s.pts.Nodup)
    {p : Nat} (hp : p < n) :
    CFSG.Sporadic.Mathieu.Native.inTreeB (treeOf n s) p = decide (p ∈ s.pts) := by
  have hle : s.pts.length ≤ n := by
    have := hnd.length_le_of_subset (l₂ := List.range n) fun p hp => List.mem_range.2 (hs p hp)
    simpa using this
  unfold CFSG.Sporadic.Mathieu.Native.inTreeB
  by_cases hm : p ∈ s.pts
  · rw [ap_treeOf_pos_mem hle hn hp hm, ap_treeOf_pts_of hn hs, getD_idxOf_of_mem hm,
      treeOf_pts_size]
    simp [List.idxOf_lt_length_of_mem hm, hm]
  · rw [ap_treeOf_pos_nmem hp hm, treeOf_pts_size]
    have : ¬ (2 ^ 32 - 1 < s.pts.length) := by omega
    simp [this, hm]

end CFSG.KS.PK

end
