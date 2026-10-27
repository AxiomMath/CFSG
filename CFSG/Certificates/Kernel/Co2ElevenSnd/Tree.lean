module

public import Certificates.Data.Kernel.Co2Eleven
public import CFSG.Certificates.Kernel.Spor.PK.NatBFS
public import CFSG.Certificates.Kernel.Spor.TabWords

public section

namespace CFSG.KC.Co2Eleven.Snd

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.KS.PK CFSG.KS.TW CFSG.KC.Co2Eleven

private theorem ap_list (l : List Nat) (hl : ∀ x ∈ l, x < 2 ^ 32) (k : Nat) :
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

theorem treeOf_ap_pts {n : Nat} {s : BS} (hs : ∀ p ∈ s.pts, p < 2 ^ 32) (k : Nat) :
    ap (treeOf n s).pts k = s.pts.getD k 0 :=
  ap_list _ hs k

theorem treeOf_ap_par {n : Nat} {s : BS} (hs : ∀ p ∈ s.par, p < 2 ^ 32) (k : Nat) :
    ap (treeOf n s).par k = s.par.getD k 0 :=
  ap_list _ hs k

theorem treeOf_ap_lab {n : Nat} {s : BS} (hs : ∀ p ∈ s.lab, p < 2 ^ 32) (k : Nat) :
    ap (treeOf n s).lab k = s.lab.getD k 0 :=
  ap_list _ hs k

theorem treeOf_ap_pos_mem {n : Nat} {s : BS} (hle : s.pts.length < 2 ^ 32) {p : Nat} (hp : p < n)
    (hm : p ∈ s.pts) : ap (treeOf n s).pos p = s.pts.idxOf p := by
  unfold ap treeOf
  rw [getElem!_pos _ p (by simpa using hp)]
  simp only [Array.getElem_ofFn, hm, if_true, UInt32.toNat_ofNat']
  have := List.idxOf_lt_length_iff.mpr hm
  exact Nat.mod_eq_of_lt (by omega)

theorem treeOf_ap_pos_nmem {n : Nat} {s : BS} {p : Nat} (hp : p < n) (hm : p ∉ s.pts) :
    ap (treeOf n s).pos p = 2 ^ 32 - 1 := by
  unfold ap treeOf
  rw [getElem!_pos _ p (by simpa using hp)]
  simp only [Array.getElem_ofFn, hm, if_false]
  rfl

theorem treeOf_size {n : Nat} (s : BS) : (treeOf n s).pts.size = s.pts.length := by
  simp [treeOf]

private theorem getD_mem' {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 ∈ l := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem idxOf_getD' {l : List Nat} (hnd : l.Nodup) {k : Nat} (hk : k < l.length) :
    l.idxOf (l.getD k 0) = k := by
  have hmem : l.getD k 0 ∈ l := getD_mem' hk
  have hlt := List.idxOf_lt_length_of_mem hmem
  have h1 : l[l.idxOf (l.getD k 0)] = l.getD k 0 := List.getElem_idxOf hlt
  have h2 : l[k] = l.getD k 0 := List.getElem_eq_getD 0
  exact hnd.eq_of_getElem_eq hlt hk (h1.trans h2.symm)

private theorem getD_idxOf' {l : List Nat} {q : Nat} (hq : q ∈ l) :
    l.getD (l.idxOf q) 0 = q := by
  have hlt := List.idxOf_lt_length_of_mem hq
  rw [← List.getElem_eq_getD 0 (h := hlt)]
  exact List.getElem_idxOf hlt

theorem treeOK_of_run {n root : Nat} {letters : Array Table} {lv : List Nat} {s : BS}
    (hn : n < 2 ^ 32) (hs : RunOK n (tabF letters) lv root s)
    (hcl : ∀ p ∈ s.pts, ∀ l ∈ lv, tabF letters l p ∈ s.pts) (hlb : ∀ l ∈ s.lab, l < 2 ^ 32) :
    CFSG.Perm.Native.treeOK n root (treeOf n s) letters lv.toArray = true := by
  have hlen : s.pts.length < 2 ^ 32 := Nat.lt_of_le_of_lt hs.le hn
  have hpts : ∀ k, ap (treeOf n s).pts k = s.pts.getD k 0 :=
    treeOf_ap_pts fun p hp => Nat.lt_trans (hs.lt p hp) hn
  have hparb : ∀ x ∈ s.par, x < 2 ^ 32 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    have hi' : i < s.pts.length := hs.len_par ▸ hi
    have hgd : s.par[i] = s.par.getD i 0 := List.getElem_eq_getD 0 (h := hi)
    rw [hgd]
    by_cases h0 : 0 < i
    · have := hs.par_lt i h0 hi'
      omega
    · have : i = 0 := by omega
      subst this
      rw [hs.par0]
      omega
  have hpar : ∀ k, ap (treeOf n s).par k = s.par.getD k 0 := treeOf_ap_par hparb
  have hlab : ∀ k, ap (treeOf n s).lab k = s.lab.getD k 0 := treeOf_ap_lab hlb
  unfold CFSG.Perm.Native.treeOK
  rw [Bool.and_eq_true, Bool.and_eq_true, allIn_iff, beq_iff_eq, treeOf_size, decide_eq_true_eq]
  refine ⟨⟨hs.pos, by rw [hpts]; exact hs.root⟩, ?_⟩
  intro k hk
  have hkmem : s.pts.getD k 0 ∈ s.pts := getD_mem' hk
  have hkn : s.pts.getD k 0 < n := hs.lt _ hkmem
  have hidx : s.pts.idxOf (s.pts.getD k 0) = k := idxOf_getD' hs.nodup hk
  unfold CFSG.Perm.Native.treeAt
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true, List.all_toArray,
    List.all_eq_true, Array.contains_iff, List.mem_toArray, treeOf_size, hpts, hpar, hlab]
  refine ⟨⟨⟨hkn, ?_⟩, ?_⟩, ?_⟩
  · rw [treeOf_ap_pos_mem hlen hkn hkmem, hidx]
  · intro l hl
    have hq : ap letters[l]! (s.pts.getD k 0) ∈ s.pts := hcl _ hkmem l hl
    have hqn := hs.lt _ hq
    rw [treeOf_ap_pos_mem hlen hqn hq]
    exact ⟨List.idxOf_lt_length_of_mem hq, getD_idxOf' hq⟩
  · by_cases hk0 : k = 0
    · exact Or.inl hk0
    · have hk0' : 0 < k := Nat.pos_of_ne_zero hk0
      exact Or.inr ⟨⟨hs.par_lt k hk0' hk, hs.lab_mem k hk0' hk⟩, hs.edge k hk0' hk⟩

structure TreeRec (T : Tree) (letters : Array Table) (LC R : Nat → Nat) (i N : Nat) : Prop where
  size : T.pts.size = N
  le : N ≤ 2300
  pos_lt : ∀ x < 2300, ap T.pos x < N ↔ rf R i 3 x < N
  pos_eq : ∀ x < 2300, rf R i 3 x < N → ap T.pos x = rf R i 3 x
  par : ∀ k < N, ap T.par k = rf R i 1 k
  lab : ∀ k < N, ap T.lab k = rf R i 2 k
  letter : ∀ k < N, 0 < k → rf R i 1 k < k →
    TR 2300 letters[CFSG.Perm.Native.invL (rf R i 2 k)]!
      (ap12 (LC (CFSG.KC.Co2Eleven.invL (rf R i 2 k))))

theorem wiK_succ (LC R : Nat → Nat) (i f k : Nat) (img : List Nat) :
    wiK LC R i (f + 1) k img = if 0 < k ∧ rf R i 1 k < k then
      wiK LC R i f (rf R i 1 k) (img.map fun x => ap12 (LC (CFSG.KC.Co2Eleven.invL (rf R i 2 k))) x)
      else img := rfl

theorem walkInv_eq {T : Tree} {letters : Array Table} {LC R : Nat → Nat} {i N : Nat}
    (H : TreeRec T letters LC R i N) :
    ∀ f k, k < f → k < N → ∀ q : Array Nat, (∀ x ∈ q.toList, x < 2300) →
      (walkInv T letters k q).toList = wiK LC R i f k q.toList ∧
        ∀ x ∈ (walkInv T letters k q).toList, x < 2300
  | 0, _, hk, _, _, _ => absurd hk (Nat.not_lt_zero _)
  | f + 1, k, hk, hkN, q, hq => by
    rw [wiK_succ]
    by_cases hc : 0 < k ∧ rf R i 1 k < k
    · have hc' : 0 < k ∧ ap T.par k < k := by rw [H.par k hkN]; exact hc
      rw [walkInv.eq_def, dif_pos hc', if_pos hc, H.par k hkN, H.lab k hkN]
      have hT := H.letter k hkN hc.1 hc.2
      have hmap : (apT letters[CFSG.Perm.Native.invL (rf R i 2 k)]! q).toList =
          q.toList.map fun x => ap12 (LC (CFSG.KC.Co2Eleven.invL (rf R i 2 k))) x := by
        rw [apT_map, Array.toList_map]
        apply List.map_congr_left
        intro x hx
        exact (hT.2 x (hq x hx)).1
      have hq' : ∀ x ∈ (apT letters[CFSG.Perm.Native.invL (rf R i 2 k)]! q).toList, x < 2300 := by
        rw [hmap]
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact (hT.2 y (hq y hy)).2
      obtain ⟨ih1, ih2⟩ := walkInv_eq H f (rf R i 1 k) (by omega) (by omega) _ hq'
      exact ⟨by rw [ih1, hmap], ih2⟩
    · have hc' : ¬ (0 < k ∧ ap T.par k < k) := by rw [H.par k hkN]; exact hc
      rw [walkInv.eq_def, dif_neg hc', if_neg hc]
      exact ⟨rfl, hq⟩

end CFSG.KC.Co2Eleven.Snd

end
