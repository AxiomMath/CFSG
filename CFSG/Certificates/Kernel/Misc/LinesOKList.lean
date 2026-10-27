module

public import CFSG.Certificates.Kernel.Misc.LinesList

public section

namespace CFSG.KC.Misc.Lines

open CFSG.Fischer.Native CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.KS.TW

variable {P : Array Flags} {pl : Array (Array Nat)} {LT : Array (Array Nat)}
  {rb : Nat → Nat → Bool} {PL : Nat → List Nat} {lf : Nat → Nat → List Nat}
  {L : Array (Array Nat)}

namespace LinesData

variable (G : PolarRel rb) (hD : LinesData rb L)
include G hD

theorem size_eq {i : Nat} (hi : i < L.size) : (L[i]!).size = 5 := by
  obtain ⟨x, hx, y, hy, hne, hr, h⟩ := hD.mem i hi
  rw [← Array.length_toList, h, Finset.length_sort, G.card5' hx hy hne hr]

omit G in
theorem mem_lt {i : Nat} (hi : i < L.size) {z : Nat} (hz : z ∈ (L[i]!).toList) : z < 693 := by
  obtain ⟨x, hx, y, hy, hne, hr, h⟩ := hD.mem i hi
  rw [h, Finset.mem_sort] at hz
  exact lt_of_mem_Ln hz

theorem get_lt {i : Nat} (hi : i < L.size) {a : Nat} (ha : a < 5) : (L[i]!)[a]! < 693 := by
  have hs := hD.size_eq G hi
  have : (L[i]!)[a]! ∈ (L[i]!).toList := by
    rw [getElem!_pos (L[i]!) a (by omega)]
    exact Array.getElem_mem_toList _
  exact hD.mem_lt hi this

theorem list_of_mem {i : Nat} (hi : i < L.size) {u v : Nat} (hne : u ≠ v)
    (hu : u ∈ (L[i]!).toList) (hv : v ∈ (L[i]!).toList) :
    (L[i]!).toList = (Ln rb u v).sort (· ≤ ·) := by
  obtain ⟨x, hx, y, hy, hxy, hr, h⟩ := hD.mem i hi
  rw [h, Finset.mem_sort] at hu hv
  rw [h, G.Ln_eq hx hy hxy hr hne hu hv]

theorem pos_of_mem {i : Nat} (hi : i < L.size) {u : Nat} (hu : u ∈ (L[i]!).toList) :
    ∃ a < 5, (L[i]!)[a]! = u := by
  have hs := hD.size_eq G hi
  obtain ⟨a, ha, e⟩ := List.getElem_of_mem hu
  have ha5 : a < 5 := by simpa [hs] using ha
  refine ⟨a, ha5, ?_⟩
  rw [getElem!_pos (L[i]!) a (by omega)]
  simpa using e

theorem get_mem {i : Nat} (hi : i < L.size) {a : Nat} (ha : a < 5) :
    (L[i]!)[a]! ∈ (L[i]!).toList := by
  have hs := hD.size_eq G hi
  rw [getElem!_pos (L[i]!) a (by omega)]
  exact Array.getElem_mem_toList _

theorem get_ne {i : Nat} (hi : i < L.size) {a b : Nat} (ha : a < 5) (hb : b < 5) (hab : a ≠ b) :
    (L[i]!)[a]! ≠ (L[i]!)[b]! := by
  have hs := hD.size_eq G hi
  obtain ⟨x, hx, y, hy, hxy, hr, h⟩ := hD.mem i hi
  have hnd : (L[i]!).toList.Nodup := by rw [h]; exact Finset.sort_nodup _ _
  rw [getElem!_pos (L[i]!) a (by omega), getElem!_pos (L[i]!) b (by omega)]
  intro e
  have e' : (L[i]!).toList[a]'(by simp [hs]; omega) = (L[i]!).toList[b]'(by simp [hs]; omega) := by
    simpa using e
  exact hab ((List.Nodup.getElem_inj_iff hnd).1 e')

theorem lineIdx_pair {u v i0 : Nat} (hu : u < 693) (hv : v < 693) (hne : u ≠ v)
    (hi0 : i0 < L.size) (hL : (L[i0]!).toList = (Ln rb u v).sort (· ≤ ·)) :
    (lineIdx L)[u * 693 + v]! = i0 := by
  have hk : u * 693 + v < 693 * 693 := by omega
  have hu' : u ∈ (L[i0]!).toList := by rw [hL, Finset.mem_sort]; exact G.left_mem_Ln hu
  have hv' : v ∈ (L[i0]!).toList := by rw [hL, Finset.mem_sort]; exact G.right_mem_Ln hv
  obtain ⟨a, ha, hau⟩ := hD.pos_of_mem G hi0 hu'
  obtain ⟨b, hb, hbv⟩ := hD.pos_of_mem G hi0 hv'
  refine lineIdx_get L hi0 hk ⟨a, ha, b, hb, ?_, by rw [hau, hbv]⟩ ?_
  · intro hab
    subst hab
    rw [hau] at hbv
    exact hne hbv
  · intro j hj hhit
    obtain ⟨a', ha', b', hb', hab', hkey⟩ := hhit
    have h1 := hD.get_lt G hj ha'
    have h2 := hD.get_lt G hj hb'
    have e1 : (L[j]!)[a']! = u := by omega
    have e2 : (L[j]!)[b']! = v := by omega
    have hu'' : u ∈ (L[j]!).toList := by rw [← e1]; exact hD.get_mem G hj ha'
    have hv'' : v ∈ (L[j]!).toList := by rw [← e2]; exact hD.get_mem G hj hb'
    have hLj := hD.list_of_mem G hj hne hu'' hv''
    exact hD.inj j hj i0 hi0 (hLj.trans hL.symm)

theorem get_lt_get {i : Nat} (hi : i < L.size) {a b : Nat} (ha : a < b) (hb : b < 5) :
    (L[i]!)[a]! < (L[i]!)[b]! := by
  have hs := hD.size_eq G hi
  obtain ⟨x, hx, y, hy, hxy, hr, h⟩ := hD.mem i hi
  have hsorted : (L[i]!).toList.Pairwise (· < ·) := by
    rw [h]
    exact (Finset.sortedLT_sort (Ln rb x y)).pairwise
  have hlen : (L[i]!).toList.length = 5 := by simpa using hs
  have := List.pairwise_iff_getElem.1 hsorted a b (by omega) (by omega) ha
  rw [getElem!_pos (L[i]!) a (by omega), getElem!_pos (L[i]!) b (by omega)]
  simpa using this

theorem idx_ok {i : Nat} (hi : i < L.size) {a b : Nat} (ha : a < 5) (hb : b < 5) (hab : a ≠ b) :
    (lineIdx L)[(L[i]!)[a]! * 693 + (L[i]!)[b]!]! = i :=
  hD.lineIdx_pair G (hD.get_lt G hi ha) (hD.get_lt G hi hb) (hD.get_ne G hi ha hb hab) hi
    (hD.list_of_mem G hi (hD.get_ne G hi ha hb hab) (hD.get_mem G hi ha) (hD.get_mem G hi hb))

end LinesData

theorem LinesData.count (G : PolarRel rb) (hD : LinesData rb L) :
    L.size = 6237 ∧ ∀ p < 693, ((Finset.range L.size).filter fun i : Nat =>
      p ∈ (L[i]!).toList.toFinset).card = 45 := by
  have hLS : ∀ i < L.size, ∃ x < 693, ∃ y < 693, x ≠ y ∧ rb x y = true ∧
      (L[i]!).toList.toFinset = Ln rb x y := by
    intro i hi
    obtain ⟨x, hx, y, hy, hxy, hr, h⟩ := hD.mem i hi
    exact ⟨x, hx, y, hy, hxy, hr, by rw [h, Finset.sort_toFinset]⟩
  have hb : ∀ i < L.size, ∀ j < L.size,
      (L[i]!).toList.toFinset = (L[j]!).toList.toFinset → i = j := by
    intro i hi j hj h
    obtain ⟨x, hx, y, hy, hxy, hr, h1⟩ := hD.mem i hi
    obtain ⟨x', hx', y', hy', hxy', hr', h2⟩ := hD.mem j hj
    apply hD.inj i hi j hj
    have e1 : (L[i]!).toList = ((L[i]!).toList.toFinset).sort (· ≤ ·) := by
      rw [h1, Finset.sort_toFinset]
    have e2 : (L[j]!).toList = ((L[j]!).toList.toFinset).sort (· ≤ ·) := by
      rw [h2, Finset.sort_toFinset]
    rw [e1, e2, h]
  have hc : ∀ x < 693, ∀ y < 693, x ≠ y → rb x y = true →
      ∃ i < L.size, (L[i]!).toList.toFinset = Ln rb x y := by
    intro x hx y hy hne hr
    obtain ⟨i, hi, h⟩ := hD.surj x hx y hy hne hr
    exact ⟨i, hi, by rw [h, Finset.sort_toFinset]⟩
  obtain ⟨h1, h2⟩ := G.lines_count L.size (fun i => (L[i]!).toList.toFinset) hLS hb hc
  exact ⟨h2, h1⟩

theorem lineListOK_of (T : Tabs P pl LT rb PL lf) (G : Geom rb PL lf) (hD : LinesData rb L) :
    lineListOK P LT L (lineIdx L) = true := by
  obtain ⟨hsize, hcount⟩ := hD.count G.rel
  unfold lineListOK
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simpa using hsize
  · rw [allIn_iff]
    intro p hp
    rw [beq_iff_eq]
    have h45 := hcount p hp
    rw [hsize] at h45
    have e : ((List.range 6237).filter fun i => L[i]!.contains p).toFinset =
        (Finset.range 6237).filter fun i : Nat => p ∈ (L[i]!).toList.toFinset := by
      ext i
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Finset.mem_filter,
        Finset.mem_range]
      simp
    rw [← List.toFinset_card_of_nodup ((List.nodup_range).filter _), e]
    exact h45
  · rw [allIn_iff]
    intro i hi
    have hi' : i < L.size := by omega
    dsimp only
    have hrel := G.rel
    obtain ⟨x, hx, y, hy, hxy, hr, hlist⟩ := hD.mem i hi'
    have hs5 := hD.size_eq hrel hi'
    have hu := hD.get_lt hrel hi' (a := 0) (by omega)
    have hv := hD.get_lt hrel hi' (a := 1) (by omega)
    have huv := hD.get_lt_get hrel hi' (a := 0) (b := 1) (by omega) (by omega)
    have hu_mem := hD.get_mem hrel hi' (a := 0) (by omega)
    have hv_mem := hD.get_mem hrel hi' (a := 1) (by omega)
    generalize hu_def : (L[i]!)[0]! = u at hu huv hu_mem
    generalize hv_def : (L[i]!)[1]! = v at hv huv hv_mem
    have hu_Ln : u ∈ Ln rb x y := by
      rw [hlist, Finset.mem_sort] at hu_mem
      exact hu_mem
    have hv_Ln : v ∈ Ln rb x y := by
      rw [hlist, Finset.mem_sort] at hv_mem
      exact hv_mem
    have hruv : rb u v = true := hrel.perp_of_mem hx hy hr hu_Ln hv_Ln
    have hLT := T.LT_get u hu v hv
    rw [if_pos hruv] at hLT
    have hlm := G.lmem u hu v hv (Nat.ne_of_lt huv) hruv
    have hLn : Ln rb u v = Ln rb x y := hrel.Ln_eq hx hy hxy hr (Nat.ne_of_lt huv) hu_Ln hv_Ln
    rw [hLT, T.P_get u hu v hv]
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    have hmemL : ∀ z, z ∈ L[i]! ↔ z ∈ Ln rb x y := by
      intro z
      rw [← Array.mem_toList_iff, hlist, Finset.mem_sort]
    refine ⟨⟨⟨⟨⟨hs5, ?_⟩, Nat.ne_of_lt huv⟩, hruv⟩, ?_, ?_⟩, ?_⟩
    · rw [Array.all_eq_true']
      intro z hz
      exact decide_eq_true (hD.mem_lt hi' (Array.mem_toList_iff.2 hz))
    · rw [Array.all_eq_true']
      intro z hz
      simp only [List.contains_toArray, List.elem_eq_mem, decide_eq_true_eq]
      rw [hlm z, hLn]
      exact (hmemL z).1 hz
    · simp only [List.all_toArray, List.all_eq_true, Array.contains_iff_mem]
      intro z hz
      rw [hlm z, hLn] at hz
      exact (hmemL z).2 hz
    · rw [allIn_iff]
      intro a ha
      rw [allIn_iff]
      intro b hb
      by_cases hab : a = b
      · simp [hab]
      · rw [Bool.or_eq_true]
        right
        exact beq_iff_eq.2 (hD.idx_ok hrel hi' ha hb hab)
  · have hrel := G.rel
    rw [allIn_iff]
    intro x hx
    dsimp only
    rw [allIn_iff]
    intro y hy
    by_cases hxy : x = y
    · simp [hxy]
    by_cases hr : rb x y = true
    · obtain ⟨i0, hi0, hlist⟩ := hD.surj x hx y hy hxy hr
      have hidx := hD.lineIdx_pair hrel hx hy hxy hi0 hlist
      have hLT := T.LT_get x hx y hy
      rw [if_pos hr] at hLT
      have hlm := G.lmem x hx y hy hxy hr
      rw [hidx, hLT]
      simp only [Bool.or_eq_true, Bool.not_eq_true']
      right
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      have hmemL : ∀ z, z ∈ L[i0]! ↔ z ∈ Ln rb x y := by
        intro z
        rw [← Array.mem_toList_iff, hlist, Finset.mem_sort]
      refine ⟨by omega, ?_, ?_⟩
      · simp only [List.all_toArray, List.all_eq_true, Array.contains_iff_mem]
        intro z hz
        exact (hmemL z).2 ((hlm z).1 hz)
      · rw [Array.all_eq_true']
        intro z hz
        simp only [List.contains_toArray, List.elem_eq_mem, decide_eq_true_eq]
        exact (hlm z).2 ((hmemL z).1 hz)
    · have hr' : rb x y = false := by simpa using hr
      rw [Bool.or_eq_true, Bool.or_eq_true]
      left
      right
      rw [T.P_get x hx y hy, hr']
      rfl

end CFSG.KC.Misc.Lines

end
