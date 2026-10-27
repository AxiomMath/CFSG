module

public import Certificates.Data.Kernel.M24G.Replay
public import Certificates.Data.CFSGNative.AS91.M24Geom
import Mathlib.Data.List.Perm.Subperm

public section

namespace CFSG.KC.M24G

open CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

theorem indexMap_loop {α : Type} [Inhabited α] (key : α → Nat) (l : Array α)
    (hd : ∀ i < l.size, ∀ j < l.size, key l[i]! = key l[j]! → i = j) :
    ∀ n, n ≤ l.size → ∀ k i,
      ((List.range n).foldl (fun m i => m.insert (key l[i]!) i) (∅ : Std.HashMap Nat Nat))[k]? =
          some i ↔ i < n ∧ key l[i]! = k
  | 0, _, k, i => by simp
  | n + 1, hn, k, i => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Std.HashMap.getElem?_insert]
    by_cases hk : key l[n]! = k
    · simp only [hk, beq_self_eq_true, if_true, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨Nat.lt_succ_self _, hk⟩
      · rintro ⟨hi, hik⟩
        exact (hd i (by omega) n (by omega) (hik.trans hk.symm)).symm
    · have hk' : (key l[n]! == k) = false := by simpa using hk
      rw [hk', if_neg Bool.false_ne_true, indexMap_loop key l hd n (by omega) k i]
      constructor
      · rintro ⟨hi, hik⟩
        exact ⟨by omega, hik⟩
      · rintro ⟨hi, hik⟩
        refine ⟨?_, hik⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact hi
        · exact absurd hik hk

theorem indexMap_eq_foldl {α : Type} [Inhabited α] (key : α → Nat) (l : Array α) :
    Native.indexMap key l =
      (List.range l.size).foldl (fun m i => m.insert (key l[i]!) i) (∅ : Std.HashMap Nat Nat) := by
  simp [Native.indexMap, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range_eq_range']

theorem indexMap_getElem?_eq_some {α : Type} [Inhabited α] (key : α → Nat) (l : Array α)
    (hd : ∀ i < l.size, ∀ j < l.size, key l[i]! = key l[j]! → i = j) (k i : Nat) :
    (Native.indexMap key l)[k]? = some i ↔ i < l.size ∧ key l[i]! = k := by
  rw [indexMap_eq_foldl]
  exact indexMap_loop key l hd l.size (Nat.le_refl _) k i

private theorem ksIdx_findK_mem (pos : KTree (Nat × Nat)) {k i : Nat}
    (h : findK k pos = some i) : (k, i) ∈ pos.toList := by
  induction pos with
  | leaf => simp [findK] at h
  | node l x r ihl ihr =>
    have hdef : findK k (.node l x r) =
        if k = x.1 then some x.2 else if k < x.1 then findK k l else findK k r := rfl
    rw [hdef] at h
    by_cases hk : k = x.1
    · rw [if_pos hk] at h
      simp only [Option.some.injEq] at h
      have hx : x = (k, i) := Prod.ext hk.symm h
      simp [KTree.toList, hx]
    · rw [if_neg hk] at h
      by_cases hlt : k < x.1
      · rw [if_pos hlt] at h
        have hl := ihl h
        simp only [KTree.toList, List.mem_append]
        exact Or.inl hl
      · rw [if_neg hlt] at h
        have hr := ihr h
        simp only [KTree.toList, List.mem_append]
        exact Or.inr (List.mem_cons_of_mem _ hr)

private theorem ksIdx_length_toList (pos : KTree (Nat × Nat)) :
    pos.toList.length = sizeK pos := by
  induction pos with
  | leaf => rfl
  | node l x r ihl ihr =>
    simp only [KTree.toList, List.length_append, List.length_cons, sizeK, ihl, ihr]
    omega

private theorem ksIdx_entry_nodup {α : Type} (key : α → Nat) (L : List α) :
    ((L.zipIdx).map (fun e : α × Nat => (key e.1, e.2))).Nodup := by
  rw [List.nodup_iff_eq_of_getElem_eq]
  intro i j hi hj h
  have h' := congrArg Prod.snd h
  simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add] at h'
  exact h'

private theorem ksIdx_posAll_findK {α : Type} (key : α → Nat) (pos : KTree (Nat × Nat)) :
    ∀ (L : List α) (i : Nat), posAll key pos L i = true →
      ∀ j (hj : j < L.length), findK (key L[j]) pos = some (i + j) := by
  intro L
  induction L with
  | nil => intro i _ j hj; simp at hj
  | cons x L ih =>
    intro i h j hj
    simp only [posAll, Bool.and_eq_true] at h
    obtain ⟨h0, h1⟩ := h
    cases j with
    | zero => simpa using h0
    | succ j =>
      have hj' : j < L.length := by simpa using hj
      have hrec := ih (i + 1) h1 j hj'
      have e : i + (j + 1) = i + 1 + j := by omega
      simpa only [List.getElem_cons_succ, e] using hrec

private theorem ksIdx_posOK {α : Type} {key : α → Nat} {L : List α}
    {pos : KTree (Nat × Nat)} (h : posOK key L pos = true) :
    sizeK pos = L.length ∧ posAll key pos L 0 = true := by
  simp only [posOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h

private theorem ksIdx_entries_perm {α : Type} (key : α → Nat) {L : List α}
    {pos : KTree (Nat × Nat)} (h : posOK key L pos = true) :
    List.Perm ((L.zipIdx).map (fun e : α × Nat => (key e.1, e.2))) pos.toList := by
  obtain ⟨hsize, hall⟩ := ksIdx_posOK h
  let M : List (Nat × Nat) := (L.zipIdx).map fun e : α × Nat => (key e.1, e.2)
  have hnd : M.Nodup := ksIdx_entry_nodup key L
  have hsub : M ⊆ pos.toList := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    obtain ⟨x, j⟩ := p
    obtain ⟨hj, hx⟩ := List.mem_zipIdx' hp
    have hf : findK (key L[j]) pos = some j := by
      simpa using ksIdx_posAll_findK key pos L 0 hall j hj
    have hm := ksIdx_findK_mem pos hf
    simpa [hx] using hm
  refine (hnd.subperm hsub).perm_of_length_le ?_
  rw [ksIdx_length_toList, hsize]
  simp [M]

theorem findK_eq_some {α : Type} (key : α → Nat) {L : List α} {pos : KTree (Nat × Nat)}
    (h : posOK key L pos = true) (k i : Nat) :
    findK k pos = some i ↔ ∃ hi : i < L.length, key L[i] = k := by
  constructor
  · intro hf
    have hperm := ksIdx_entries_perm key h
    have hmem : (k, i) ∈
        (L.zipIdx).map (fun e : α × Nat => (key e.1, e.2)) :=
      hperm.symm.subset (ksIdx_findK_mem pos hf)
    obtain ⟨p, hp, hpi⟩ := List.mem_map.1 hmem
    obtain ⟨x, j⟩ := p
    obtain ⟨hj, hx⟩ := List.mem_zipIdx' hp
    have hji : j = i := congrArg Prod.snd hpi
    have hkx : key x = k := congrArg Prod.fst hpi
    refine ⟨by simpa [hji] using hj, ?_⟩
    subst i
    rw [← hx]
    exact hkx
  · rintro ⟨hi, hik⟩
    have hfind := ksIdx_posAll_findK key pos L 0 (ksIdx_posOK h).2 i hi
    rw [← hik]
    simpa using hfind

theorem posOK_inj {α : Type} {key : α → Nat} {L : List α} {pos : KTree (Nat × Nat)}
    (h : posOK key L pos = true) {i j : Nat} (hi : i < L.length) (hj : j < L.length)
    (e : key L[i] = key L[j]) : i = j := by
  have h1 := (findK_eq_some key h (key L[j]) i).2 ⟨hi, e⟩
  have h2 := (findK_eq_some key h (key L[j]) j).2 ⟨hj, rfl⟩
  rw [h1] at h2
  exact Option.some.inj h2

theorem toArray_getElem! {α : Type} [Inhabited α] (L : List α) {i : Nat} (hi : i < L.length) :
    L.toArray[i]! = L[i] := by
  rw [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

theorem indexMap_getElem?_eq_findK {α : Type} [Inhabited α] {key : α → Nat} {L : List α}
    {pos : KTree (Nat × Nat)} (h : posOK key L pos = true) (k : Nat) :
    (Native.indexMap key L.toArray)[k]? = findK k pos := by
  have hd : ∀ i < L.toArray.size, ∀ j < L.toArray.size,
      key L.toArray[i]! = key L.toArray[j]! → i = j := by
    intro i hi j hj e
    rw [List.size_toArray] at hi hj
    rw [toArray_getElem! L hi, toArray_getElem! L hj] at e
    exact posOK_inj h hi hj e
  have hiff : ∀ i, (Native.indexMap key L.toArray)[k]? = some i ↔ findK k pos = some i := by
    intro i
    rw [indexMap_getElem?_eq_some key L.toArray hd, findK_eq_some key h, List.size_toArray]
    constructor
    · rintro ⟨hi, e⟩
      exact ⟨hi, by rwa [toArray_getElem! L hi] at e⟩
    · rintro ⟨hi, e⟩
      exact ⟨hi, by rwa [toArray_getElem! L hi]⟩
  cases hf : findK k pos with
  | some i => exact (hiff i).2 hf
  | none =>
    cases hm : (Native.indexMap key L.toArray)[k]? with
    | none => rfl
    | some i =>
      rw [(hiff i).1 hm] at hf
      exact absurd hf (by simp)

@[expose] def idxNat {α : Type} [Inhabited α] [BEq α] (key : α → Nat) (l : Array α) (n : Nat)
    (t : α) : Nat :=
  match (Native.indexMap key l)[key t]? with
  | some q => if q < n && l[q]! == t then q else n
  | none => n

theorem octIdx_eq_idxNat (m : Nat) : Native.octIdx m = idxNat id (Native.octList ()) Native.nOct m :=
  rfl

theorem trioIdx_eq_idxNat (t : Nat × Nat × Nat) :
    Native.trioIdx t = idxNat Native.key3 (Native.trioList ()) Native.nTrio t :=
  rfl

theorem sextIdx_eq_idxNat (s : List Nat) :
    Native.sextIdx s = idxNat Native.keyL (Native.sextList ()) Native.nSext s :=
  rfl

theorem idxNat_eq_idxK {α : Type} [Inhabited α] [BEq α] [LawfulBEq α] {key : α → Nat}
    {L : List α} {pos : KTree (Nat × Nat)} (h : posOK key L pos = true) {n : Nat}
    (hn : L.length = n) {t : α} (hinj : ∀ y ∈ L, key y = key t → y = t) :
    idxNat key L.toArray n t = idxK pos n (key t) := by
  unfold idxNat idxK
  rw [indexMap_getElem?_eq_findK h]
  cases hf : findK (key t) pos with
  | none => rfl
  | some q =>
    obtain ⟨hq, hk⟩ := (findK_eq_some key h _ _).1 hf
    have e : L[q] = t := hinj _ (List.getElem_mem hq) hk
    have hq' : q < n := hn ▸ hq
    simp [toArray_getElem! L hq, e, hq']

theorem idxK_getElem {α : Type} {key : α → Nat} {L : List α} {pos : KTree (Nat × Nat)}
    (h : posOK key L pos = true) (n : Nat) {i : Nat} (hi : i < L.length) :
    idxK pos n (key L[i]) = i := by
  unfold idxK
  rw [(findK_eq_some key h _ i).2 ⟨hi, rfl⟩]

theorem idxK_lt_iff {α : Type} {key : α → Nat} {L : List α} {pos : KTree (Nat × Nat)}
    (h : posOK key L pos = true) {n : Nat} (hn : L.length = n) (k : Nat) :
    idxK pos n k < n ↔ ∃ i, ∃ hi : i < L.length, key L[i] = k := by
  unfold idxK
  cases hf : findK k pos with
  | some q =>
    obtain ⟨hq, hk⟩ := (findK_eq_some key h _ _).1 hf
    exact ⟨fun _ => ⟨q, hq, hk⟩, fun _ => hn ▸ hq⟩
  | none =>
    refine ⟨fun h' => absurd h' (Nat.lt_irrefl n), ?_⟩
    rintro ⟨i, hi, hk⟩
    rw [(findK_eq_some key h k i).2 ⟨hi, hk⟩] at hf
    exact absurd hf (by simp)

end CFSG.KC.M24G
