module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataLocalFamNative
public import Std.Data.HashSet.Lemmas

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataLocal

open CFSG.Sporadic.J4.QT

attribute [local irreducible] invs commMasks prodTab fixList fixLists tabL

theorem getD_of_lt {α : Type} {l : List α} {i : Nat} (h : i < l.length) (d : α) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem mem_invs {t : List Nat} : t ∈ invs ↔ t ∈ tabL ∧ compT t t = idT ∧ t ≠ idT := by
  simp only [invs, List.mem_filter, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]

theorem inv_mem {i : Nat} (hi : i < nInv) : inv i ∈ invs := by
  rw [inv, getD_of_lt hi]
  exact List.getElem_mem hi

theorem exists_inv {t : List Nat} (ht : t ∈ invs) : ∃ i < nInv, inv i = t := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ht
  exact ⟨i, hi, by rw [inv, getD_of_lt hi]⟩

theorem foldl_maskOf_testBit (l : List Nat) (a k : Nat) :
    (l.foldl (fun acc j => acc ||| (1 <<< j)) a).testBit k = (a.testBit k || decide (k ∈ l)) := by
  induction l generalizing a with
  | nil => simp
  | cons j l ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : j = k
    · subst h; simp
    · by_cases h' : k ∈ l <;> simp [h, h', Ne.symm h]

theorem testBit_maskOf (l : List Nat) (k : Nat) : (maskOf l).testBit k = decide (k ∈ l) := by
  rw [maskOf, foldl_maskOf_testBit]
  simp

theorem mem_bitIdx {m j : Nat} : j ∈ bitIdx m ↔ j < nInv ∧ m.testBit j = true := by
  simp [bitIdx, List.mem_filter, List.mem_range]

theorem lt_of_testBit_of_shiftRight {m j n : Nat} (hm : m >>> n = 0) (hj : m.testBit j = true) :
    j < n := by
  refine Nat.lt_of_not_ge fun hge => ?_
  have h := Nat.testBit_shiftRight (x := m) (i := n) (j := j - n)
  rw [hm, Nat.zero_testBit, show n + (j - n) = j by omega, hj] at h
  exact absurd h (by simp)

theorem lt_nInv_of_testBit {m j : Nat} (hm : m >>> nInv = 0) (hj : m.testBit j = true) :
    j < nInv := lt_of_testBit_of_shiftRight hm hj

theorem bitIdx_ne_nil {m : Nat} (hm : m >>> nInv = 0) (h0 : m ≠ 0) : bitIdx m ≠ [] := by
  intro h
  apply h0
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.zero_testBit]
  cases hj : m.testBit j with
  | false => rfl
  | true =>
    have : j ∈ bitIdx m := mem_bitIdx.2 ⟨lt_nInv_of_testBit hm hj, hj⟩
    rw [h] at this
    simp at this

theorem testBit_ext (m i k : Nat) :
    (ext m i).testBit k = true ↔
      m.testBit k = true ∨ k = i ∨ ∃ j ∈ bitIdx m, prodIdx i j = k := by
  rw [ext, extWith, Nat.testBit_or, testBit_maskOf]
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, List.mem_map]

theorem mem_cands {m i : Nat} : i ∈ cands m ↔
    i < nInv ∧ m.testBit i = false ∧
      ∀ j, m.testBit j = true → (commMasks.getD i 0).testBit j = true := by
  simp only [cands, List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
    beq_iff_eq]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h j hj
    have := congrArg (fun x => x.testBit j) h
    simp only [Nat.testBit_and, hj, Bool.true_and] at this
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and]
    cases hj : m.testBit j
    · simp
    · rw [h j hj]; rfl

theorem mem_dedup {l : List Nat} {x : Nat} (h : x ∈ l) : x ∈ dedup l := by
  have key : ∀ (l : List Nat) (s : Std.HashSet Nat), (x ∈ s ∨ x ∈ l) →
      x ∈ l.foldl (fun (s : Std.HashSet Nat) x => s.insert x) s := by
    intro l
    induction l with
    | nil => intro s hs; simpa using hs
    | cons y l ih =>
      intro s hs
      rw [List.foldl_cons]
      apply ih
      rcases hs with hs | hs
      · exact Or.inl (Std.HashSet.mem_insert.2 (Or.inr hs))
      · rcases List.mem_cons.1 hs with rfl | hs
        · exact Or.inl (Std.HashSet.mem_insert.2 (Or.inl (beq_self_eq_true _)))
        · exact Or.inr hs
  unfold dedup
  rw [Std.HashSet.mem_toList]
  exact key l {} (Or.inr h)

theorem ext_mem_exts {m i : Nat} (h : i ∈ cands m) : ext m i ∈ exts m := by
  unfold exts
  exact List.mem_map.2 ⟨i, h, rfl⟩

theorem ext_mem_next {F : List Nat} {m i : Nat} (hm : m ∈ F) (h : i ∈ cands m) :
    ext m i ∈ next F :=
  mem_dedup (List.mem_flatMap.2 ⟨m, hm, ext_mem_exts h⟩)

@[expose] def lvl (k : Nat) : List Nat := levels.getD k []

theorem levelsFrom_getD_succ : ∀ (n : Nat) (F : List Nat) (k : Nat), k + 1 < n →
    (levelsFrom n F).getD (k + 1) [] = next ((levelsFrom n F).getD k [])
  | 0, _, _, h => by omega
  | n + 1, F, 0, h => by
    cases n with
    | zero => omega
    | succ n => simp [levelsFrom]
  | n + 1, F, k + 1, h => by
    simpa [levelsFrom] using levelsFrom_getD_succ n (next F) k (by omega)

theorem lvl_succ {k : Nat} (hk : k < 7) : lvl (k + 1) = next (lvl k) :=
  levelsFrom_getD_succ 8 [0] k (by omega)

theorem lvl_zero : lvl 0 = [0] := rfl

theorem levelsFrom_length : ∀ (n : Nat) (F : List Nat), (levelsFrom n F).length = n
  | 0, _ => rfl
  | n + 1, F => by simp [levelsFrom, levelsFrom_length n]

theorem lvl_eq_nil {k : Nat} (hk : 8 ≤ k) : lvl k = [] := by
  rw [lvl, List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by rw [levels, levelsFrom_length]; exact hk)]
  rfl

theorem chkFam_spec (h : chkFam = true) :
    chkTabs = true ∧ lvl 7 = [] ∧ ∀ k, ∀ m ∈ lvl k, m >>> nInv = 0 ∧ boundOK m = true := by
  simp only [chkFam, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun k m hm => ?_⟩
  by_cases hk : k < levels.length
  · rw [lvl, getD_of_lt hk] at hm
    have := h3 _ (List.getElem_mem hk) m hm
    simpa using this
  · rw [lvl, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hm
    simp at hm

@[expose] def FamMem (m : Nat) : Prop := ∃ k, m ∈ lvl k

theorem famMem_zero : FamMem 0 := ⟨0, by rw [lvl_zero]; simp⟩

theorem famMem_shift (h : chkFam = true) {m : Nat} (hm : FamMem m) : m >>> nInv = 0 := by
  obtain ⟨k, hk⟩ := hm
  exact ((chkFam_spec h).2.2 k m hk).1

theorem famMem_boundOK (h : chkFam = true) {m : Nat} (hm : FamMem m) : boundOK m = true := by
  obtain ⟨k, hk⟩ := hm
  exact ((chkFam_spec h).2.2 k m hk).2

theorem famMem_ext (h : chkFam = true) {m i : Nat} (hm : FamMem m) (hi : i ∈ cands m) :
    FamMem (ext m i) := by
  obtain ⟨k, hk⟩ := hm
  have hk7 : k < 7 := by
    cases Nat.lt_or_ge k 7 with
    | inl hlt => exact hlt
    | inr hge =>
      exfalso
      rcases Nat.eq_or_lt_of_le hge with h7 | hlt
      · rw [← h7, (chkFam_spec h).2.1] at hk
        simp at hk
      · rw [lvl_eq_nil (by omega)] at hk
        simp at hk
  exact ⟨k + 1, by rw [lvl_succ hk7]; exact ext_mem_next hk hi⟩

theorem chkTabs_spec (h : chkTabs = true) {i j : Nat} (hi : i < nInv) (hj : j < nInv) :
    (commMasks.getD i 0).testBit j = commutes i j ∧
      (i = j ∨ commutes i j = false ∨
        (prodIdx i j < nInv ∧ inv (prodIdx i j) = compT (inv i) (inv j))) := by
  simp only [chkTabs, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h i hi j hj
  refine ⟨h1, ?_⟩
  rcases h2 with (h2 | h2) | ⟨h2, h3⟩
  · exact Or.inl h2
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr ⟨h2, h3⟩)

theorem commMasks_testBit (h : chkTabs = true) {i j : Nat} (hi : i < nInv) (hj : j < nInv) :
    (commMasks.getD i 0).testBit j = commutes i j := (chkTabs_spec h hi hj).1

theorem prod_spec (h : chkTabs = true) {i j : Nat} (hi : i < nInv) (hj : j < nInv) (hij : i ≠ j)
    (hc : commutes i j = true) :
    prodIdx i j < nInv ∧ inv (prodIdx i j) = compT (inv i) (inv j) := by
  rcases (chkTabs_spec h hi hj).2 with h1 | h1 | h1
  · exact absurd h1 hij
  · rw [hc] at h1; exact absurd h1 (by simp)
  · exact h1

end CFSG.EvenSporadicStandard.J4Std.DataLocal
