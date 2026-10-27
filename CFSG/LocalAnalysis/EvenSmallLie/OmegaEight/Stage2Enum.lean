module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Pack
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

open Matrix

@[expose] def bsearchAux (A : Array ℕ) (k : ℕ) : ℕ → ℕ → ℕ → Option ℕ
  | 0, _, _ => none
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if A.getD mid 0 < k then bsearchAux A k fuel (mid + 1) hi
      else if A.getD mid 0 = k then some mid else bsearchAux A k fuel lo mid
    else none

@[expose] def memK (A : Array ℕ) (k : ℕ) : Bool :=
  match bsearchAux A k 64 0 A.size with
  | some i => decide (i < A.size) && A.getD i 0 == k
  | none => false

theorem exists_of_memK {A : Array ℕ} {k : ℕ} (h : memK A k = true) :
    ∃ i < A.size, A.getD i 0 = k := by
  unfold memK at h
  split at h
  · rename_i i _
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨i, h.1, h.2⟩
  · exact absurd h (by decide)

@[expose] def genK (gs : Array (ℕ × ℕ)) (j : ℕ) : ℕ × ℕ := gs.getD j (idK, idK)

@[expose] def genG (gs : Array (ℕ × ℕ)) (j : ℕ) : GL12 := glOf (genK gs j).1 (genK gs j).2

@[expose] def grpOf (gs : Array (ℕ × ℕ)) : Subgroup GL12 :=
  Subgroup.closure {x | ∃ j < gs.size, genG gs j = x}

@[expose] def gensOK (gs : Array (ℕ × ℕ)) : Bool := gs.all fun g => invPair g.1 g.2

theorem invPair_idK : invPair idK idK = true := by
  have h : mulK idK idK = idK :=
    eq_of_toMatK_eq (mulK_lt _ _) idK_lt (by rw [toMatK_mulK, toMatK_idK, one_mul])
  simp [invPair, h]

theorem invPair_genK {gs : Array (ℕ × ℕ)} (h : gensOK gs = true) (j : ℕ) :
    invPair (genK gs j).1 (genK gs j).2 = true := by
  rw [genK, Array.getD_eq_getD_getElem?]
  rcases hj : gs[j]? with _ | g
  · exact invPair_idK
  · simp only [gensOK, Array.all_eq_true] at h
    obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.1 hj
    exact h j hlt

theorem rep_genG {gs : Array (ℕ × ℕ)} (h : gensOK gs = true) (j : ℕ) :
    Rep (genK gs j).1 (genG gs j) := rep_glOf (invPair_genK h j)

theorem rep_genG_inv {gs : Array (ℕ × ℕ)} (h : gensOK gs = true) (j : ℕ) :
    Rep (genK gs j).2 (genG gs j)⁻¹ := rep_glOf_inv (invPair_genK h j)

theorem genG_mem {gs : Array (ℕ × ℕ)} (h : gensOK gs = true) (j : ℕ) : genG gs j ∈ grpOf gs := by
  by_cases hj : j < gs.size
  · exact Subgroup.subset_closure ⟨j, hj, rfl⟩
  · have e : genK gs j = (idK, idK) := by
      rw [genK, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl
    have h1 : genG gs j = 1 := (rep_genG h j).unique (by rw [e]; exact rep_one)
    rw [h1]
    exact one_mem _

structure Enum where
  keys : Array ℕ
  par : Array ℕ
  gen : Array ℕ
  dep : Array ℕ

@[expose] def sortedK (A : Array ℕ) : Bool :=
  (List.range (A.size - 1)).all fun i => decide (A.getD i 0 < A.getD (i + 1) 0)

@[expose] def tabs (gs : Array (ℕ × ℕ)) : Array (Array ℕ) := gs.map fun g => tab g.1

@[expose] def treeAt (gs : Array (ℕ × ℕ)) (T : Array (Array ℕ)) (E : Enum) (i : ℕ) : Bool :=
  (E.keys.getD i 0 == idK) ||
    (decide (E.par.getD i 0 < E.keys.size) && decide (E.gen.getD i 0 < gs.size) &&
      decide (E.dep.getD (E.par.getD i 0) 0 < E.dep.getD i 0) &&
      E.keys.getD i 0 == mulT (T.getD (E.gen.getD i 0) #[]) (E.keys.getD (E.par.getD i 0) 0))

@[expose] def closedAll (gs : Array (ℕ × ℕ)) (E : Enum) : Bool :=
  (List.range gs.size).all fun j =>
    let T := tab (genK gs j).1
    (List.range E.keys.size).all fun i => memK E.keys (mulT T (E.keys.getD i 0))

@[expose] def enumOK (gs : Array (ℕ × ℕ)) (E : Enum) : Bool :=
  let T := tabs gs
  gensOK gs && sortedK E.keys && memK E.keys idK &&
    ((List.range E.keys.size).all fun i =>
      decide (E.keys.getD i 0 < 2 ^ 144) && treeAt gs T E i) && closedAll gs E

theorem tabs_getD (gs : Array (ℕ × ℕ)) {j : ℕ} (hj : j < gs.size) :
    (tabs gs).getD j #[] = tab (genK gs j).1 := by
  rw [tabs, Array.getD_eq_getD_getElem?, Array.getElem?_map, genK, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem hj]
  simp only [Option.map_some, Option.getD_some]

theorem grpOf_induction {gs : Array (ℕ × ℕ)} (P : GL12 → Prop) (h1 : P 1)
    (hmul : ∀ x, ∀ j < gs.size, P x → P (x * genG gs j)) : ∀ x ∈ grpOf gs, P x := by
  intro x hx
  induction hx using Subgroup.closure_induction_right with
  | one => exact h1
  | mul_right x _ y hy ih =>
    obtain ⟨j, hj, rfl⟩ := hy
    exact hmul x j hj ih
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨j, hj, rfl⟩ := hy
    have hk : ∀ k, P (x * genG gs j ^ k) := by
      intro k
      induction k with
      | zero => simpa using ih
      | succ k ihk => rw [pow_succ, ← mul_assoc]; exact hmul _ j hj ihk
    have hn := orderOf_pos (genG gs j)
    have e : genG gs j ^ (orderOf (genG gs j) - 1) = (genG gs j)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, Nat.sub_add_cancel hn, pow_orderOf_eq_one]
    rw [← e]
    exact hk _

namespace Enum

variable {gs : Array (ℕ × ℕ)} {E : Enum}

theorem of_enumOK (h : enumOK gs E = true) :
    gensOK gs = true ∧ sortedK E.keys = true ∧ memK E.keys idK = true ∧
      (∀ i < E.keys.size, E.keys.getD i 0 < 2 ^ 144 ∧ treeAt gs (tabs gs) E i = true) ∧
        closedAll gs E = true := by
  simp only [enumOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, fun i hi => h.1.2 i hi, h.2⟩

theorem exists_mem (h : enumOK gs E = true) :
    ∀ i < E.keys.size, ∃ x ∈ grpOf gs, Rep (E.keys.getD i 0) x := by
  obtain ⟨hg, -, -, hall, -⟩ := of_enumOK h
  suffices H : ∀ d, ∀ i < E.keys.size, E.dep.getD i 0 = d →
      ∃ x ∈ grpOf gs, Rep (E.keys.getD i 0) x from fun i hi => H _ i hi rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i hi hd
    have ht := (hall i hi).2
    simp only [treeAt, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at ht
    rcases ht with h1 | ⟨⟨⟨hp, hj⟩, hdep⟩, hk⟩
    · exact ⟨1, one_mem _, by rw [h1]; exact rep_one⟩
    · obtain ⟨x, hx, hrx⟩ := ih _ (hd ▸ hdep) _ hp rfl
      refine ⟨x * genG gs (E.gen.getD i 0), mul_mem hx (genG_mem hg _), ?_⟩
      rw [hk, tabs_getD gs hj, mulT_tab]
      exact hrx.mul (rep_genG hg _)

theorem exists_key (h : enumOK gs E = true) {x : GL12} (hx : x ∈ grpOf gs) :
    ∃ i < E.keys.size, Rep (E.keys.getD i 0) x := by
  obtain ⟨hg, -, hid, -, hcl⟩ := of_enumOK h
  simp only [closedAll, List.all_eq_true, List.mem_range] at hcl
  refine grpOf_induction (fun x => ∃ i < E.keys.size, Rep (E.keys.getD i 0) x) ?_ ?_ x hx
  · obtain ⟨i, hi, hk⟩ := exists_of_memK hid
    exact ⟨i, hi, by rw [hk]; exact rep_one⟩
  · rintro y j hj ⟨i, hi, hr⟩
    obtain ⟨i', hi', hk⟩ := exists_of_memK (hcl j hj i hi)
    refine ⟨i', hi', ?_⟩
    rw [hk, mulT_tab]
    exact hr.mul (rep_genG hg j)

theorem lt_of_sortedK {A : Array ℕ} (hs : sortedK A = true) {i j : ℕ} (hij : i < j)
    (hj : j < A.size) : A.getD i 0 < A.getD j 0 := by
  simp only [sortedK, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hs
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h1 | rfl
    · exact (ih h1 (by omega)).trans (hs j (by omega))
    · exact hs i (by omega)

theorem key_lt (h : enumOK gs E = true) {i : ℕ} (hi : i < E.keys.size) :
    E.keys.getD i 0 < 2 ^ 144 := ((of_enumOK h).2.2.2.1 i hi).1

theorem index_unique (h : enumOK gs E = true) {i j : ℕ} (hi : i < E.keys.size)
    (hj : j < E.keys.size) (e : E.keys.getD i 0 = E.keys.getD j 0) : i = j := by
  have hs := (of_enumOK h).2.1
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd e (lt_of_sortedK hs hij hj).ne
  · rfl
  · exact absurd e (lt_of_sortedK hs hij hi).ne'

theorem card_eq (h : enumOK gs E = true) : Nat.card (grpOf gs) = E.keys.size := by
  choose f hf using fun i : Fin E.keys.size => exists_mem h i i.2
  choose g hg using fun x : grpOf gs => exists_key h x.2
  have hfi : Function.Injective fun i => (⟨f i, (hf i).1⟩ : grpOf gs) := by
    intro i j e
    have e' : f i = f j := congrArg Subtype.val e
    exact Fin.ext (index_unique h i.2 j.2 ((hf i).2.key_unique (e' ▸ (hf j).2)
      (key_lt h i.2) (key_lt h j.2)))
  have hgi : Function.Injective fun x : grpOf gs => (⟨g x, (hg x).1⟩ : Fin E.keys.size) := by
    intro x y e
    have e' : g x = g y := congrArg Fin.val e
    exact Subtype.ext ((hg x).2.unique (e' ▸ (hg y).2))
  apply le_antisymm
  · simpa using Nat.card_le_card_of_injective _ hgi
  · simpa using Nat.card_le_card_of_injective _ hfi

theorem mem_iff (h : enumOK gs E = true) {k : ℕ} (hk : k < 2 ^ 144) {x : GL12} (hx : Rep k x) :
    x ∈ grpOf gs ↔ ∃ i < E.keys.size, E.keys.getD i 0 = k := by
  constructor
  · intro hm
    obtain ⟨i, hi, hr⟩ := exists_key h hm
    exact ⟨i, hi, hr.key_unique hx (key_lt h hi) hk⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨y, hy, hry⟩ := exists_mem h i hi
    rwa [hry.unique hx] at hy

theorem not_mem (h : enumOK gs E = true) {k : ℕ} (hk : k < 2 ^ 144) {x : GL12} (hx : Rep k x)
    (hc : E.keys.contains k = false) : x ∉ grpOf gs := by
  rw [mem_iff h hk hx]
  rintro ⟨i, hi, rfl⟩
  have : E.keys.contains (E.keys.getD i 0) = true := by
    rw [Array.contains_iff_mem, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    exact Array.getElem_mem hi
  rw [hc] at this
  exact absurd this (by decide)

end Enum

@[expose] def mkEnum (gs : Array (ℕ × ℕ)) (fuel : ℕ := 1000) : Enum := Id.run do
  let mut seen : Std.HashMap ℕ (ℕ × ℕ × ℕ) := (∅ : Std.HashMap ℕ (ℕ × ℕ × ℕ)).insert idK (idK, 0, 0)
  let mut front : Array ℕ := #[idK]
  let T := tabs gs
  let mut d := 0
  for _ in [0:fuel] do
    if front.isEmpty then break
    d := d + 1
    let mut nf : Array ℕ := #[]
    for x in front do
      for j in [0:gs.size] do
        let z := mulT (T.getD j #[]) x
        if !seen.contains z then
          seen := seen.insert z (x, j, d)
          nf := nf.push z
    front := nf
  let keys := (seen.toArray.map (·.1)).qsort (· < ·)
  let idx : Std.HashMap ℕ ℕ := (keys.zipIdx).foldl (fun m p => m.insert p.1 p.2) ∅
  let info := fun k => seen.getD k (0, 0, 0)
  return ⟨keys, keys.map fun k => idx.getD (info k).1 0, keys.map fun k => (info k).2.1,
    keys.map fun k => (info k).2.2⟩

end CFSG.EvenSmallLie.OmegaEight.Stage2
