module

public import Certificates.Data.Kernel.Kc3DfsK
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.Kc3K

open CFSG.QuasithinUnique.A5.Kc3SporPerm

theorem dfsKR_spec {M : Nat} {pr ct : Nat → Nat → Nat} {nbr : Nat → List Nat} {NM : Nat → Nat}
    {lo len : Nat} (h : dfsKR M pr ct nbr NM lo len = true) :
    ∀ i, lo ≤ i → i < lo + len → dfsKI M pr ct nbr NM i = true := by
  intro i h1 h2
  unfold dfsKR at h
  rw [List.all_eq_true] at h
  have := h (i - lo) (List.mem_range.2 (by omega))
  rwa [Nat.add_sub_cancel' h1] at this

theorem histK_cons (y : Nat) (l : List Nat) : histK (y :: l) = histK l + 2 ^ (8 * y) := by
  change histK l + 1 <<< (8 * y) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

@[expose] def loK (v : Nat) (l : List Nat) : Nat :=
  ((List.range v).map fun x => l.count x * 2 ^ (8 * x)).sum

theorem loK_succ (v : Nat) (l : List Nat) : loK (v + 1) l = loK v l + l.count v * 2 ^ (8 * v) := by
  simp [loK, List.range_succ]

theorem histK_nil : histK [] = 0 := rfl

theorem loK_nil : ∀ v, loK v [] = 0
  | 0 => rfl
  | v + 1 => by rw [loK_succ, loK_nil v, List.count_nil, Nat.zero_mul]

theorem loK_cons (y : Nat) (l : List Nat) :
    ∀ v, loK v (y :: l) = loK v l + if y < v then 2 ^ (8 * y) else 0
  | 0 => by simp [loK]
  | v + 1 => by
    rw [loK_succ, loK_succ, loK_cons y l v, List.count_cons, add_mul]
    rcases lt_trichotomy y v with h | rfl | h
    · simp only [h, if_true, Nat.lt_succ_of_lt h, beq_iff_eq, h.ne, if_false]
      omega
    · simp only [lt_irrefl, if_false, beq_self_eq_true, if_true, Nat.lt_succ_self]
      omega
    · simp only [Nat.not_lt.2 h.le, if_false, beq_iff_eq, h.ne', Nat.not_lt.2 h]
      omega

theorem loK_lt {l : List Nat} (hc : ∀ x, l.count x < 256) : ∀ v, loK v l < 2 ^ (8 * v)
  | 0 => by simp [loK]
  | v + 1 => by
    rw [loK_succ, Nat.mul_succ, Nat.pow_add]
    have h1 := loK_lt hc v
    have h2 : l.count v * 2 ^ (8 * v) ≤ 255 * 2 ^ (8 * v) :=
      Nat.mul_le_mul_right _ (by have := hc v; omega)
    omega

theorem histK_split (v : Nat) : ∀ l : List Nat,
    ∃ U, histK l = loK v l + 2 ^ (8 * v) * (l.count v + 256 * U)
  | [] => ⟨0, by simp only [histK_nil, loK_nil, List.count_nil, Nat.mul_zero, Nat.add_zero]⟩
  | y :: l => by
    obtain ⟨U, hU⟩ := histK_split v l
    rw [histK_cons, hU, loK_cons, List.count_cons]
    rcases lt_trichotomy y v with h | rfl | h
    · refine ⟨U, ?_⟩
      simp only [h, if_true, beq_iff_eq, h.ne, if_false, Nat.add_zero]
      ring
    · refine ⟨U, ?_⟩
      simp only [lt_irrefl, if_false, beq_self_eq_true, if_true, Nat.add_zero]
      ring
    · refine ⟨U + 2 ^ (8 * (y - v - 1)), ?_⟩
      have e : 2 ^ (8 * y) = 2 ^ (8 * v) * (256 * 2 ^ (8 * (y - v - 1))) := by
        have h256 : (256 : Nat) = 2 ^ 8 := rfl
        rw [h256, ← Nat.pow_add, ← Nat.pow_add]
        congr 1
        omega
      simp only [Nat.not_lt.2 h.le, if_false, beq_iff_eq, h.ne', Nat.add_zero]
      rw [e]
      ring

theorem cntK_histK {vals : List Nat} (hlen : vals.length < 256) (v : Nat) :
    cntK (histK vals) v = vals.count v := by
  have hc : ∀ x, vals.count x < 256 := fun x => lt_of_le_of_lt (List.count_le_length) hlen
  obtain ⟨U, hU⟩ := histK_split v vals
  have hP : 0 < 2 ^ (8 * v) := Nat.two_pow_pos _
  change (histK vals >>> (8 * v)) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, hU,
    Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt (loK_lt hc v), Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hc v)]

theorem hist_foldl (l : List Nat) : ∀ (a : Array Nat), (∀ x ∈ l, x < a.size) →
    (l.foldl (fun (h : Array Nat) v => h.modify v (· + 1)) a).size = a.size ∧
    ∀ x < a.size, (l.foldl (fun (h : Array Nat) v => h.modify v (· + 1)) a)[x]! =
      a[x]! + l.count x := by
  induction l with
  | nil => intro a _; simp
  | cons v l ih =>
    intro a ha
    obtain ⟨hs, hg⟩ := ih (a.modify v (· + 1)) (fun x hx => by
      simpa using ha x (List.mem_cons_of_mem _ hx))
    refine ⟨by simpa using hs, fun x hx => ?_⟩
    rw [List.foldl_cons, hg x (by simpa using hx), getElem!_pos _ x (by simpa using hx),
      getElem!_pos a x hx, Array.getElem_modify, List.count_cons]
    by_cases hvx : v = x
    · subst hvx
      simp
      omega
    · simp [hvx]

theorem le_foldl_max : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], a => by simp
  | y :: l, a => by
    obtain ⟨h1, h2⟩ := le_foldl_max l (max a y)
    refine ⟨le_trans (le_max_left a y) h1, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_trans (le_max_right a x) h1
    · exact h2 x hx

theorem witness_bad {vals : List Nat} {v : Nat} (h : okSize (vals.count v) = false) :
    okSize (vals.count (witness vals)) = false := by
  have hv : v ∈ vals := by
    by_contra hn
    rw [List.count_eq_zero_of_not_mem hn] at h
    exact absurd h (by decide)
  have hmx := (le_foldl_max vals 0).2
  obtain ⟨-, hH⟩ := hist_foldl vals (Array.replicate (vals.foldl max 0 + 1) 0)
    (fun x hx => by simp only [Array.size_replicate]; have := hmx x hx; omega)
  have hH' : ∀ x ∈ vals, (vals.foldl (fun (h : Array Nat) v => h.modify v (· + 1))
      (Array.replicate (vals.foldl max 0 + 1) 0))[x]! = vals.count x := by
    intro x hx
    have hx' : x < (Array.replicate (vals.foldl max 0 + 1) 0).size := by
      simp only [Array.size_replicate]; have := hmx x hx; omega
    rw [hH x hx', getElem!_pos _ x hx']
    simp
  unfold witness
  dsimp only
  cases hf : vals.find? (fun w => !okSize (vals.foldl (fun (h : Array Nat) v => h.modify v (· + 1))
      (Array.replicate (vals.foldl max 0 + 1) 0))[w]!) with
  | none =>
    have := List.find?_eq_none.1 hf v hv
    rw [hH' v hv, h] at this
    exact absurd rfl this
  | some w =>
    have hw := List.find?_some hf
    have hwm := List.mem_of_find?_eq_some hf
    rw [hH' w hwm] at hw
    simpa using hw

set_option maxRecDepth 20000 in
theorem length_pairsL : pairsL.length = 210 := by decide

theorem leafBad_of_leafK {pr ct : Nat → Nat → Nat} {i j k l : Nat}
    (h : leafK pr ct i j k l = true) : leafBad pr ct i j k l = true := by
  have hvals : valsK ct ((List.range 16).map (elF pr i j k l)) =
      pairsL.map fun p => ct ((List.range 16).map (elF pr i j k l)).toArray[p.1]!
        ((List.range 16).map (elF pr i j k l)).toArray[p.2]! := by
    unfold valsK
    apply List.map_congr_left
    intro p _
    simp only [List.getD_eq_getElem?_getD, getElem!_def, List.getElem?_toArray]
    rfl
  unfold leafK at h
  rw [hvals, List.any_eq_true] at h
  obtain ⟨v, -, hv⟩ := h
  have hlen : (pairsL.map fun p => ct ((List.range 16).map (elF pr i j k l)).toArray[p.1]!
      ((List.range 16).map (elF pr i j k l)).toArray[p.2]!).length < 256 := by
    rw [List.length_map, length_pairsL]
    decide
  rw [cntK_histK hlen] at hv
  unfold leafBad
  dsimp only
  simpa using witness_bad (by simpa using hv)

theorem dfsB_of_dfsKI {M : Nat} {pr ct : Nat → Nat → Nat} {nbr : Nat → List Nat}
    {NM : Nat → Nat} (hnbr : ∀ i < M, ∀ j ∈ nbr i, j < M)
    (hNM : ∀ x < M, ∀ y < M, pr x y < M → (NM x).testBit y = true)
    (h : ∀ i < M, dfsKI M pr ct nbr NM i = true) : dfsB M pr ct nbr = true := by
  unfold dfsB
  rw [List.all_eq_true]
  intro i hi
  have hiM : i < M := List.mem_range.1 hi
  have hK := h i hiM
  unfold dfsKI at hK
  rw [List.all_eq_true] at hK ⊢
  intro j hj
  have hjM := hnbr i hiM j hj
  have hKj := hK j hj
  cases hg2 : g2 M pr i j
  · simp
  have hg2' := hg2
  simp only [g2, Bool.and_eq_true, decide_eq_true_eq] at hg2'
  have hijM : pr i j < M := hg2'.1.2
  simp only [hg2, Bool.not_true, Bool.false_or, List.all_eq_true] at hKj ⊢
  intro k hk
  have hkM := hnbr i hiM k hk
  have hKk := hKj k hk
  cases hg3 : g3 M pr i j k
  · simp
  have hg3' := hg3
  simp only [g3, Bool.and_eq_true, decide_eq_true_eq] at hg3'
  obtain ⟨⟨⟨⟨⟨⟨-, hik⟩, hjk⟩, hijk⟩, -⟩, -⟩, -⟩ := hg3'
  have hbk : (NM i &&& NM j &&& NM (pr i j)).testBit k = true := by
    simp only [Nat.testBit_and, Bool.and_eq_true]
    exact ⟨⟨hNM i hiM k hkM hik, hNM j hjM k hkM hjk⟩, hNM _ hijM k hkM hijk⟩
  simp only [hbk, hg3, Bool.not_true, Bool.false_or, List.all_eq_true] at hKk ⊢
  intro l hl
  have hKl := hKk l hl
  have hlM := hnbr i hiM l hl
  cases hg4 : g4 M pr i j k l
  · simp
  have hg4' := hg4
  simp only [g4, Bool.and_eq_true, decide_eq_true_eq] at hg4'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hil⟩, hjl⟩, hijl⟩, hkl⟩, hikl⟩, hjkl⟩, hijkl⟩, -⟩, -⟩, -⟩, -⟩, -⟩,
    -⟩, -⟩ := hg4'
  have hbl : (NM i &&& NM j &&& NM (pr i j) &&& NM k &&& NM (pr i k) &&& NM (pr j k) &&&
      NM (pr (pr i j) k)).testBit l = true := by
    simp only [Nat.testBit_and, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨hNM i hiM l hlM hil, hNM j hjM l hlM hjl⟩, hNM _ hijM l hlM hijl⟩,
      hNM k hkM l hlM hkl⟩, hNM _ hik l hlM hikl⟩, hNM _ hjk l hlM hjkl⟩, hNM _ hijk l hlM hijkl⟩
  have hleaf : leafK pr ct i j k l = true := by
    simpa only [hbl, hg4, Bool.not_true, Bool.false_or] using hKl
  simp only [hg4, Bool.not_true, Bool.false_or]
  exact leafBad_of_leafK hleaf

end CFSG.KC.Kc3K

end
