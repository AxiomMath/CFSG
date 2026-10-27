module

public import CFSG.Certificates.Kernel.M24G.ReplayFacts
public import CFSG.Certificates.Kernel.M24G.ImgSound
public import CFSG.Certificates.Kernel.M24G.ListsSound
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.M24G

open CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

theorem img_lt {t : Array Nat} (ht : ∀ x ∈ t.toList, x < 24) (m : Nat) :
    Native.img t m < 2 ^ 24 := by
  rw [img_eq_imgF t ht]
  have e : (2 : Nat) ^ 24 = 16777216 := by decide
  have hm : ∀ x, x % 16777216 < 2 ^ 24 := fun x => by
    rw [e]
    exact Nat.mod_lt _ (by decide)
  unfold imgF field24
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (hm _) (hm _)) (hm _)

theorem foldl_ite_pull (c : Nat → Bool) (g : Nat → Nat) : ∀ (l : List Nat) (acc : Nat),
    l.foldl (fun acc i => if c i = true then acc ||| g i else acc) acc =
      acc ||| l.foldl (fun acc i => if c i = true then acc ||| g i else acc) 0
  | [], acc => by simp
  | a :: l, acc => by
    simp only [List.foldl_cons]
    by_cases h : c a = true
    · simp only [h, if_true, Nat.zero_or]
      rw [foldl_ite_pull c g l (acc ||| g a), foldl_ite_pull c g l (g a), Nat.or_assoc]
    · simp only [h, if_false]
      exact foldl_ite_pull c g l acc

theorem foldl_ite_split (c c₁ c₂ : Nat → Bool) (hc : ∀ i, c i = (c₁ i || c₂ i)) (g : Nat → Nat) :
    ∀ l : List Nat, l.foldl (fun acc i => if c i = true then acc ||| g i else acc) 0 =
      l.foldl (fun acc i => if c₁ i = true then acc ||| g i else acc) 0 |||
        l.foldl (fun acc i => if c₂ i = true then acc ||| g i else acc) 0
  | [] => by simp
  | a :: l => by
    simp only [List.foldl_cons]
    rw [foldl_ite_pull c, foldl_ite_pull c₁, foldl_ite_pull c₂, foldl_ite_split c c₁ c₂ hc g l, hc a]
    apply Nat.eq_of_testBit_eq
    intro k
    cases h₁ : c₁ a <;> cases h₂ : c₂ a <;>
      simp only [Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or, if_true, if_false,
        Nat.testBit_or, Nat.zero_testBit, Bool.false_eq_true] <;>
      cases (g a).testBit k <;> simp

theorem img_or (t : Array Nat) (a b : Nat) :
    Native.img t (a ||| b) = Native.img t a ||| Native.img t b := by
  unfold Native.img
  exact foldl_ite_split _ _ _ (fun i => Nat.testBit_or a b i) _ _

theorem shl_or_eq (x y n : Nat) (hy : y < 2 ^ n) : x <<< n ||| y = x * 2 ^ n + y := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hy, Nat.shiftLeft_eq]

theorem keyL_def (l : List Nat) :
    Native.keyL l = l.foldl (fun acc m => (acc <<< 24) ||| m) 0 := rfl

theorem pow_succ24 (n : Nat) : 2 ^ (24 * (n + 1)) = 2 ^ 24 * 2 ^ (24 * n) := by
  rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]

theorem keyL_foldl : ∀ (l : List Nat), (∀ m ∈ l, m < 2 ^ 24) → ∀ acc,
    l.foldl (fun acc m => (acc <<< 24) ||| m) acc =
      acc * 2 ^ (24 * l.length) + l.foldl (fun acc m => (acc <<< 24) ||| m) 0
  | [], _, acc => by simp
  | m :: l, hl, acc => by
    have hm := hl m List.mem_cons_self
    have hl' : ∀ x ∈ l, x < 2 ^ 24 := fun x hx => hl x (List.mem_cons_of_mem m hx)
    simp only [List.foldl_cons, Nat.zero_shiftLeft, Nat.zero_or]
    rw [keyL_foldl l hl' (acc <<< 24 ||| m), keyL_foldl l hl' m, shl_or_eq acc m 24 hm,
      List.length_cons, pow_succ24]
    ring

theorem keyL_cons {m : Nat} {l : List Nat} (hl : ∀ x ∈ l, x < 2 ^ 24) :
    Native.keyL (m :: l) = m * 2 ^ (24 * l.length) + Native.keyL l := by
  rw [keyL_def, keyL_def]
  simp only [List.foldl_cons, Nat.zero_shiftLeft, Nat.zero_or]
  exact keyL_foldl l hl m

theorem keyL_lt : ∀ l : List Nat, (∀ m ∈ l, m < 2 ^ 24) → Native.keyL l < 2 ^ (24 * l.length)
  | [], _ => by simp [Native.keyL]
  | m :: l, hl => by
    have hm := hl m List.mem_cons_self
    have hl' : ∀ x ∈ l, x < 2 ^ 24 := fun x hx => hl x (List.mem_cons_of_mem m hx)
    rw [keyL_cons hl', List.length_cons, pow_succ24]
    have hk := keyL_lt l hl'
    calc m * 2 ^ (24 * l.length) + Native.keyL l < m * 2 ^ (24 * l.length) + 2 ^ (24 * l.length) :=
          Nat.add_lt_add_left hk _
      _ = (m + 1) * 2 ^ (24 * l.length) := by ring
      _ ≤ 2 ^ 24 * 2 ^ (24 * l.length) := Nat.mul_le_mul_right _ hm

theorem mul_add_inj {P m m' K K' : Nat} (hK : K < P) (hK' : K' < P) (e : m * P + K = m' * P + K') :
    m = m' ∧ K = K' := by
  have hP : 0 < P := by omega
  have h1 : (m * P + K) / P = m := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hK, Nat.zero_add]
  have h2 : (m * P + K) % P = K := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hK]
  have h1' : (m' * P + K') / P = m' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hK', Nat.zero_add]
  have h2' : (m' * P + K') % P = K' := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hK']
  rw [e] at h1 h2
  exact ⟨h1.symm.trans h1', h2.symm.trans h2'⟩

theorem keyL_inj : ∀ (l l' : List Nat), l.length = l'.length → (∀ m ∈ l, m < 2 ^ 24) →
    (∀ m ∈ l', m < 2 ^ 24) → Native.keyL l = Native.keyL l' → l = l'
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h
  | m :: l, m' :: l', hlen, h1, h2, e => by
    have h1' : ∀ x ∈ l, x < 2 ^ 24 := fun x hx => h1 x (List.mem_cons_of_mem m hx)
    have h2' : ∀ x ∈ l', x < 2 ^ 24 := fun x hx => h2 x (List.mem_cons_of_mem m' hx)
    have hl : l.length = l'.length := by simpa using hlen
    rw [keyL_cons h1', keyL_cons h2', hl] at e
    have k1 := keyL_lt l h1'
    have k2 := keyL_lt l' h2'
    rw [hl] at k1
    obtain ⟨rfl, e'⟩ := mul_add_inj k1 k2 e
    rw [keyL_inj l l' hl h1' h2' e']

theorem key3_eq_keyL (a b c : Nat) : Native.key3 (a, b, c) = Native.keyL [a, b, c] := by
  simp only [Native.key3, Native.keyL, List.foldl_cons, List.foldl_nil, Nat.zero_shiftLeft,
    Nat.zero_or]
  have e : a <<< 48 = (a <<< 24) <<< 24 := Nat.shiftLeft_add a 24 24
  rw [e, Nat.shiftLeft_or_distrib]

theorem key3_inj {t t' : Nat × Nat × Nat} (h : ∀ m ∈ Native.octsT t, m < 2 ^ 24)
    (h' : ∀ m ∈ Native.octsT t', m < 2 ^ 24) (e : Native.key3 t = Native.key3 t') : t = t' := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨a', b', c'⟩ := t'
  rw [key3_eq_keyL, key3_eq_keyL] at e
  have := keyL_inj [a, b, c] [a', b', c'] rfl h h' e
  simp only [List.cons.injEq, and_true] at this
  obtain ⟨rfl, rfl, rfl⟩ := this
  rfl

theorem sort3_mem (a b c : Nat) : Native.sort3 a b c ∈
    [(a, b, c), (a, c, b), (c, a, b), (b, a, c), (b, c, a), (c, b, a)] := by
  unfold Native.sort3
  split_ifs <;> simp

theorem mem_sort3 {a b c x : Nat} (h : x ∈ Native.octsT (Native.sort3 a b c)) :
    x = a ∨ x = b ∨ x = c := by
  have hp := sort3_mem a b c
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with e | e | e | e | e | e <;> rw [e] at h <;>
    simp only [Native.octsT, List.mem_cons, List.not_mem_nil, or_false] at h <;> omega

theorem mem_sortL {l : List Nat} {x : Nat} : x ∈ Native.sortL l ↔ x ∈ l := by
  rw [sortL_eq_sortN, sortN_eq]
  exact List.mem_insertionSort _

theorem length_sortL (l : List Nat) : (Native.sortL l).length = l.length := by
  rw [sortL_eq_sortN, sortN_eq]
  exact List.length_insertionSort _ _

theorem treeOK_of_replay {α : Type} [Inhabited α] [DecidableEq α] {key : α → Nat}
    {steps : List (α → α)} {base : α} {fuel : Nat} {L : List α} {par gen : List Nat}
    {pos : KTree (Nat × Nat)} (hr : replayOK key steps base fuel L par gen pos = true)
    (idx : α → Nat) (hidx : ∀ p (hp : p < L.length), idx L[p] = p) :
    Native.treeOK L.toArray par.toArray gen.toArray steps idx = true := by
  obtain ⟨-, -, hpl, hgl, ht, -⟩ := replay_facts hr
  unfold Native.treeOK Native.allLt
  simp only [Bool.and_eq_true, beq_iff_eq, List.size_toArray, hpl, hgl, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, decide_eq_true_eq, true_and]
  intro p hp
  rcases Nat.eq_zero_or_pos p with rfl | h1
  · exact Or.inl rfl
  · right
    obtain ⟨q1, q2, q3⟩ := ht p h1 hp
    rw [toArray_getElem!_eq_getD par, toArray_getElem!_eq_getD gen, toArray_getElem!_eq_getD L]
    have d : (default : Nat) = 0 := rfl
    rw [d, q3, hidx p hp]
    exact ⟨⟨q1, q2⟩, rfl⟩

end CFSG.KC.M24G
