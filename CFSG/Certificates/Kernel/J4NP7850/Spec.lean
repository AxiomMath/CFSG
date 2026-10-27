module

public import Certificates.Data.Kernel.J4NP7850
public import Aesop.BuiltinRules
public import Batteries.Data.List.Lemmas
public import Batteries.Data.Nat.Bitwise.Lemmas
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.NeZero
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Push

public section

namespace CFSG.KS.J4NP7850

open CFSG.KC.Loop CFSG.KC.J4Q CFSG.KD.J4M4F CFSG.KD.J4NP7850

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem beq_iff {a b : Nat} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem neN_iff {a b : Nat} : neN a b = true ↔ a ≠ b := by
  unfold neN
  rw [notB_eq]
  cases h : Nat.beq a b
  · refine ⟨fun _ e => ?_, fun _ => rfl⟩
    rw [beq_iff.mpr e] at h
    exact Bool.noConfusion h
  · exact ⟨fun h' => (Bool.false_ne_true h').elim, fun hne => (hne (beq_iff.mp h)).elim⟩

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem getN_eq (d : Nat) : ∀ (l : List Nat) (i : Nat), getN d l i = l.getD i d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getN_eq d l i

theorem allR_iff {n : Nat} {f : Nat → Bool} : allR n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allR]
  | succ n ih =>
    change andB (allR n f) (f n) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact h1 i h
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

theorem memK_iff {x : Nat} : ∀ {l : List Nat}, memK x l = true ↔ x ∈ l
  | [] => by simp [memK]
  | y :: l => by
    change orB (Nat.beq x y) (memK x l) = true ↔ _
    rw [orB_eq, Bool.or_eq_true, memK_iff, List.mem_cons, beq_iff]

theorem allL_iff {f : Nat → Bool} : ∀ {l : List Nat}, allL l f = true ↔ ∀ y ∈ l, f y = true
  | [] => by simp [allL]
  | y :: l => by
    change andB (f y) (allL l f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, allL_iff, List.forall_mem_cons]

theorem land_shiftRight_one (s t : Nat) :
    Nat.beq (Nat.land (Nat.shiftRight s t) 1) 1 = s.testBit t := by
  have e1 : Nat.land (Nat.shiftRight s t) 1 = (s >>> t) % 2 := Nat.and_one_is_mod _
  have e2 : s.testBit t = ((s >>> t) % 2 != 0) := by rw [Nat.testBit, Nat.one_and_eq_mod_two]
  rw [e1, e2]
  rcases Nat.mod_two_eq_zero_or_one (s >>> t) with h | h <;> rw [h] <;> rfl

theorem combK_succ (B : List Nat) (n s : Nat) :
    combK B (n + 1) s = if s.testBit n then combK B n s ^^^ B.getD n 0 else combK B n s := by
  change Bool.rec (motive := fun _ => Nat) (combK B n s) (Nat.xor (combK B n s) (getN 0 B n))
    (Nat.beq (Nat.land (Nat.shiftRight s n) 1) 1) = _
  rw [land_shiftRight_one, getN_eq]
  cases s.testBit n <;> rfl

theorem combK_xor (B : List Nat) : ∀ (n s t : Nat),
    combK B n (s ^^^ t) = combK B n s ^^^ combK B n t
  | 0, _, _ => by
    change (0 : Nat) = 0 ^^^ 0
    rw [Nat.zero_xor]
  | n + 1, s, t => by
    rw [combK_succ, combK_succ, combK_succ, combK_xor B n s t, Nat.testBit_xor]
    cases s.testBit n <;> cases t.testBit n <;> simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

theorem combK_mod (B : List Nat) : ∀ (n s : Nat), combK B n (s % 2 ^ n) = combK B n s
  | 0, _ => rfl
  | n + 1, s => by
    rw [combK_succ, combK_succ, Nat.testBit_mod_two_pow]
    have e : combK B n (s % 2 ^ (n + 1)) = combK B n s := by
      rw [← combK_mod B n (s % 2 ^ (n + 1)), ← combK_mod B n s, Nat.mod_mod_of_dvd]
      exact Nat.pow_dvd_pow 2 (Nat.le_succ n)
    rw [e]
    simp

theorem inSpanK_iff {B : List Nat} {n x : Nat} :
    inSpanK B n x = true ↔ ∃ s < 2 ^ n, combK B n s = x := by
  unfold inSpanK
  have e : Nat.shiftLeft 1 n = 2 ^ n := Nat.one_shiftLeft n
  rw [notB_eq, Bool.not_eq_true', ← Bool.not_eq_true, allR_iff, e]
  simp only [neN_iff, ne_eq, not_forall, not_not, exists_prop]

theorem combK_xor_mem {B : List Nat} {n x y : Nat} (hx : ∃ s < 2 ^ n, combK B n s = x)
    (hy : ∃ s < 2 ^ n, combK B n s = y) : ∃ s < 2 ^ n, combK B n s = x ^^^ y := by
  obtain ⟨s, -, rfl⟩ := hx
  obtain ⟨t, -, rfl⟩ := hy
  refine ⟨(s ^^^ t) % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n), ?_⟩
  rw [combK_mod, combK_xor]

theorem nsK_spec {x : Nat} : ∀ {l : List Nat}, l.Pairwise (· < ·) → nsK x l = true → x ∉ l
  | [], _, _ => List.not_mem_nil
  | y :: l, hl, h => by
    change Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (nsK x l) false (Nat.beq x y)) true (Nat.blt x y) = true
      at h
    obtain ⟨hy, hl'⟩ := List.pairwise_cons.mp hl
    rw [List.mem_cons, not_or]
    cases hxy : Nat.blt x y
    · rw [hxy] at h
      cases hb : Nat.beq x y
      · rw [hb] at h
        refine ⟨fun e => ?_, nsK_spec hl' h⟩
        rw [beq_iff.mpr e] at hb
        exact Bool.noConfusion hb
      · rw [hb] at h
        exact (Bool.false_ne_true h).elim
    · have hlt : x < y := by simpa using hxy
      refine ⟨Nat.ne_of_lt hlt, fun hm => ?_⟩
      exact absurd (hy x hm) (Nat.lt_asymm hlt)

theorem ltHead_spec {x : Nat} {ch : List Nat} {rest : List (List Nat)}
    (h : ltHead x (ch :: rest) = false) : ∃ y ∈ ch, y ≤ x := by
  cases ch with
  | nil => exact Bool.noConfusion h
  | cons y ch =>
    change Nat.blt x y = false at h
    refine ⟨y, List.mem_cons_self, Nat.le_of_not_lt fun hlt => ?_⟩
    have h2 : Nat.blt x y = true := by rw [Nat.blt_eq]; exact hlt
    rw [h2] at h
    exact Bool.noConfusion h

theorem ninC_spec {x : Nat} : ∀ {chs : List (List Nat)}, (∀ ch ∈ chs, ch ≠ []) →
    chs.flatten.Pairwise (· < ·) → ninC x chs = true → x ∉ chs.flatten
  | [], _, _, _ => by simp
  | ch :: rest, hne, hs, h => by
    have hne' : ∀ c ∈ rest, c ≠ [] := fun c hc => hne c (List.mem_cons_of_mem _ hc)
    change Bool.rec (motive := fun _ => Bool) (ninC x rest) (nsK x ch) (ltHead x rest) = true at h
    rw [List.flatten_cons, List.pairwise_append] at hs
    obtain ⟨hch, hrest, hcr⟩ := hs
    rw [List.flatten_cons, List.mem_append, not_or]
    cases hl : ltHead x rest
    · rw [hl] at h
      refine ⟨fun hm => ?_, ninC_spec hne' hrest h⟩
      cases rest with
      | nil => exact Bool.noConfusion hl
      | cons ch' rest' =>
        obtain ⟨y, hy, hyx⟩ := ltHead_spec hl
        have := hcr x hm y (List.mem_flatten.mpr ⟨ch', List.mem_cons_self, hy⟩)
        omega
    · rw [hl] at h
      refine ⟨nsK_spec hch h, fun hm => ?_⟩
      cases rest with
      | nil => simp at hm
      | cons ch' rest' =>
        cases ch' with
        | nil => exact hne' [] List.mem_cons_self rfl
        | cons y ch'' =>
          change Nat.blt x y = true at hl
          have hxy : x < y := by simpa using hl
          rw [List.flatten_cons] at hrest
          rw [List.flatten_cons, List.mem_append] at hm
          rcases hm with hm | hm
          · rcases List.mem_cons.mp hm with rfl | hm
            · omega
            · have := (List.pairwise_cons.mp ((List.pairwise_append.mp hrest).1)).1 x hm
              omega
          · have := (List.pairwise_append.mp hrest).2.2 y List.mem_cons_self x hm
            omega

theorem indK_testBit : ∀ (l : List Nat) (c : Nat), (indK l).testBit c = true ↔ c ∈ l
  | [], c => by
    change (0 : Nat).testBit c = true ↔ _
    simp
  | x :: l, c => by
    change (indK l ||| 1 <<< x).testBit c = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, indK_testBit l c, Nat.one_shiftLeft, Nat.testBit_two_pow,
      decide_eq_true_eq, List.mem_cons, or_comm, eq_comm]

theorem mem_spanL_go (b : Nat) : ∀ (L acc : List Nat) (x : Nat),
    x ∈ List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun y _ ih2 acc => ih2 (List.cons (Nat.xor y b) acc)) L acc ↔ x ∈ acc ∨ (x ^^^ b) ∈ L
  | [], acc, x => by simp
  | y :: L, acc, x => by
    change x ∈ List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun y _ ih2 acc => ih2 (List.cons (Nat.xor y b) acc)) L ((y ^^^ b) :: acc) ↔ _
    rw [mem_spanL_go b L, List.mem_cons, List.mem_cons]
    constructor
    · rintro ((rfl | h) | h)
      · exact Or.inr (Or.inl (by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]))
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | (h | h))
      · exact Or.inl (Or.inr h)
      · refine Or.inl (Or.inl ?_)
        rw [← h, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      · exact Or.inr h

theorem mem_spanL_nil (x : Nat) : x ∈ spanL [] ↔ x = 0 := by
  change x ∈ [0] ↔ _
  simp

theorem mem_spanL_cons (b : Nat) (B : List Nat) (x : Nat) :
    x ∈ spanL (b :: B) ↔ x ∈ spanL B ∨ (x ^^^ b) ∈ spanL B :=
  mem_spanL_go b (spanL B) (spanL B) x

theorem imgP_eq (TP w : List Nat) : ∀ B : List Nat, imgP TP w B = B.map (wimgP TP w)
  | [] => rfl
  | b :: B => by
    change wimgP TP w b :: imgP TP w B = _
    rw [imgP_eq TP w B, List.map_cons]

theorem wimgP_cons (TP : List Nat) (i : Nat) (w : List Nat) (m : Nat) :
    wimgP TP (i :: w) m = actP (TP.getD i 0) (wimgP TP w m) := by
  change strictN (wimgP TP w m) (fun x => actP (getN 0 TP i) x) = _
  rw [strictN_eq, getN_eq]

@[expose] noncomputable def orbKey (TP B w : List Nat) : Nat := indK (spanL (imgP TP w B))

theorem wOK_iff : ∀ {w : List Nat}, wOK w = true ↔ ∀ i ∈ w, i < 6
  | [] => by simp [wOK]
  | i :: w => by
    change andB (Nat.blt i 6) (wOK w) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, wOK_iff, List.forall_mem_cons, Nat.blt_eq]

theorem orbK_go (TP B : List Nat) : ∀ (W : List (List Nat)) (prev : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun w _ ih prev => strictB (indK (spanL (imgP TP w B))) fun k =>
        andB (wOK w) (andB (Nat.blt prev k) (ih k))) W prev = true →
    (∀ w ∈ W, ∀ i ∈ w, i < 6) ∧ (∀ w ∈ W, prev < orbKey TP B w) ∧
      (W.map (orbKey TP B)).Pairwise (· < ·)
  | [], _, _ => by simp
  | w :: W, prev, h => by
    change strictB (orbKey TP B w) (fun k =>
      andB (wOK w) (andB (Nat.blt prev k) (List.rec (motive := fun _ => Nat → Bool)
        (fun _ => true) (fun w _ ih prev => strictB (indK (spanL (imgP TP w B))) fun k =>
          andB (wOK w) (andB (Nat.blt prev k) (ih k))) W k))) = true at h
    rw [strictB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨hw, hlt, hrest⟩ := h
    obtain ⟨h1, h2, h3⟩ := orbK_go TP B W (orbKey TP B w) hrest
    refine ⟨?_, ?_, ?_⟩
    · rintro w' hw'
      rcases List.mem_cons.mp hw' with rfl | hw'
      · exact wOK_iff.mp hw
      · exact h1 w' hw'
    · rintro w' hw'
      rcases List.mem_cons.mp hw' with rfl | hw'
      · exact hlt
      · exact Nat.lt_trans hlt (h2 w' hw')
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨?_, h3⟩
      intro k hk
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hk
      exact h2 w' hw'

theorem orbK_spec {TP B : List Nat} {W : List (List Nat)} (h : orbK TP B W = true) :
    (∀ w ∈ W, ∀ i ∈ w, i < 6) ∧ (W.map (orbKey TP B)).Pairwise (· < ·) := by
  obtain ⟨h1, -, h3⟩ := orbK_go TP B W 0 h
  exact ⟨h1, h3⟩

theorem land_one_eq (v p : Nat) :
    Nat.land (Nat.shiftRight v p) 1 = if v.testBit p then 1 else 0 := by
  have e1 : Nat.land (Nat.shiftRight v p) 1 = (v >>> p) % 2 := Nat.and_one_is_mod _
  have e2 : v.testBit p = ((v >>> p) % 2 != 0) := by rw [Nat.testBit, Nat.one_and_eq_mod_two]
  rw [e1, e2]
  rcases Nat.mod_two_eq_zero_or_one (v >>> p) with h | h <;> rw [h] <;> rfl

theorem blt_shift112 {p : Nat} (h : Nat.blt p (Nat.shiftLeft 1 112) = true) : p < 2 ^ 112 := by
  have e : Nat.shiftLeft 1 112 = 2 ^ 112 := Nat.one_shiftLeft 112
  rw [e, Nat.blt_eq] at h
  exact h

theorem piK_spec {rm G : Nat} {PV KW : List Nat} (h : piK rm G PV KW = true) :
    ∀ k < 31, PV.getD k 0 < 2 ^ 112 ∧ vecJ rm (PV.getD k 0) G = KW.getD k 0 := by
  intro k hk
  have h1 := allR_iff.mp h k hk
  rw [getN_eq, strictB_eq, andB_eq, Bool.and_eq_true, beq_iff, getN_eq] at h1
  exact ⟨blt_shift112 h1.1, h1.2⟩

theorem y8FixK_spec {rm : Nat} {Us PV B : List Nat} (h : y8FixK rm Us PV B = true) :
    ∀ t < 6, ∀ k < 31, etaV rm Us (B.getD t 0) (PV.getD k 0) = PV.getD k 0 := by
  intro t ht k hk
  have h1 := allR_iff.mp (allR_iff.mp h t ht) k hk
  rw [getN_eq, strictB_eq, beq_iff, getN_eq] at h1
  exact h1

theorem y8MoveK_spec {rm : Nat} {Us PV C MW : List Nat} (h : y8MoveK rm Us PV C MW = true) :
    ∀ s < 31, MW.getD s 0 < 31 ∧ etaV rm Us (combK C 5 (s + 1)) (PV.getD (MW.getD s 0) 0) ≠
      PV.getD (MW.getD s 0) 0 := by
  intro s hs
  have h1 := allR_iff.mp h s hs
  rw [getN_eq, strictB_eq, getN_eq, strictB_eq, andB_eq, Bool.and_eq_true, Nat.blt_eq,
    neN_iff] at h1
  exact h1

theorem y8DecK_spec {L B C Pr : List Nat} (h : y8DecK L B C Pr = true) :
    (∀ s < 64, combK B 6 s ∈ L) ∧ (∀ y ∈ L, ∃ s < 2 ^ 6, combK B 6 s = y) ∧
      ∀ j < 11, (∃ s < 2 ^ 5, combK C 5 s = Pr.getD j 0) ∧ 2 ^ j ^^^ Pr.getD j 0 ∈ L := by
  unfold y8DecK at h
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun s hs => memK_iff.mp (allR_iff.mp h1 s hs),
    fun y hy => inSpanK_iff.mp (allL_iff.mp h2 y hy), fun j hj => ?_⟩
  have h4 := allR_iff.mp h3 j hj
  rw [getN_eq, strictB_eq, andB_eq, Bool.and_eq_true, inSpanK_iff, memK_iff] at h4
  have e : Nat.shiftLeft 1 j = 2 ^ j := Nat.one_shiftLeft j
  rw [← e]
  exact h4

theorem moveK_spec {rm : Nat} {Us PV : List Nat} {k : Nat} (h : moveK rm Us PV k = true) :
    k < 31 ∧ ∀ k' < 31, etaV rm Us 4 (PV.getD k 0) ≠ PV.getD k' 0 := by
  unfold moveK at h
  rw [andB_eq, Bool.and_eq_true, Nat.blt_eq, getN_eq, strictB_eq] at h
  refine ⟨h.1, fun k' hk' => ?_⟩
  have h1 := allR_iff.mp h.2 k' hk'
  rw [getN_eq, neN_iff] at h1
  exact h1

theorem kwFixK_spec {rm one : Nat} {FM KW : List Nat} (h : kwFixK rm one FM KW = true) :
    ∀ j < 10, ∀ k < 31, vecJ rm (KW.getD k 0) (FM.getD j one) = KW.getD k 0 := by
  intro j hj k hk
  have h1 := allR_iff.mp h j hj
  rw [getN_eq, strictB_eq] at h1
  have h2 := allR_iff.mp h1 k hk
  rw [getN_eq, strictB_eq, beq_iff] at h2
  exact h2

theorem basisK_spec {rm one : Nat} {FM P B : List Nat} (h : basisK rm one FM P B = true) :
    (∀ s < 6, P.getD s 0 < 112) ∧ ∀ t < 6, B.getD t 0 < 2 ^ 112 ∧
      (∀ j < 10, vecJ rm (B.getD t 0) (FM.getD j one) = B.getD t 0) ∧
      ∀ s < 6, (B.getD t 0).testBit (P.getD s 0) = decide (s = t) := by
  unfold basisK at h
  rw [andB_eq, Bool.and_eq_true] at h
  refine ⟨fun s hs => ?_, fun t ht => ?_⟩
  · have h1 := allR_iff.mp h.1 s hs
    rw [getN_eq, Nat.blt_eq] at h1
    exact h1
  · have h1 := allR_iff.mp h.2 t ht
    rw [getN_eq, strictB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h1
    obtain ⟨ha, hb, hc⟩ := h1
    refine ⟨blt_shift112 ha, fun j hj => ?_, fun s hs => ?_⟩
    · have h2 := allR_iff.mp hb j hj
      rw [getN_eq, beq_iff] at h2
      exact h2
    · have h2 := allR_iff.mp hc s hs
      rw [getN_eq, beq_iff, land_one_eq] at h2
      by_cases hst : s = t
      · subst hst
        rw [Nat.beq_refl] at h2
        change _ = 1 at h2
        cases hb' : (B.getD s 0).testBit (P.getD s 0)
        · rw [hb'] at h2
          simp at h2
        · simp
      · have hb2 : Nat.beq s t = false := by
          cases hq : Nat.beq s t
          · rfl
          · exact absurd (beq_iff.mp hq) hst
        rw [hb2] at h2
        change _ = 0 at h2
        cases hb' : (B.getD t 0).testBit (P.getD s 0)
        · simp [hst]
        · rw [hb'] at h2
          simp at h2

theorem spanK_spec {B K U : List Nat} (h : spanK B K U = true) :
    ∀ s < 63, combK B 6 (s + 1) ∈ K ∨ combK B 6 (s + 1) ∈ U := by
  intro s hs
  have h1 := allR_iff.mp h s hs
  rw [strictB_eq, orB_eq, Bool.or_eq_true, memK_iff, memK_iff] at h1
  exact h1

theorem othVK_spec {rm G : Nat} {U Qs : List Nat} (h : othVK rm G U Qs = true) :
    ∀ i < 32, vecJ rm (Qs.getD i 0) G = U.getD i 0 := by
  intro i hi
  have h1 := allR_iff.mp h i hi
  rw [getN_eq, getN_eq, beq_iff] at h1
  exact h1

theorem othSK_spec {R0 : Nat} {Qs : List Nat} {S5 S6 : List (List Nat)}
    (hne5 : ∀ ch ∈ S5, ch ≠ []) (hne6 : ∀ ch ∈ S6, ch ≠ [])
    (hs5 : S5.flatten.Pairwise (· < ·)) (hs6 : S6.flatten.Pairwise (· < ·))
    (h : othSK R0 Qs S5 S6 = true) :
    ∀ i < 32, Qs.getD i 0 ≠ R0 ∧ Qs.getD i 0 ∉ S5.flatten ∧ Qs.getD i 0 ∉ S6.flatten := by
  intro i hi
  have h1 := allR_iff.mp h i hi
  rw [getN_eq, strictB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, neN_iff] at h1
  exact ⟨h1.1, ninC_spec hne5 hs5 h1.2.1, ninC_spec hne6 hs6 h1.2.2⟩

theorem duadK_spec {c rm one G U4 : Nat} {FM : List Nat} (h : duadK c rm one G FM U4 = true) :
    mulJ c rm G (fRK c rm one FM 420) = mulJ c rm U4 G := by
  unfold duadK at h
  rw [strictB_eq, beq_iff] at h
  exact h

end CFSG.KS.J4NP7850
