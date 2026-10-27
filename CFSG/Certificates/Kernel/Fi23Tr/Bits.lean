module

public import Certificates.Data.CFSGNative.Fi23.Tr
import CFSG.Certificates.Kernel.Fi22LH.Loops

public section

namespace CFSG.KS.Fi23Tr

open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native

instance byteArray_lawfulBEq : LawfulBEq ByteArray where
  eq_of_beq {a b} h := by
    change ByteArray.beq a b = true at h
    unfold ByteArray.beq at h
    exact ByteArray.ext (eq_of_beq h)
  rfl {a} := by
    change ByteArray.beq a a = true
    unfold ByteArray.beq
    exact beq_self_eq_true _

@[expose] def Canon (B : PBits) : Prop := B.size = 3959 ∧ pBit B 31671 = false

@[expose] def bitOf (b : UInt8) (i : Nat) : Bool := b >>> i.toUInt8 &&& 1 != 0

theorem bitOf_or_small : ∀ n < 256, ∀ i < 8, ∀ j < 8,
    bitOf (n.toUInt8 ||| (1 : UInt8) <<< i.toUInt8) j = (bitOf n.toUInt8 j || j == i) := by
  decide +kernel

theorem bitOf_testBit_small : ∀ n < 256, ∀ i < 8, bitOf n.toUInt8 i = n.testBit i := by
  decide +kernel

theorem bitOf_zero : ∀ i < 8, bitOf 0 i = false := by decide

theorem toUInt8_toNat (b : UInt8) : b.toNat.toUInt8 = b := by
  apply UInt8.toNat_inj.1
  rw [Nat.toUInt8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt b.toNat_lt]

theorem bitOf_or (b : UInt8) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    bitOf (b ||| (1 : UInt8) <<< i.toUInt8) j = (bitOf b j || j == i) := by
  have := bitOf_or_small b.toNat b.toNat_lt i hi j hj
  rwa [toUInt8_toNat] at this

theorem bitOf_testBit (b : UInt8) {i : Nat} (hi : i < 8) : bitOf b i = b.toNat.testBit i := by
  have := bitOf_testBit_small b.toNat b.toNat_lt i hi
  rwa [toUInt8_toNat] at this

theorem byte_ext {a b : UInt8} (h : ∀ i < 8, bitOf a i = bitOf b i) : a = b := by
  apply UInt8.toNat_inj.1
  apply Nat.eq_of_testBit_eq
  intro i
  rcases Nat.lt_or_ge i 8 with hi | hi
  · rw [← bitOf_testBit a hi, ← bitOf_testBit b hi, h i hi]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le a.toNat_lt (Nat.pow_le_pow_right (by omega) hi)),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le b.toNat_lt (Nat.pow_le_pow_right (by omega) hi))]

theorem get!_data (B : ByteArray) (i : Nat) : B.get! i = B.data[i]! := by
  cases B
  rfl

theorem set!_data (B : ByteArray) (i : Nat) (v : UInt8) : (B.set! i v).data = B.data.set! i v := by
  cases B
  rfl

theorem size_data (B : ByteArray) : B.size = B.data.size := rfl

theorem pBit_eq (B : PBits) (x : Nat) : pBit B x = bitOf (B.data[x / 8]!) (x % 8) := by
  unfold pBit bitOf
  rw [get!_data]

theorem size_pSet (B : PBits) (x : Nat) : (pSet B x).size = B.size := by
  unfold pSet
  rw [size_data, size_data, set!_data, Array.size_set!]

theorem pBit_pSet {B : PBits} {x : Nat} (hx : x / 8 < B.size) (y : Nat) :
    pBit (pSet B x) y = (pBit B y || y == x) := by
  unfold pSet
  rw [pBit_eq, pBit_eq, set!_data, get!_data]
  by_cases e : x / 8 = y / 8
  · rw [← e, Array.getElem!_set!_self _ _ _ (by rw [← size_data]; exact hx),
      bitOf_or _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))]
    congr 1
    apply Bool.eq_iff_iff.2
    simp only [beq_iff_eq]
    constructor
    · intro h
      omega
    · intro h
      rw [h]
  · rw [Array.getElem!_set!_ne _ _ _ _ e]
    have : (y == x) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      exact e (by rw [h])
    rw [this, Bool.or_false]

theorem pBit_pZero (y : Nat) : pBit (pZero ()) y = false := by
  rw [pBit_eq]
  unfold pZero
  by_cases h : y / 8 < 3959
  · rw [getElem!_pos _ _ (by simpa using h)]
    simp only [Array.getElem_replicate]
    exact bitOf_zero _ (Nat.mod_lt _ (by omega))
  · rw [getElem!_neg _ _ (by simpa using h)]
    exact bitOf_zero _ (Nat.mod_lt _ (by omega))

theorem size_pZero : (pZero ()).size = 3959 := by
  unfold pZero
  rw [size_data]
  simp

theorem pOf_eq (z : PBits) (xs : Array Nat) : pOf z xs = xs.toList.foldl pSet z := by
  unfold pOf
  rw [Array.foldl_toList]

theorem foldl_pSet (l : List Nat) : ∀ z : PBits, (l.foldl pSet z).size = z.size ∧
    ((∀ x ∈ l, x / 8 < z.size) → ∀ y, pBit (l.foldl pSet z) y = (pBit z y || l.contains y)) := by
  induction l with
  | nil => intro z; simp
  | cons a l ih =>
    intro z
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (pSet z a)
    rw [size_pSet] at h1 h2
    refine ⟨h1, fun hl y => ?_⟩
    rw [h2 (fun x hx => hl x (List.mem_cons_of_mem _ hx)), pBit_pSet (hl a List.mem_cons_self),
      List.contains_cons]
    cases pBit z y <;> cases (y == a) <;> cases l.contains y <;> rfl

theorem size_pOf {z : PBits} (xs : Array Nat) : (pOf z xs).size = z.size := by
  rw [pOf_eq]
  exact (foldl_pSet _ z).1

theorem pBit_pOf {z : PBits} (hz : z.size = 3959) {xs : Array Nat} (hxs : ∀ x ∈ xs, x < 31672)
    (y : Nat) : pBit (pOf z xs) y = (pBit z y || xs.contains y) := by
  rw [pOf_eq, (foldl_pSet _ z).2 (fun x hx => by
    have := hxs x (by simpa using hx)
    omega)]
  congr 1
  simp

@[expose] def imgByte (T : Table) (b : UInt8) (w : Nat) (C : PBits) : PBits :=
  (List.range 8).foldl (fun C i => if bitOf b i = true then pSet C (ap T (8 * w + i)) else C) C

theorem imgByte_zero (T : Table) (w : Nat) (C : PBits) : imgByte T 0 w C = C := by
  unfold imgByte
  have : ∀ (l : List Nat), (∀ i ∈ l, i < 8) → ∀ C : PBits,
      l.foldl (fun C i => if bitOf 0 i = true then pSet C (ap T (8 * w + i)) else C) C = C := by
    intro l
    induction l with
    | nil => intro _ C; rfl
    | cons a l ih =>
      intro hl C
      rw [List.foldl_cons, bitOf_zero a (hl a List.mem_cons_self)]
      exact ih (fun i hi => hl i (List.mem_cons_of_mem _ hi)) C
  exact this _ (fun i hi => List.mem_range.1 hi) C

theorem pImg_eq (z : PBits) (T : Table) (B : PBits) :
    pImg z T B = (List.range 3959).foldl (fun C w => imgByte T (B.get! w) w C) z := by
  unfold pImg
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', bind_pure]
  refine CFSG.KS.Fi22LH.forIn_yield _ (fun w s => imgByte T (B.get! w) w s) (fun w s => ?_) _ _
  have hin : ∀ s : PBits, (forIn (m := Id) (List.range 8) s fun i s =>
      if (B.get! w >>> i.toUInt8 &&& 1 != 0) = true then pure (ForInStep.yield (pSet s (ap T (8 * w + i))))
      else pure (ForInStep.yield s)) = imgByte T (B.get! w) w s := fun s =>
    CFSG.KS.Fi22LH.forIn_yield _ _ (fun i s => by unfold bitOf; split <;> rfl) _ _
  split
  · rename_i hb
    rw [bind_pure_comp, hin]
    rfl
  · rename_i hb
    have : B.get! w = 0 := by simpa using hb
    rw [this, imgByte_zero]
    rfl

theorem fold_cond {α : Type} (c : α → Bool) (v : α → Nat) :
    ∀ (l : List α), (∀ a ∈ l, c a = true → v a < 31672) → ∀ C : PBits, C.size = 3959 →
      (l.foldl (fun C a => if c a = true then pSet C (v a) else C) C).size = 3959 ∧
      ∀ y, pBit (l.foldl (fun C a => if c a = true then pSet C (v a) else C) C) y = true ↔
        pBit C y = true ∨ ∃ a ∈ l, c a = true ∧ v a = y
  | [], _, C, hC => ⟨hC, fun y => by simp⟩
  | a :: l, hl, C, hC => by
    rw [List.foldl_cons]
    have hl' : ∀ a ∈ l, c a = true → v a < 31672 := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    by_cases hca : c a = true
    · rw [if_pos hca]
      have ha := hl a List.mem_cons_self hca
      have hs : (pSet C (v a)).size = 3959 := by rw [size_pSet, hC]
      obtain ⟨h1, h2⟩ := fold_cond c v l hl' _ hs
      refine ⟨h1, fun y => ?_⟩
      rw [h2, pBit_pSet (by rw [hC]; omega), Bool.or_eq_true, beq_iff_eq]
      constructor
      · rintro ((h | h) | ⟨x, hx, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨a, List.mem_cons_self, hca, h.symm⟩
        · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, h⟩
      · rintro (h | ⟨x, hx, h⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact Or.inl (Or.inr h.2.symm)
          · exact Or.inr ⟨x, hx, h⟩
    · rw [if_neg hca]
      obtain ⟨h1, h2⟩ := fold_cond c v l hl' C hC
      refine ⟨h1, fun y => ?_⟩
      rw [h2]
      constructor
      · rintro (h | ⟨x, hx, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, h⟩
      · rintro (h | ⟨x, hx, h⟩)
        · exact Or.inl h
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact absurd h.1 hca
          · exact Or.inr ⟨x, hx, h⟩

theorem pBit_mk (B : PBits) {w i : Nat} (hi : i < 8) : pBit B (8 * w + i) = bitOf (B.get! w) i := by
  rw [pBit_eq, get!_data]
  have h1 : (8 * w + i) / 8 = w := by omega
  have h2 : (8 * w + i) % 8 = i := by omega
  rw [h1, h2]

theorem pImg_spec {z : PBits} (hz : z.size = 3959) {T : Table} (hT : ∀ x < 31672, ap T x < 31672)
    (B : PBits) : (pImg z T B).size = 3959 ∧ ∀ y, pBit (pImg z T B) y = true ↔
      pBit z y = true ∨ ∃ x < 31672, pBit B x = true ∧ ap T x = y := by
  rw [pImg_eq]
  have key : ∀ n ≤ 3959, ((List.range n).foldl (fun C w => imgByte T (B.get! w) w C) z).size = 3959 ∧
      ∀ y, pBit ((List.range n).foldl (fun C w => imgByte T (B.get! w) w C) z) y = true ↔
        pBit z y = true ∨ ∃ x < 8 * n, pBit B x = true ∧ ap T x = y := by
    intro n
    induction n with
    | zero => intro _; exact ⟨hz, fun y => by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      obtain ⟨g1, g2⟩ := fold_cond (fun i => bitOf (B.get! n) i) (fun i => ap T (8 * n + i))
        (List.range 8) (fun i hi _ => hT _ (by have := List.mem_range.1 hi; omega)) _ h1
      have g2' : ∀ y, pBit (imgByte T (B.get! n) n
          ((List.range n).foldl (fun C w => imgByte T (B.get! w) w C) z)) y = true ↔
          pBit ((List.range n).foldl (fun C w => imgByte T (B.get! w) w C) z) y = true ∨
            ∃ a ∈ List.range 8, bitOf (B.get! n) a = true ∧ ap T (8 * n + a) = y := g2
      refine ⟨g1, fun y => ?_⟩
      rw [g2', h2]
      constructor
      · rintro ((h | ⟨x, hx, h⟩) | ⟨i, hi, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨x, by omega, h⟩
        · have hi' := List.mem_range.1 hi
          exact Or.inr ⟨8 * n + i, by omega, by rw [pBit_mk B hi']; exact h.1, h.2⟩
      · rintro (h | ⟨x, hx, h⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.lt_or_ge x (8 * n) with hx' | hx'
          · exact Or.inl (Or.inr ⟨x, hx', h⟩)
          · have e : x = 8 * n + (x - 8 * n) := by omega
            have hi : x - 8 * n < 8 := by omega
            rw [e, pBit_mk B hi] at h
            exact Or.inr ⟨x - 8 * n, List.mem_range.2 hi, h⟩
  exact key 3959 (Nat.le_refl _)

theorem size_pImg {z : PBits} (hz : z.size = 3959) {T : Table} (hT : ∀ x < 31672, ap T x < 31672)
    (B : PBits) : (pImg z T B).size = 3959 := (pImg_spec hz hT B).1

theorem pBit_pImg {z : PBits} (hz : z.size = 3959) {T : Table} (hT : ∀ x < 31672, ap T x < 31672)
    (B : PBits) (y : Nat) :
    pBit (pImg z T B) y = true ↔ pBit z y = true ∨ ∃ x < 31672, pBit B x = true ∧ ap T x = y :=
  (pImg_spec hz hT B).2 y

theorem pKey_eq (z B : PBits) :
    pKey z B = (List.range 31671).foldl (fun C x => if pBit B x = true then pSet C x else C) z := by
  unfold pKey
  have : ∀ n, Nat.fold n (fun x _ C => if pBit B x = true then pSet C x else C) z =
      (List.range n).foldl (fun C x => if pBit B x = true then pSet C x else C) z := by
    intro n
    induction n with
    | zero => rw [Nat.fold_zero, List.range_zero, List.foldl_nil]
    | succ n ih =>
      rw [Nat.fold_succ, ih, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact this 31671

theorem pKey_spec {z : PBits} (hz : z.size = 3959) (B : PBits) : (pKey z B).size = 3959 ∧
    ∀ y, pBit (pKey z B) y = (pBit z y || (decide (y < 31671) && pBit B y)) := by
  rw [pKey_eq]
  obtain ⟨h1, h2⟩ := fold_cond (fun x => pBit B x) (fun x => x) (List.range 31671)
    (fun x hx _ => by have := List.mem_range.1 hx; omega) z hz
  refine ⟨h1, fun y => ?_⟩
  apply Bool.eq_iff_iff.2
  rw [h2, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨x, hx, h, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨List.mem_range.1 hx, h⟩
  · rintro (h | ⟨hy, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨y, List.mem_range.2 hy, h, rfl⟩

theorem size_pKey {z : PBits} (hz : z.size = 3959) (B : PBits) : (pKey z B).size = 3959 :=
  (pKey_spec hz B).1

theorem pBit_pKey {z : PBits} (hz : z.size = 3959) (B : PBits) (y : Nat) :
    pBit (pKey z B) y = (pBit z y || (decide (y < 31671) && pBit B y)) := (pKey_spec hz B).2 y

theorem pBits_ext {A B : PBits} (hA : A.size = 3959) (hB : B.size = 3959)
    (h : ∀ x < 31672, pBit A x = pBit B x) : A = B := by
  apply ByteArray.ext
  apply Array.ext (by rw [← size_data, ← size_data, hA, hB])
  intro w h1 h2
  have hw : w < 3959 := by rw [← size_data, hA] at h1; exact h1
  rw [← getElem!_pos A.data w h1, ← getElem!_pos B.data w h2, ← get!_data, ← get!_data]
  apply byte_ext
  intro i hi
  rw [← pBit_mk A hi, ← pBit_mk B hi]
  exact h _ (by omega)

theorem canon_ext {A B : PBits} (hA : Canon A) (hB : Canon B)
    (h : ∀ x < 31671, pBit A x = pBit B x) : A = B := by
  refine pBits_ext hA.1 hB.1 fun x hx => ?_
  rcases Nat.lt_or_ge x 31671 with hx' | hx'
  · exact h x hx'
  · have : x = 31671 := by omega
    rw [this, hA.2, hB.2]

theorem canon_pImg {T : Table} (hT : ∀ x < 31672, ap T x < 31671) (B : PBits) :
    Canon (pImg (pZero ()) T B) := by
  have hT' : ∀ x < 31672, ap T x < 31672 := fun x hx => by have := hT x hx; omega
  refine ⟨size_pImg size_pZero hT' B, ?_⟩
  cases h : pBit (pImg (pZero ()) T B) 31671 with
  | false => rfl
  | true =>
    rcases (pBit_pImg size_pZero hT' B 31671).1 h with h0 | ⟨x, hx, -, e⟩
    · rw [pBit_pZero] at h0
      exact absurd h0 (by simp)
    · have := hT x hx
      omega

theorem pBit_lt {B : PBits} (hB : Canon B) {x : Nat} (h : pBit B x = true) : x < 31671 := by
  rcases Nat.lt_or_ge x 31671 with hx | hx
  · exact hx
  · exfalso
    rcases Nat.lt_or_ge x 31672 with hx' | hx'
    · have : x = 31671 := by omega
      rw [this, hB.2] at h
      exact absurd h (by simp)
    · rw [pBit_eq, getElem!_neg _ _ (by rw [← size_data, hB.1]; omega)] at h
      have h0 : bitOf 0 (x % 8) = false := bitOf_zero _ (Nat.mod_lt _ (by omega))
      exact absurd h (by rw [Bool.not_eq_true]; exact h0)

theorem pKey_canon {B : PBits} (hB : Canon B) : pKey (pZero ()) B = B := by
  refine pBits_ext (size_pKey size_pZero B) hB.1 fun x hx => ?_
  rw [pBit_pKey size_pZero, pBit_pZero, Bool.false_or]
  by_cases h : x < 31671
  · rw [decide_eq_true h, Bool.true_and]
  · rw [decide_eq_false h, Bool.false_and]
    have : x = 31671 := by omega
    rw [this, hB.2]

end CFSG.KS.Fi23Tr
