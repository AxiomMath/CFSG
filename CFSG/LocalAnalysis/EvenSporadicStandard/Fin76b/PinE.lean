module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TableE

public section

namespace CFSG.EvenSporadicStandard.Fin76b.TablePin

open Subgroup

@[expose] def members (n M : ℕ) : List ℕ := (List.range n).filter fun a => M.testBit a

theorem mem_members {n M a : ℕ} : a ∈ members n M ↔ a < n ∧ M.testBit a = true := by
  simp [members, List.mem_filter, List.mem_range]

@[expose] def prodMask (n : ℕ) (mul : ℕ → ℕ → ℕ) (M N : ℕ) : ℕ :=
  let bn := members n N
  (members n M).foldl (fun acc m => bn.foldl (fun acc' c => acc' ||| 1 <<< mul m c) acc) 0

theorem foldl_or_testBit {α : Type*} (l : List α) (f : α → ℕ) (acc x : ℕ) :
    (l.foldl (fun a y => a ||| 1 <<< f y) acc).testBit x = true ↔
      acc.testBit x = true ∨ ∃ y ∈ l, f y = x := by
  induction l generalizing acc with
  | nil => simp
  | cons y l ih =>
    rw [List.foldl_cons, ih]
    simp only [Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow,
      decide_eq_true_eq, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

theorem testBit_prodMask {n : ℕ} {mul : ℕ → ℕ → ℕ} {M N x : ℕ} :
    (prodMask n mul M N).testBit x = true ↔
      ∃ m c, m < n ∧ c < n ∧ M.testBit m = true ∧ N.testBit c = true ∧ mul m c = x := by
  unfold prodMask
  simp only
  have key : ∀ (l : List ℕ) (acc : ℕ),
      (l.foldl (fun acc m => (members n N).foldl (fun acc' c => acc' ||| 1 <<< mul m c) acc)
        acc).testBit x = true ↔
      acc.testBit x = true ∨ ∃ m ∈ l, ∃ c ∈ members n N, mul m c = x := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons m l ih =>
      intro acc
      rw [List.foldl_cons, ih, foldl_or_testBit (members n N) (mul m)]
      simp only [List.mem_cons, exists_eq_or_imp]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  rw [key]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, mem_members]
  constructor
  · rintro ⟨m, ⟨hm, hmM⟩, c, ⟨hc, hcN⟩, h⟩
    exact ⟨m, c, hm, hc, hmM, hcN, h⟩
  · rintro ⟨m, c, hm, hc, hmM, hcN, h⟩
    exact ⟨m, ⟨hm, hmM⟩, c, ⟨hc, hcN⟩, h⟩

@[expose] def invIdx (n : ℕ) (mul : ℕ → ℕ → ℕ) (g : ℕ) : ℕ :=
  ((List.range n).find? fun b => mul g b == 0).getD 0

@[expose] def conjMask (n : ℕ) (mul : ℕ → ℕ → ℕ) (a : ℕ) : ℕ :=
  (List.range n).foldl (fun acc g => acc ||| 1 <<< mul (mul g a) (invIdx n mul g)) 0

@[expose] def nclAux (n : ℕ) (mul : ℕ → ℕ → ℕ) (C : ℕ) : ℕ → ℕ → ℕ
  | 0, S => S
  | k + 1, S =>
    let S' := S ||| prodMask n mul S C
    if S' == S then S else nclAux n mul C k S'

@[expose] def nclMask (n : ℕ) (mul : ℕ → ℕ → ℕ) (a : ℕ) : ℕ :=
  nclAux n mul (conjMask n mul a) (n + 1) 1

@[expose] def nclVals (n : ℕ) (mul : ℕ → ℕ → ℕ) : List ℕ :=
  ((List.range n).map (nclMask n mul)).dedup

@[expose] def latStep (n : ℕ) (mul : ℕ → ℕ → ℕ) (V : List ℕ) (L : List ℕ) : List ℕ :=
  (L ++ L.flatMap fun M => V.map (prodMask n mul M)).dedup

@[expose] def latIter (n : ℕ) (mul : ℕ → ℕ → ℕ) (V : List ℕ) : ℕ → List ℕ → List ℕ
  | 0, L => L
  | k + 1, L =>
    let L' := latStep n mul V L
    if L'.length == L.length then L else latIter n mul V k L'

@[expose] def lattice (n : ℕ) (mul : ℕ → ℕ → ℕ) : List ℕ :=
  latIter n mul (nclVals n mul) 40 [1]

@[expose] def maskOf (l : List ℕ) : ℕ := l.foldl (fun acc a => acc ||| 1 <<< a) 0

@[expose] def shape (n : ℕ) (mul : ℕ → ℕ → ℕ) (tI M : ℕ) : Bool :=
  let B := members n M
  B.contains tI &&
    B.any (fun a => B.any fun b => mul a b != mul b a) &&
    B.all (fun a => B.all fun b => mul a b == mul b a || mul a b == mul (mul b a) tI) &&
    B.all (fun y => !(B.all fun f => mul f y == mul y f) || y == 0 || y == tI) &&
    (List.range n).all (fun a => !(B.all fun e => mul a e == mul e a) || a == 0 || a == tI)

@[expose] def pinCheck (n : ℕ) (mul : ℕ → ℕ → ℕ) (tI : ℕ) : Bool :=
  let V := nclVals n mul
  let L := lattice n mul
  TableE.eCheck n mul tI && L.contains 1 &&
    L.all (fun M => V.all fun NC => L.contains (prodMask n mul M NC)) &&
    L.all (fun M => !shape n mul tI M || M == maskOf (TableE.eList n mul tI))

structure TableSpec {X : Type*} [Group X] (T : Subgroup X) (t : X) (n : ℕ) (elt : ℕ → X)
    (mul : ℕ → ℕ → ℕ) (tI : ℕ) : Prop where
  memT : ∀ a < n, elt a ∈ T
  surj : ∀ x ∈ T, ∃ a < n, elt a = x
  inj : ∀ a b, a < n → b < n → elt a = elt b → a = b
  mul_spec : ∀ a b, a < n → b < n → mul a b < n ∧ elt a * elt b = elt (mul a b)
  zero : elt 0 = 1
  tI_lt : tI < n
  tI_elt : elt tI = t
  pos : 0 < n

theorem all_eq_false_iff {α : Type*} (l : List α) (p : α → Bool) :
    l.all p = false ↔ ¬ ∀ x ∈ l, p x = true := by
  rw [Bool.eq_false_iff, ne_eq, List.all_eq_true]

theorem shape_iff {n : ℕ} {mul : ℕ → ℕ → ℕ} {tI M : ℕ} :
    shape n mul tI M = true ↔
      (tI ∈ members n M ∧ (∃ a ∈ members n M, ∃ b ∈ members n M, mul a b ≠ mul b a) ∧
        (∀ a ∈ members n M, ∀ b ∈ members n M, mul a b = mul b a ∨ mul a b = mul (mul b a) tI) ∧
        (∀ y ∈ members n M, (∀ f ∈ members n M, mul f y = mul y f) → y = 0 ∨ y = tI) ∧
        (∀ a < n, (∀ e ∈ members n M, mul a e = mul e a) → a = 0 ∨ a = tI)) := by
  simp only [shape, Bool.and_eq_true, List.contains_iff_mem, List.any_eq_true, List.all_eq_true,
    bne_iff_ne, ne_eq, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true', List.mem_range,
    all_eq_false_iff]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    refine ⟨h1, h2, h3, fun y hy hall => ?_, fun a ha hall => ?_⟩
    · rcases h4 y hy with (h | h) | h
      · exact absurd (fun f hf => by simpa using hall f hf) h
      · exact Or.inl h
      · exact Or.inr h
    · rcases h5 a ha with (h | h) | h
      · exact absurd (fun f hf => by simpa using hall f hf) h
      · exact Or.inl h
      · exact Or.inr h
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨⟨⟨⟨h1, h2⟩, h3⟩, fun y hy => ?_⟩, fun a ha => ?_⟩
    · by_cases hall : ∀ f ∈ members n M, mul f y = mul y f
      · rcases h4 y hy hall with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · exact Or.inl (Or.inl fun h => hall fun f hf => by simpa using h f hf)
    · by_cases hall : ∀ e ∈ members n M, mul a e = mul e a
      · rcases h5 a ha hall with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · exact Or.inl (Or.inl fun h => hall fun f hf => by simpa using h f hf)

end CFSG.EvenSporadicStandard.Fin76b.TablePin
