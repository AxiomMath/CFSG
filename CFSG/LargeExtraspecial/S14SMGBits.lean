module

public import CFSG.LargeExtraspecial.S14SMGDefs

public section

namespace CFSG.LargeExtraspecial.S14.SMG

open CFSG.SmithE

theorem applyCols_xor (cols : Array Nat) (a b : Nat) :
    applyCols cols (a ^^^ b) = applyCols cols a ^^^ applyCols cols b := by
  unfold applyCols
  generalize List.range cols.size = L
  suffices h : ∀ x y, L.foldl (fun acc m => if (a ^^^ b).testBit m then acc ^^^ cols[m]! else acc)
      (x ^^^ y) = L.foldl (fun acc m => if a.testBit m then acc ^^^ cols[m]! else acc) x ^^^
        L.foldl (fun acc m => if b.testBit m then acc ^^^ cols[m]! else acc) y by
    simpa using h 0 0
  induction L with
  | nil => intro x y; rfl
  | cons m L ih =>
    intro x y
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    rw [Nat.testBit_xor]
    cases a.testBit m <;> cases b.testBit m <;>
      simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

theorem applyCols_two_pow (cols : Array Nat) {m : Nat} (hm : m < cols.size) :
    applyCols cols (2 ^ m) = cols[m]! := by
  unfold applyCols
  have key : ∀ n, (List.range n).foldl
      (fun acc j => if (2 ^ m).testBit j then acc ^^^ cols[j]! else acc) 0 =
        if m < n then cols[m]! else 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, Nat.testBit_two_pow]
      by_cases h1 : m = n
      · subst h1
        simp
      · by_cases h2 : m < n
        · simp [h1, h2, show m < n + 1 by omega]
        · simp [h1, h2, show ¬ m < n + 1 by omega]
  rw [key]
  simp [hm]

theorem applyCols_lt {cols : Array Nat} {n : Nat} (h : ∀ m < cols.size, cols[m]! < 2 ^ n)
    (c : Nat) : applyCols cols c < 2 ^ n := by
  unfold applyCols
  have key : ∀ L : List Nat, (∀ m ∈ L, m < cols.size) → ∀ a < 2 ^ n,
      L.foldl (fun acc m => if c.testBit m then acc ^^^ cols[m]! else acc) a < 2 ^ n := by
    intro L
    induction L with
    | nil => intro _ a ha; simpa using ha
    | cons m L ih =>
      intro hL a ha
      simp only [List.foldl_cons]
      apply ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
      split_ifs
      · exact Nat.xor_lt_two_pow ha (h m (hL m List.mem_cons_self))
      · exact ha
  exact key _ (fun m hm => List.mem_range.mp hm) 0 (by positivity)

theorem decomp_bit {c n : Nat} (hc : c < 2 ^ (n + 1)) :
    c = c % 2 ^ n ^^^ (if c.testBit n then 2 ^ n else 0) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_mod_two_pow]
  by_cases hi : i < n
  · split_ifs <;> simp [hi, show n ≠ i by omega]
  · by_cases hin : i = n
    · subst hin
      split_ifs with h <;> simp [h]
    · have : c.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hc
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
      split_ifs <;> simp [hi, this, Ne.symm hin]

theorem eq_of_xorLin {f g : Nat → Nat} (hf : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (hg : ∀ a b, g (a ^^^ b) = g a ^^^ g b) (n : Nat) (h : ∀ m < n, f (2 ^ m) = g (2 ^ m)) :
    ∀ c < 2 ^ n, f c = g c := by
  have hf0 : f 0 = 0 := by
    have := hf 0 0
    rw [Nat.xor_self] at this
    rw [this, Nat.xor_self]
  have hg0 : g 0 = 0 := by
    have := hg 0 0
    rw [Nat.xor_self] at this
    rw [this, Nat.xor_self]
  induction n with
  | zero =>
    intro c hc
    have : c = 0 := by simpa using hc
    rw [this, hf0, hg0]
  | succ n ih =>
    intro c hc
    rw [decomp_bit hc, hf, hg, ih (fun m hm => h m (by omega)) _ (Nat.mod_lt _ (by positivity))]
    congr 1
    split_ifs
    · exact h n (by omega)
    · rw [hf0, hg0]

theorem comp_xorLin {f g : Nat → Nat} (hf : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (hg : ∀ a b, g (a ^^^ b) = g a ^^^ g b) : ∀ a b, f (g (a ^^^ b)) = f (g a) ^^^ f (g b) := by
  intro a b
  rw [hg, hf]

theorem testBit_code (v : Fin 20 → ZMod 2) (i : Nat) :
    (code v).testBit i = if h : i < 20 then decide (v ⟨i, h⟩ = 1) else false :=
  Nat.testBit_ofBits _

theorem code_lt (v : Fin 20 → ZMod 2) : code v < 2 ^ 20 := Nat.ofBits_lt_two_pow _

theorem decide_add_eq_one (a b : ZMod 2) :
    decide (a + b = 1) = (decide (a = 1) ^^ decide (b = 1)) := by
  revert a b
  decide

theorem code_add (u v : Fin 20 → ZMod 2) : code (u + v) = code u ^^^ code v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_code, testBit_code, testBit_code]
  split_ifs with h
  · exact decide_add_eq_one _ _
  · rfl

theorem code_zero : code 0 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_code]
  split_ifs <;> simp

theorem eq_of_decide_eq (a b : ZMod 2) (h : decide (a = 1) = decide (b = 1)) : a = b := by
  revert a b
  decide

theorem code_injective : Function.Injective code := by
  intro u v h
  funext m
  have := congrArg (fun c => Nat.testBit c m.val) h
  simp only [testBit_code, m.isLt, ↓reduceDIte] at this
  exact eq_of_decide_eq _ _ this

theorem exists_code {c : Nat} (hc : c < 2 ^ 20) : ∃ v, code v = c := by
  refine ⟨fun m => if c.testBit m.val then 1 else 0, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_code]
  split_ifs with h1 h2
  · simp [h2]
  · simp [h2]
  · exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hc
      (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

end CFSG.LargeExtraspecial.S14.SMG
