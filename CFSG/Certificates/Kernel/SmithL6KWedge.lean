module

public import CFSG.Certificates.Kernel.SmithL6KMeet

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6
open CFSG.SmithE (tri applyCols)

theorem det3B_xor1 : ∀ a a' b c d d' e f g g' h i : Bool,
    det3B (a ^^ a') b c (d ^^ d') e f (g ^^ g') h i =
      (det3B a b c d e f g h i ^^ det3B a' b c d' e f g' h i) := by decide

theorem det3B_xor2 : ∀ a b b' c d e e' f g h h' i : Bool,
    det3B a (b ^^ b') c d (e ^^ e') f g (h ^^ h') i =
      (det3B a b c d e f g h i ^^ det3B a b' c d e' f g h' i) := by decide

theorem det3B_xor3 : ∀ a b c c' d e f f' g h i i' : Bool,
    det3B a b (c ^^ c') d e (f ^^ f') g h (i ^^ i') =
      (det3B a b c d e f g h i ^^ det3B a b c' d e f' g h i') := by decide

theorem det3B_swap12 : ∀ a b c d e f g h i : Bool,
    det3B b a c e d f h g i = det3B a b c d e f g h i := by decide

theorem det3B_swap23 : ∀ a b c d e f g h i : Bool,
    det3B a c b d f e g i h = det3B a b c d e f g h i := by decide

theorem det3B_self12 : ∀ a c d f g i : Bool, det3B a a c d d f g g i = false := by decide

theorem det3B_self23 : ∀ a b d e g h : Bool, det3B a b b d e e g h h = false := by decide

@[expose] def wbit (a b c t : Nat) : Bool :=
  det3B (a.testBit (tri[t]!).1) (b.testBit (tri[t]!).1) (c.testBit (tri[t]!).1)
    (a.testBit (tri[t]!).2.1) (b.testBit (tri[t]!).2.1) (c.testBit (tri[t]!).2.1)
    (a.testBit (tri[t]!).2.2) (b.testBit (tri[t]!).2.2) (c.testBit (tri[t]!).2.2)

theorem wedge3_eq_foldl (a b c : Nat) : wedge3 a b c =
    (List.range 20).foldl (fun acc t => if wbit a b c t then acc ||| 2 ^ t else acc) 0 := by
  unfold wedge3
  congr 1

theorem wedge3_testBit (a b c x : Nat) :
    (wedge3 a b c).testBit x = (decide (x < 20) && wbit a b c x) := by
  have e := foldl_or_testBit (fun t => t) (wbit a b c) (List.range 20) 0 x
  rw [wedge3_eq_foldl, e]
  apply Bool.eq_iff_iff.mpr
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true, List.mem_range,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨t, ht, hw, rfl⟩
    exact ⟨ht, hw⟩
  · rintro ⟨hx, hw⟩
    exact ⟨x, hx, hw, rfl⟩

theorem wedge3_lt20 (a b c : Nat) : wedge3 a b c < 2 ^ 20 := by
  apply Nat.lt_pow_two_of_testBit
  intro x hx
  rw [wedge3_testBit]
  simp [show ¬ x < 20 by omega]

theorem wedge3_xor1 (a a' b c : Nat) : wedge3 (a ^^^ a') b c = wedge3 a b c ^^^ wedge3 a' b c := by
  apply Nat.eq_of_testBit_eq
  intro x
  rw [Nat.testBit_xor, wedge3_testBit, wedge3_testBit, wedge3_testBit]
  unfold wbit
  simp only [Nat.testBit_xor]
  rw [det3B_xor1]
  cases decide (x < 20) <;> simp

theorem wedge3_xor2 (a b b' c : Nat) : wedge3 a (b ^^^ b') c = wedge3 a b c ^^^ wedge3 a b' c := by
  apply Nat.eq_of_testBit_eq
  intro x
  rw [Nat.testBit_xor, wedge3_testBit, wedge3_testBit, wedge3_testBit]
  unfold wbit
  simp only [Nat.testBit_xor]
  rw [det3B_xor2]
  cases decide (x < 20) <;> simp

theorem wedge3_xor3 (a b c c' : Nat) : wedge3 a b (c ^^^ c') = wedge3 a b c ^^^ wedge3 a b c' := by
  apply Nat.eq_of_testBit_eq
  intro x
  rw [Nat.testBit_xor, wedge3_testBit, wedge3_testBit, wedge3_testBit]
  unfold wbit
  simp only [Nat.testBit_xor]
  rw [det3B_xor3]
  cases decide (x < 20) <;> simp

theorem wedge3_swap12 (a b c : Nat) : wedge3 b a c = wedge3 a b c := by
  apply Nat.eq_of_testBit_eq
  intro x
  rw [wedge3_testBit, wedge3_testBit]
  unfold wbit
  rw [det3B_swap12]

theorem wedge3_swap23 (a b c : Nat) : wedge3 a c b = wedge3 a b c := by
  apply Nat.eq_of_testBit_eq
  intro x
  rw [wedge3_testBit, wedge3_testBit]
  unfold wbit
  rw [det3B_swap23]

theorem wedge3_self12 (a c : Nat) : wedge3 a a c = 0 := by
  apply Nat.eq_of_testBit_eq
  intro x
  rw [wedge3_testBit]
  unfold wbit
  rw [det3B_self12]
  simp

theorem wedge3_self23 (a b : Nat) : wedge3 a b b = 0 := by
  apply Nat.eq_of_testBit_eq
  intro x
  rw [wedge3_testBit]
  unfold wbit
  rw [det3B_self23]
  simp

theorem wedge3_self13 (a b : Nat) : wedge3 a b a = 0 := by
  rw [← wedge3_swap23, wedge3_self12]

theorem applyCols_xorL (cols : Array Nat) (a b : Nat) :
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
      simp only [Bool.true_xor, Bool.false_xor, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, ↓reduceIte] <;>
      (apply Nat.eq_of_testBit_eq
       intro i
       simp only [Nat.testBit_xor]
       cases x.testBit i <;> cases y.testBit i <;> cases (cols[m]!).testBit i <;> rfl)

theorem applyCols_powL (cols : Array Nat) {m : Nat} (hm : m < cols.size) :
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

theorem applyCols_zeroL (cols : Array Nat) : applyCols cols 0 = 0 := by
  have h := applyCols_xorL cols 0 0
  rw [Nat.xor_self] at h
  rw [h, Nat.xor_self]

theorem split_top_bit {c n : Nat} (hc : c < 2 ^ (n + 1)) :
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
        (Nat.pow_le_pow_right (by decide) (by omega)))
      split_ifs <;> simp [hi, this, Ne.symm hin]

theorem xorAdd_ext {F G : Nat → Nat} (hF : ∀ a b, F (a ^^^ b) = F a ^^^ F b)
    (hG : ∀ a b, G (a ^^^ b) = G a ^^^ G b) (n : Nat) (h : ∀ m < n, F (2 ^ m) = G (2 ^ m)) :
    ∀ c < 2 ^ n, F c = G c := by
  have hF0 : F 0 = 0 := by
    have := hF 0 0
    rw [Nat.xor_self] at this
    rw [this, Nat.xor_self]
  have hG0 : G 0 = 0 := by
    have := hG 0 0
    rw [Nat.xor_self] at this
    rw [this, Nat.xor_self]
  induction n with
  | zero =>
    intro c hc
    have : c = 0 := by simpa using hc
    rw [this, hF0, hG0]
  | succ n ih =>
    intro c hc
    rw [split_top_bit hc, hF, hG, ih (fun m hm => h m (by omega)) _ (Nat.mod_lt _ (Nat.two_pow_pos n))]
    congr 1
    split_ifs
    · exact h n (by omega)
    · rw [hF0, hG0]

@[expose] def perm3 (i j l : Nat) (p : Nat × Nat × Nat) : Prop :=
  (i = p.1 ∧ j = p.2.1 ∧ l = p.2.2) ∨ (j = p.1 ∧ i = p.2.1 ∧ l = p.2.2) ∨
    (i = p.1 ∧ l = p.2.1 ∧ j = p.2.2) ∨ (l = p.1 ∧ j = p.2.1 ∧ i = p.2.2) ∨
    (j = p.1 ∧ l = p.2.1 ∧ i = p.2.2) ∨ (l = p.1 ∧ i = p.2.1 ∧ j = p.2.2)

instance (i j l : Nat) (p : Nat × Nat × Nat) : Decidable (perm3 i j l p) := by
  unfold perm3
  infer_instance

theorem wedge3_basis : ∀ i < 6, ∀ j < 6, ∀ l < 6,
    (wedge3 (2 ^ i) (2 ^ j) (2 ^ l) = 0 ∧ (i = j ∨ j = l ∨ i = l)) ∨
      ∃ t < 20, wedge3 (2 ^ i) (2 ^ j) (2 ^ l) = 2 ^ t ∧ perm3 i j l tri[t]! := by
  decide

theorem wedge3_perm3 {f : Nat → Nat} {i j l : Nat} {p : Nat × Nat × Nat} (h : perm3 i j l p) :
    wedge3 (f (2 ^ i)) (f (2 ^ j)) (f (2 ^ l)) =
      wedge3 (f (2 ^ p.1)) (f (2 ^ p.2.1)) (f (2 ^ p.2.2)) := by
  obtain ⟨r0, r1, r2⟩ := p
  rcases h with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
      ⟨h0, h1, h2⟩ <;> dsimp only at h0 h1 h2 <;> subst h0 h1 h2
  · rfl
  · rw [wedge3_swap12]
  · rw [wedge3_swap23]
  · rw [wedge3_swap12, wedge3_swap23, wedge3_swap12]
  · rw [wedge3_swap12, wedge3_swap23]
  · rw [wedge3_swap23, wedge3_swap12]

theorem wedge3_map {f : Nat → Nat} (hf : ∀ x y, f (x ^^^ y) = f x ^^^ f y) {C : Array Nat}
    (hC : C.size = 20)
    (hCt : ∀ t < 20, C[t]! = wedge3 (f (2 ^ (tri[t]!).1)) (f (2 ^ (tri[t]!).2.1))
      (f (2 ^ (tri[t]!).2.2)))
    {a b c : Nat} (ha : a < 64) (hb : b < 64) (hc : c < 64) :
    applyCols C (wedge3 a b c) = wedge3 (f a) (f b) (f c) := by
  have h64 : (64 : Nat) = 2 ^ 6 := rfl
  have hbase : ∀ i < 6, ∀ j < 6, ∀ l < 6, applyCols C (wedge3 (2 ^ i) (2 ^ j) (2 ^ l)) =
      wedge3 (f (2 ^ i)) (f (2 ^ j)) (f (2 ^ l)) := by
    intro i hi j hj l hl
    rcases wedge3_basis i hi j hj l hl with ⟨h0, hr⟩ | ⟨t, ht, hw, hp⟩
    · rw [h0, applyCols_zeroL]
      rcases hr with e | e | e <;> subst e
      · rw [wedge3_self12]
      · rw [wedge3_self23]
      · rw [wedge3_self13]
    · rw [hw, applyCols_powL C (by omega), hCt t ht, wedge3_perm3 hp]
  have h3 : ∀ i < 6, ∀ j < 6, ∀ z < 64, applyCols C (wedge3 (2 ^ i) (2 ^ j) z) =
      wedge3 (f (2 ^ i)) (f (2 ^ j)) (f z) := by
    intro i hi j hj z hz
    refine xorAdd_ext (F := fun z => applyCols C (wedge3 (2 ^ i) (2 ^ j) z))
      (G := fun z => wedge3 (f (2 ^ i)) (f (2 ^ j)) (f z)) ?_ ?_ 6
      (fun l hl => hbase i hi j hj l hl) z (h64 ▸ hz)
    · intro x y
      simp only [wedge3_xor3, applyCols_xorL]
    · intro x y
      simp only [hf, wedge3_xor3]
  have h2 : ∀ i < 6, ∀ y < 64, ∀ z < 64, applyCols C (wedge3 (2 ^ i) y z) =
      wedge3 (f (2 ^ i)) (f y) (f z) := by
    intro i hi y hy z hz
    refine xorAdd_ext (F := fun y => applyCols C (wedge3 (2 ^ i) y z))
      (G := fun y => wedge3 (f (2 ^ i)) (f y) (f z)) ?_ ?_ 6
      (fun j hj => h3 i hi j hj z hz) y (h64 ▸ hy)
    · intro x y
      simp only [wedge3_xor2, applyCols_xorL]
    · intro x y
      simp only [hf, wedge3_xor2]
  refine xorAdd_ext (F := fun x => applyCols C (wedge3 x b c))
    (G := fun x => wedge3 (f x) (f b) (f c)) ?_ ?_ 6 (fun i hi => h2 i hi b hb c hc) a (h64 ▸ ha)
  · intro x y
    simp only [wedge3_xor1, applyCols_xorL]
  · intro x y
    simp only [hf, wedge3_xor1]

theorem tvApply_xor (k x y : Nat) : tvApply k (x ^^^ y) = tvApply k x ^^^ tvApply k y := by
  unfold tvApply
  generalize tvPair k = p
  obtain ⟨v, φ⟩ := p
  simp only
  rw [form_xor_right]
  cases form φ x <;> cases form φ y <;>
    simp only [Bool.true_xor, Bool.false_xor, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      ↓reduceIte] <;>
    (apply Nat.eq_of_testBit_eq
     intro i
     simp only [Nat.testBit_xor]
     cases x.testBit i <;> cases y.testBit i <;> cases v.testBit i <;> rfl)

theorem tvCols_size (k : Nat) : (tvCols k).size = 20 := by
  unfold tvCols
  rw [Array.size_ofFn]

theorem tvCols_get {k t : Nat} (ht : t < 20) : (tvCols k)[t]! =
    wedge3 (tvApply k (2 ^ (tri[t]!).1)) (tvApply k (2 ^ (tri[t]!).2.1))
      (tvApply k (2 ^ (tri[t]!).2.2)) := by
  unfold tvCols
  rw [getElem!_pos _ t (by rw [Array.size_ofFn]; exact ht), Array.getElem_ofFn]

theorem tvCols_wedge3 (k : Nat) {a b c : Nat} (ha : a < 64) (hb : b < 64) (hc : c < 64) :
    applyCols (tvCols k) (wedge3 a b c) = wedge3 (tvApply k a) (tvApply k b) (tvApply k c) :=
  wedge3_map (tvApply_xor k) (tvCols_size k) (fun _ ht => tvCols_get ht) ha hb hc

theorem tvApply_lt {k x : Nat} (hk : k < 1953) (hx : x < 64) : tvApply k x < 64 := by
  have hp := tvP_tvPair hk
  unfold tvApply
  revert hp
  generalize tvPair k = p
  intro hp
  obtain ⟨v, φ⟩ := p
  simp only
  split
  · exact xor_lt64 hx hp.1
  · exact hx

theorem tvApply_tvApply {k : Nat} (hk : k < 1953) (x : Nat) : tvApply k (tvApply k x) = x := by
  have hp := tvP_tvPair hk
  unfold tvApply
  revert hp
  generalize tvPair k = p
  intro hp
  obtain ⟨v, φ⟩ := p
  have hφv : form φ v = false := hp.2.2.2.2
  simp only
  cases hx : form φ x
  · simp [hx]
  · simp only [↓reduceIte]
    rw [form_xor_right, hx, hφv]
    simp [Nat.xor_assoc]

theorem pow_lt64 {r : Nat} (h : r < 6) : 2 ^ r < 64 :=
  calc 2 ^ r < 2 ^ 6 := Nat.pow_lt_pow_right (by decide) h
    _ = 64 := rfl

theorem tri_lt6 : ∀ m < 20, (tri[m]!).1 < 6 ∧ (tri[m]!).2.1 < 6 ∧ (tri[m]!).2.2 < 6 := by decide

theorem wedge3_tri : ∀ m < 20,
    wedge3 (2 ^ (tri[m]!).1) (2 ^ (tri[m]!).2.1) (2 ^ (tri[m]!).2.2) = 2 ^ m := by decide

theorem tvArr_get {k : Nat} (hk : k < 1953) : tvArr[k]! = tvCols k := by
  unfold tvArr
  rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn]

theorem chkTvInv_holds : chkTvInv = true := by
  unfold chkTvInv
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  intro k hk
  rw [tvArr_get hk]
  refine ⟨tvCols_size k, fun m hm => ⟨?_, ?_⟩⟩
  · rw [tvCols_get hm]
    exact wedge3_lt20 _ _ _
  · obtain ⟨h0, h1, h2⟩ := tri_lt6 m hm
    rw [tvCols_get hm, tvCols_wedge3 k (tvApply_lt hk (pow_lt64 h0)) (tvApply_lt hk (pow_lt64 h1))
      (tvApply_lt hk (pow_lt64 h2)), tvApply_tvApply hk, tvApply_tvApply hk, tvApply_tvApply hk,
      wedge3_tri m hm]

end CFSG.SmithL6.K
