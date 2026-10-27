module

public import CFSG.CGT.T75M23.L2FInputs7
public import CFSG.CGT.T75M23.N7Model
public import CFSG.CGT.T75M23.N7Main

public section

namespace CFSG.CGT.T75M23

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

@[expose] def IsTab7 (X : Table) (x : N7) : Prop := ∃ w : Word6, X = n7Tab w ∧ x = n7 w

theorem IsTab7.ofWord (w : Word6) : IsTab7 (n7Tab w) (n7 w) := ⟨w, rfl, rfl⟩

theorem IsTab7.one : IsTab7 (idT 23) (1 : N7) := ⟨[], rfl, n7_nil.symm⟩

theorem IsTab7.of_word_inv (w : Word6) : IsTab7 (n7Tab (invWord7 w)) (n7 w)⁻¹ :=
  ⟨invWord7 w, rfl, (n7_invWord w).symm⟩

section Tab

theorem IsTab7.mul {X Y : Table} {x y : N7} (hX : IsTab7 X x) (hY : IsTab7 Y y) :
    IsTab7 (compT 23 X Y) (x * y) := by
  obtain ⟨u, rfl, rfl⟩ := hX
  obtain ⟨v, rfl, rfl⟩ := hY
  exact ⟨u ++ v, (n7Tab_append u v).symm, (n7_append u v).symm⟩

theorem IsTab7.eq_iff {X Y : Table} {x y : N7} (hX : IsTab7 X x) (hY : IsTab7 Y y) :
    X = Y ↔ x = y := by
  obtain ⟨u, rfl, rfl⟩ := hX
  obtain ⟨v, rfl, rfl⟩ := hY
  exact n7_eq_iff_tab.symm

theorem IsTab7.conj {X Xi T : Table} {x t : N7} (hX : IsTab7 X x) (hXi : IsTab7 Xi x⁻¹)
    (hT : IsTab7 T t) : IsTab7 (tConj7 X Xi T) (x * t * x⁻¹) :=
  (hX.mul hT).mul hXi

theorem IsTab7.comm_iff {X Y : Table} {x y : N7} (hX : IsTab7 X x) (hY : IsTab7 Y y) :
    commTab7 X Y = true ↔ x * y = y * x := by
  rw [commTab7, beq_iff_eq]
  exact (hX.mul hY).eq_iff (hY.mul hX)

end Tab

@[expose] def n7T : Subgroup N7 := Subgroup.closure (Set.range tGen7)

theorem tw7_zero : tw7 0 = [] := rfl

theorem tw7_two_pow (i : Fin 4) : tw7 (2 ^ i.val) = [(Fin.natAdd 2 i, true)] := by
  fin_cases i <;> rfl

section TT

theorem tw7_mul (h : tCheck7 = true) {k l : ℕ} (hk : k < 16) (hl : l < 16) :
    n7 (tw7 k) * n7 (tw7 l) = n7 (tw7 (k ^^^ l)) := by
  simp only [tCheck7, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [← n7_append]
  exact n7_eq_of_tab_eq (h.1 k hk l hl)

theorem tw7_sq (h : tCheck7 = true) {k : ℕ} (hk : k < 16) : n7 (tw7 k) * n7 (tw7 k) = 1 := by
  rw [tw7_mul h hk hk, Nat.xor_self, tw7_zero, n7_nil]

end TT

theorem n7_tw_mem (k : ℕ) : n7 (tw7 k) ∈ n7T := by
  have key : ∀ l : List (Fin 4),
      n7 (l.flatMap fun i => if k.testBit i.val then [(Fin.natAdd 2 i, true)] else []) ∈ n7T := by
    intro l
    induction l with
    | nil => simp [n7_nil]
    | cons i l ih =>
      rw [List.flatMap_cons, n7_append]
      refine n7T.mul_mem ?_ ih
      by_cases hi : k.testBit i.val
      · simp only [hi, ite_true]
        exact Subgroup.subset_closure ⟨i, by rw [n7_singleton]; rfl⟩
      · simp [hi, n7_nil]
  exact key (List.finRange 4)

section TT2

theorem mem_n7T_iff (h : tCheck7 = true) (x : N7) : x ∈ n7T ↔ ∃ k, k < 16 ∧ x = n7 (tw7 k) := by
  constructor
  · intro hx
    let S : Subgroup N7 :=
      { carrier := {x | ∃ k, k < 16 ∧ x = n7 (tw7 k)}
        one_mem' := ⟨0, by norm_num, by rw [tw7_zero, n7_nil]⟩
        mul_mem' := by
          rintro _ _ ⟨k, hk, rfl⟩ ⟨l, hl, rfl⟩
          exact ⟨k ^^^ l, Nat.xor_lt_two_pow (n := 4) hk hl, (tw7_mul h hk hl)⟩
        inv_mem' := by
          rintro _ ⟨k, hk, rfl⟩
          refine ⟨k, hk, ?_⟩
          exact inv_eq_of_mul_eq_one_right (tw7_sq h hk) }
    have hle : n7T ≤ S := by
      refine (Subgroup.closure_le S).2 ?_
      rintro _ ⟨i, rfl⟩
      refine ⟨2 ^ i.val, ?_, ?_⟩
      · have : 2 ^ i.val < 2 ^ 4 := Nat.pow_lt_pow_right (by norm_num) i.isLt
        simpa using this
      · rw [tw7_two_pow, n7_singleton]
        rfl
    exact hle hx
  · rintro ⟨k, -, rfl⟩
    exact n7_tw_mem k

theorem tTabs7_contains_iff (h : tCheck7 = true) {X : Table} {x : N7} (hX : IsTab7 X x) :
    tTabs7.contains X = true ↔ x ∈ n7T := by
  rw [mem_n7T_iff h, List.contains_iff_mem, tTabs7, List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, List.mem_range.1 hk, (hX.eq_iff (IsTab7.ofWord _)).1 rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, List.mem_range.2 hk, ((IsTab7.ofWord _).eq_iff hX).2 rfl⟩

end TT2

theorem mem_closure_klein_iff7 {K : Type*} [Group K] {p q : K} (hp : p * p = 1) (hq : q * q = 1)
    (hpq : p * q = q * p) (x : K) :
    x ∈ Subgroup.closure ({p, q} : Set K) ↔ x = 1 ∨ x = p ∨ x = q ∨ x = p * q := by
  have e1 : p * (p * q) = q := by rw [← mul_assoc, hp, one_mul]
  have e2 : q * (p * q) = p := by rw [← mul_assoc, ← hpq, mul_assoc, hq, mul_one]
  have e4 : p * q * p = q := by rw [mul_assoc, ← hpq, ← mul_assoc, hp, one_mul]
  have e5 : p * q * q = p := by rw [mul_assoc, hq, mul_one]
  have e6 : p * q * (p * q) = 1 := by rw [mul_assoc, e2, hp]
  constructor
  · intro hx
    let S : Subgroup K :=
      { carrier := {y | y = 1 ∨ y = p ∨ y = q ∨ y = p * q}
        one_mem' := Or.inl rfl
        mul_mem' := by
          rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
            simp [hp, hq, e1, e2, e4, e5, e6, hpq.symm]
        inv_mem' := by
          rintro a (rfl | rfl | rfl | rfl)
          · simp
          · simp [inv_eq_of_mul_eq_one_right hp]
          · simp [inv_eq_of_mul_eq_one_right hq]
          · simp [mul_inv_rev, inv_eq_of_mul_eq_one_right hp, inv_eq_of_mul_eq_one_right hq,
              hpq.symm] }
    have hle : Subgroup.closure ({p, q} : Set K) ≤ S := by
      refine (Subgroup.closure_le S).2 ?_
      rintro y (rfl | rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    exact hle hx
  · have hpm : p ∈ Subgroup.closure ({p, q} : Set K) := Subgroup.subset_closure (by simp)
    have hqm : q ∈ Subgroup.closure ({p, q} : Set K) := Subgroup.subset_closure (by simp)
    rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact hpm
    · exact hqm
    · exact mul_mem hpm hqm

theorem ncard_four7 {K : Type*} {a b c d : K} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : ({a, b, c, d} : Set K).ncard = 4 := by
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hcd]
  · simpa using ⟨hbc, hbd⟩
  · simpa using ⟨hab, hac, had⟩

theorem card_eq_four7 {K : Type*} [Group K] (S : Subgroup K) {a b c d : K}
    (hS : ∀ y ∈ S, y = a ∨ y = b ∨ y = c ∨ y = d) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hd : d ∈ S) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) : Nat.card S = 4 := by
  have hset : (S : Set K) = {a, b, c, d} := by
    ext y
    simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · exact hS y
    · rintro (rfl | rfl | rfl | rfl) <;> assumption
  have h1 : (S : Set K).ncard = 4 := by
    rw [hset]
    exact ncard_four7 hab hac had hbc hbd hcd
  rw [← h1, ← Nat.card_coe_set_eq]
  rfl

theorem contains_four_iff7 {a b c d : Table} {A B C D : N7} {Y : Table} {y : N7}
    (ha : IsTab7 a A) (hb : IsTab7 b B) (hc : IsTab7 c C) (hd : IsTab7 d D) (hY : IsTab7 Y y) :
    [a, b, c, d].contains Y = true ↔ y = A ∨ y = B ∨ y = C ∨ y = D := by
  simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false]
  rw [hY.eq_iff ha, hY.eq_iff hb, hY.eq_iff hc, hY.eq_iff hd]

@[expose] def bm0 : N7 := n7 (bGen7 0)

@[expose] def bm1 : N7 := n7 (bGen7 1)

@[expose] def n7B : Subgroup N7 := Subgroup.closure {bm0, bm1}

theorem isTab7_bt0 : IsTab7 bt0 bm0 := IsTab7.ofWord _

theorem isTab7_bt1 : IsTab7 bt1 bm1 := IsTab7.ofWord _

theorem isTab7_bt01 : IsTab7 bt01 (bm0 * bm1) := ⟨bGen7 0 ++ bGen7 1, rfl, n7_append _ _⟩

section BB

theorem bFacts7 (hb : bCheck7 = true) (ht : tCheck7 = true) :
    bm0 * bm0 = 1 ∧ bm1 * bm1 = 1 ∧ bm0 * bm1 = bm1 * bm0 ∧ bm0 ≠ 1 ∧ bm1 ≠ 1 ∧ bm0 ≠ bm1 ∧
      bm0 * bm1 ≠ 1 ∧ bm0 * bm1 ≠ bm0 ∧ bm0 * bm1 ≠ bm1 ∧ bm0 ∉ n7T := by
  simp only [bCheck7, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hb
  have t0 := isTab7_bt0
  have t1 := isTab7_bt1
  have t01 := isTab7_bt01
  refine ⟨(((t0.mul t0).eq_iff IsTab7.one).1 h1), (((t1.mul t1).eq_iff IsTab7.one).1 h2),
    ((t0.comm_iff t1).1 (by simpa [commTab7] using h3)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact absurd ((t0.eq_iff IsTab7.one).2 h) (by simpa using h4)
  · intro h
    exact absurd ((t1.eq_iff IsTab7.one).2 h) (by simpa using h5)
  · intro h
    exact absurd ((t0.eq_iff t1).2 h) (by simpa using h6)
  · intro h
    exact absurd ((t01.eq_iff IsTab7.one).2 h) (by simpa using h7)
  · intro h
    exact absurd ((t01.eq_iff t0).2 h) (by simpa using h8)
  · intro h
    exact absurd ((t01.eq_iff t1).2 h) (by simpa using h9)
  · intro h
    exact absurd ((tTabs7_contains_iff ht t0).2 h) (by simpa using h10)

theorem mem_n7B_iff (hb : bCheck7 = true) (ht : tCheck7 = true) (x : N7) :
    x ∈ n7B ↔ x = 1 ∨ x = bm0 ∨ x = bm1 ∨ x = bm0 * bm1 := by
  obtain ⟨h1, h2, h3, -⟩ := bFacts7 hb ht
  exact mem_closure_klein_iff7 h1 h2 h3 x

theorem bTabs7_contains_iff (hb : bCheck7 = true) (ht : tCheck7 = true) {X : Table} {x : N7}
    (hX : IsTab7 X x) : bTabs7.contains X = true ↔ x ∈ n7B := by
  rw [mem_n7B_iff hb ht, bTabs7, contains_four_iff7 IsTab7.one isTab7_bt0 isTab7_bt1 isTab7_bt01 hX]

theorem card_n7B (hb : bCheck7 = true) (ht : tCheck7 = true) : Nat.card n7B = 4 := by
  obtain ⟨-, -, -, h4, h5, h6, h7, h8, h9, -⟩ := bFacts7 hb ht
  have hm := mem_n7B_iff hb ht
  exact card_eq_four7 n7B (a := 1) (b := bm0) (c := bm1) (d := bm0 * bm1)
    (fun y hy => (hm y).1 hy) (one_mem _) ((hm _).2 (Or.inr (Or.inl rfl)))
    ((hm _).2 (Or.inr (Or.inr (Or.inl rfl)))) ((hm _).2 (Or.inr (Or.inr (Or.inr rfl))))
    h4.symm h5.symm h7.symm h6 h8.symm h9.symm

end BB

theorem mem_normalizer_klein7 {N : Type*} [Group N] {K : Subgroup N} {p q : N} (hp : p ∈ K)
    (hq : q ∈ K) (hK : ∀ y ∈ K, y = 1 ∨ y = p ∨ y = q ∨ y = p * q) {x : N} :
    x ∈ Subgroup.normalizer (K : Set N) ↔
      x * p * x⁻¹ ∈ K ∧ x * q * x⁻¹ ∈ K ∧ x⁻¹ * p * x ∈ K ∧ x⁻¹ * q * x ∈ K := by
  have key : ∀ z : N, z * p * z⁻¹ ∈ K → z * q * z⁻¹ ∈ K → ∀ y ∈ K, z * y * z⁻¹ ∈ K := by
    intro z h1 h2 y hy
    rcases hK y hy with rfl | rfl | rfl | rfl
    · simp
    · exact h1
    · exact h2
    · have : z * (p * q) * z⁻¹ = (z * p * z⁻¹) * (z * q * z⁻¹) := by group
      rw [this]
      exact K.mul_mem h1 h2
  constructor
  · intro hx
    have hx' : x⁻¹ ∈ Subgroup.normalizer (K : Set N) := (Subgroup.normalizer (K : Set N)).inv_mem hx
    refine ⟨(Subgroup.mem_normalizer_iff.1 hx p).1 hp, (Subgroup.mem_normalizer_iff.1 hx q).1 hq,
      ?_, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.1 hx' p).1 hp
    · simpa using (Subgroup.mem_normalizer_iff.1 hx' q).1 hq
  · rintro ⟨h1, h2, h3, h4⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact key x h1 h2 y
    · intro hy
      have := key x⁻¹ (by simpa using h3) (by simpa using h4) _ hy
      simpa [mul_assoc] using this

section NL

theorem normL7_iff {K : Subgroup N7} {L : List Table} {p q : N7} {P Q : Table} (hP : IsTab7 P p)
    (hQ : IsTab7 Q q) (hp : p ∈ K) (hq : q ∈ K) (hK : ∀ y ∈ K, y = 1 ∨ y = p ∨ y = q ∨ y = p * q)
    (hL : ∀ (Y : Table) (y : N7), IsTab7 Y y → (L.contains Y = true ↔ y ∈ K)) {X Xi : Table}
    {x : N7} (hX : IsTab7 X x) (hXi : IsTab7 Xi x⁻¹) :
    normL7 L P Q X Xi = true ↔ x ∈ Subgroup.normalizer (K : Set N7) := by
  have hX' : IsTab7 X (x⁻¹)⁻¹ := by rwa [inv_inv]
  rw [mem_normalizer_klein7 hp hq hK, normL7]
  simp only [Bool.and_eq_true]
  rw [hL _ _ (IsTab7.conj hX hXi hP), hL _ _ (IsTab7.conj hX hXi hQ),
    hL _ _ (IsTab7.conj hXi hX' hP), hL _ _ (IsTab7.conj hXi hX' hQ)]
  simp only [inv_inv, and_assoc]

theorem normB7_iff (hb : bCheck7 = true) (ht : tCheck7 = true) {X Xi : Table} {x : N7}
    (hX : IsTab7 X x) (hXi : IsTab7 Xi x⁻¹) :
    normB7 X Xi = true ↔ x ∈ Subgroup.normalizer (n7B : Set N7) := by
  have hm := mem_n7B_iff hb ht
  refine normL7_iff isTab7_bt0 isTab7_bt1 ((hm _).2 (Or.inr (Or.inl rfl)))
    ((hm _).2 (Or.inr (Or.inr (Or.inl rfl)))) (fun y hy => (hm y).1 hy) ?_ hX hXi
  intro Y y hY
  exact bTabs7_contains_iff hb ht hY

end NL

end CFSG.CGT.T75M23
