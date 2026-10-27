module

public import CFSG.CGT.T75JM.L2FInputs
public import CFSG.CGT.T75JM.N0Model

public section

namespace CFSG.CGT.T75JM

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

@[expose] def IsTab (X : Table) (x : N0) : Prop := ∃ w : W6, X = n0Tab w ∧ x = n0 w

theorem IsTab.ofWord (w : W6) : IsTab (n0Tab w) (n0 w) := ⟨w, rfl, rfl⟩

theorem IsTab.one : IsTab (idT 22) (1 : N0) := ⟨[], rfl, n0_nil.symm⟩

theorem IsTab.of_word_inv (w : W6) : IsTab (n0Tab (invWord w)) (n0 w)⁻¹ :=
  ⟨invWord w, rfl, (n0_invWord w).symm⟩

section Tab

theorem IsTab.mul {X Y : Table} {x y : N0} (hX : IsTab X x) (hY : IsTab Y y) :
    IsTab (compT 22 X Y) (x * y) := by
  obtain ⟨u, rfl, rfl⟩ := hX
  obtain ⟨v, rfl, rfl⟩ := hY
  exact ⟨u ++ v, (n0Tab_append u v).symm, (n0_append u v).symm⟩

theorem IsTab.eq_iff {X Y : Table} {x y : N0} (hX : IsTab X x) (hY : IsTab Y y) :
    X = Y ↔ x = y := by
  obtain ⟨u, rfl, rfl⟩ := hX
  obtain ⟨v, rfl, rfl⟩ := hY
  exact n0_eq_iff_tab.symm

theorem IsTab.conj {X Xi T : Table} {x t : N0} (hX : IsTab X x) (hXi : IsTab Xi x⁻¹)
    (hT : IsTab T t) : IsTab (tConj X Xi T) (x * t * x⁻¹) :=
  (hX.mul hT).mul hXi

theorem IsTab.comm_iff {X Y : Table} {x y : N0} (hX : IsTab X x) (hY : IsTab Y y) :
    commTab X Y = true ↔ x * y = y * x := by
  rw [commTab, beq_iff_eq]
  exact (hX.mul hY).eq_iff (hY.mul hX)

end Tab

theorem isTab_surj (x : N0) : ∃ w : W6, x = n0 w := n0_surj x

@[expose] def n0T : Subgroup N0 := Subgroup.closure (Set.range tGen)

theorem tw_zero : tw 0 = [] := rfl

theorem tw_two_pow (i : Fin 4) : tw (2 ^ i.val) = [(Fin.natAdd 2 i, true)] := by
  fin_cases i <;> rfl

section TT

theorem tw_mul (h : tCheck = true) {k l : ℕ} (hk : k < 16) (hl : l < 16) :
    n0 (tw k) * n0 (tw l) = n0 (tw (k ^^^ l)) := by
  simp only [tCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [← n0_append]
  exact n0_eq_of_tab_eq (h.1 k hk l hl)

theorem tw_sq (h : tCheck = true) {k : ℕ} (hk : k < 16) : n0 (tw k) * n0 (tw k) = 1 := by
  rw [tw_mul h hk hk, Nat.xor_self, tw_zero, n0_nil]

end TT

theorem n0_tw_mem (k : ℕ) : n0 (tw k) ∈ n0T := by
  have key : ∀ l : List (Fin 4),
      n0 (l.flatMap fun i => if k.testBit i.val then [(Fin.natAdd 2 i, true)] else []) ∈ n0T := by
    intro l
    induction l with
    | nil => simp [n0_nil]
    | cons i l ih =>
      rw [List.flatMap_cons, n0_append]
      refine n0T.mul_mem ?_ ih
      by_cases hi : k.testBit i.val
      · simp only [hi, ite_true]
        exact Subgroup.subset_closure ⟨i, by rw [n0_singleton]; rfl⟩
      · simp [hi, n0_nil]
  exact key (List.finRange 4)

section TT2

theorem mem_n0T_iff (h : tCheck = true) (x : N0) : x ∈ n0T ↔ ∃ k, k < 16 ∧ x = n0 (tw k) := by
  constructor
  · intro hx
    let S : Subgroup N0 :=
      { carrier := {x | ∃ k, k < 16 ∧ x = n0 (tw k)}
        one_mem' := ⟨0, by norm_num, by rw [tw_zero, n0_nil]⟩
        mul_mem' := by
          rintro _ _ ⟨k, hk, rfl⟩ ⟨l, hl, rfl⟩
          exact ⟨k ^^^ l, Nat.xor_lt_two_pow (n := 4) hk hl, (tw_mul h hk hl)⟩
        inv_mem' := by
          rintro _ ⟨k, hk, rfl⟩
          refine ⟨k, hk, ?_⟩
          exact inv_eq_of_mul_eq_one_right (tw_sq h hk) }
    have hle : n0T ≤ S := by
      refine (Subgroup.closure_le S).2 ?_
      rintro _ ⟨i, rfl⟩
      refine ⟨2 ^ i.val, ?_, ?_⟩
      · have : 2 ^ i.val < 2 ^ 4 := Nat.pow_lt_pow_right (by norm_num) i.isLt
        simpa using this
      · rw [tw_two_pow, n0_singleton]
        rfl
    exact hle hx
  · rintro ⟨k, -, rfl⟩
    exact n0_tw_mem k

theorem tTabs_contains_iff (h : tCheck = true) {X : Table} {x : N0} (hX : IsTab X x) :
    tTabs.contains X = true ↔ x ∈ n0T := by
  rw [mem_n0T_iff h, List.contains_iff_mem, tTabs, List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, List.mem_range.1 hk, (hX.eq_iff (IsTab.ofWord _)).1 rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, List.mem_range.2 hk, ((IsTab.ofWord _).eq_iff hX).2 rfl⟩

end TT2

theorem mem_closure_klein_iff {K : Type*} [Group K] {p q : K} (hp : p * p = 1) (hq : q * q = 1)
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

theorem ncard_four {K : Type*} {a b c d : K} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : ({a, b, c, d} : Set K).ncard = 4 := by
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hcd]
  · simpa using ⟨hbc, hbd⟩
  · simpa using ⟨hab, hac, had⟩

theorem card_eq_four {K : Type*} [Group K] (S : Subgroup K) {a b c d : K}
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
    exact ncard_four hab hac had hbc hbd hcd
  rw [← h1, ← Nat.card_coe_set_eq]
  rfl

theorem contains_four_iff {a b c d : Table} {A B C D : N0} {Y : Table} {y : N0}
    (ha : IsTab a A) (hb : IsTab b B) (hc : IsTab c C) (hd : IsTab d D) (hY : IsTab Y y) :
    [a, b, c, d].contains Y = true ↔ y = A ∨ y = B ∨ y = C ∨ y = D := by
  simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false]
  rw [hY.eq_iff ha, hY.eq_iff hb, hY.eq_iff hc, hY.eq_iff hd]

@[expose] def bb0 : N0 := n0 (bGen 0)

@[expose] def bb1 : N0 := n0 (bGen 1)

@[expose] def n0B : Subgroup N0 := Subgroup.closure {bb0, bb1}

theorem isTab_tb0 : IsTab tb0 bb0 := IsTab.ofWord _

theorem isTab_tb1 : IsTab tb1 bb1 := IsTab.ofWord _

theorem isTab_tb01 : IsTab tb01 (bb0 * bb1) := ⟨bGen 0 ++ bGen 1, rfl, n0_append _ _⟩

section BB

theorem bFacts (hb : bCheck = true) (ht : tCheck = true) :
    bb0 * bb0 = 1 ∧ bb1 * bb1 = 1 ∧ bb0 * bb1 = bb1 * bb0 ∧ bb0 ≠ 1 ∧ bb1 ≠ 1 ∧ bb0 ≠ bb1 ∧
      bb0 * bb1 ≠ 1 ∧ bb0 * bb1 ≠ bb0 ∧ bb0 * bb1 ≠ bb1 ∧ bb0 ∉ n0T := by
  simp only [bCheck, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hb
  have t0 := isTab_tb0
  have t1 := isTab_tb1
  have t01 := isTab_tb01
  refine ⟨(((t0.mul t0).eq_iff IsTab.one).1 h1), (((t1.mul t1).eq_iff IsTab.one).1 h2),
    ((t0.comm_iff t1).1 (by simpa [commTab] using h3)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact absurd ((t0.eq_iff IsTab.one).2 h) (by simpa using h4)
  · intro h
    exact absurd ((t1.eq_iff IsTab.one).2 h) (by simpa using h5)
  · intro h
    exact absurd ((t0.eq_iff t1).2 h) (by simpa using h6)
  · intro h
    exact absurd ((t01.eq_iff IsTab.one).2 h) (by simpa using h7)
  · intro h
    exact absurd ((t01.eq_iff t0).2 h) (by simpa using h8)
  · intro h
    exact absurd ((t01.eq_iff t1).2 h) (by simpa using h9)
  · intro h
    exact absurd ((tTabs_contains_iff ht t0).2 h) (by simpa using h10)

theorem mem_n0B_iff (hb : bCheck = true) (ht : tCheck = true) (x : N0) :
    x ∈ n0B ↔ x = 1 ∨ x = bb0 ∨ x = bb1 ∨ x = bb0 * bb1 := by
  obtain ⟨h1, h2, h3, -⟩ := bFacts hb ht
  exact mem_closure_klein_iff h1 h2 h3 x

theorem bTabs_contains_iff (hb : bCheck = true) (ht : tCheck = true) {X : Table} {x : N0}
    (hX : IsTab X x) : bTabs.contains X = true ↔ x ∈ n0B := by
  rw [mem_n0B_iff hb ht, bTabs, contains_four_iff IsTab.one isTab_tb0 isTab_tb1 isTab_tb01 hX]

theorem card_n0B (hb : bCheck = true) (ht : tCheck = true) : Nat.card n0B = 4 := by
  obtain ⟨-, -, -, h4, h5, h6, h7, h8, h9, -⟩ := bFacts hb ht
  have hm := mem_n0B_iff hb ht
  exact card_eq_four n0B (a := 1) (b := bb0) (c := bb1) (d := bb0 * bb1)
    (fun y hy => (hm y).1 hy) (one_mem _) ((hm _).2 (Or.inr (Or.inl rfl)))
    ((hm _).2 (Or.inr (Or.inr (Or.inl rfl)))) ((hm _).2 (Or.inr (Or.inr (Or.inr rfl))))
    h4.symm h5.symm h7.symm h6 h8.symm h9.symm

end BB

theorem mem_normalizer_klein {N : Type*} [Group N] {K : Subgroup N} {p q : N} (hp : p ∈ K)
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

theorem normL_iff {K : Subgroup N0} {L : List Table} {p q : N0} {P Q : Table} (hP : IsTab P p)
    (hQ : IsTab Q q) (hp : p ∈ K) (hq : q ∈ K) (hK : ∀ y ∈ K, y = 1 ∨ y = p ∨ y = q ∨ y = p * q)
    (hL : ∀ (Y : Table) (y : N0), IsTab Y y → (L.contains Y = true ↔ y ∈ K)) {X Xi : Table}
    {x : N0} (hX : IsTab X x) (hXi : IsTab Xi x⁻¹) :
    normL L P Q X Xi = true ↔ x ∈ Subgroup.normalizer (K : Set N0) := by
  have hX' : IsTab X (x⁻¹)⁻¹ := by rwa [inv_inv]
  rw [mem_normalizer_klein hp hq hK, normL]
  simp only [Bool.and_eq_true]
  rw [hL _ _ (IsTab.conj hX hXi hP), hL _ _ (IsTab.conj hX hXi hQ),
    hL _ _ (IsTab.conj hXi hX' hP), hL _ _ (IsTab.conj hXi hX' hQ)]
  simp only [inv_inv, and_assoc]

theorem normB_iff (hb : bCheck = true) (ht : tCheck = true) {X Xi : Table} {x : N0}
    (hX : IsTab X x) (hXi : IsTab Xi x⁻¹) :
    normB X Xi = true ↔ x ∈ Subgroup.normalizer (n0B : Set N0) := by
  have hm := mem_n0B_iff hb ht
  refine normL_iff isTab_tb0 isTab_tb1 ((hm _).2 (Or.inr (Or.inl rfl)))
    ((hm _).2 (Or.inr (Or.inr (Or.inl rfl)))) (fun y hy => (hm y).1 hy) ?_ hX hXi
  intro Y y hY
  exact bTabs_contains_iff hb ht hY

end NL

end CFSG.CGT.T75JM
