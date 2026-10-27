module

public import CFSG.HardMathSupport.U4FF.ClassDigits

public section

namespace CFSG.HardMathSupport.U4FF

namespace Lbl

variable {n : ℕ}

noncomputable instance instFintypeLbl (n : ℕ) : Fintype (Lbl n) :=
  Fintype.ofEquiv ((Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool))
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2⟩
      invFun := fun l => (l.a, l.b, l.c)
      left_inv := fun x => rfl
      right_inv := fun l => rfl }

private theorem fiber_modEq_cases {x y N : ℕ} (hx : x ≤ N) (hy : y ≤ N)
    (h : x ≡ y [MOD N]) : x = y ∨ (x = 0 ∧ y = N) ∨ (x = N ∧ y = 0) := by
  have h' : x % N = y % N := h
  rcases Nat.lt_or_ge x N with hxN | hxN <;> rcases Nat.lt_or_ge y N with hyN | hyN
  · left
    rw [Nat.mod_eq_of_lt hxN, Nat.mod_eq_of_lt hyN] at h'
    exact h'
  · right; left
    have hy' : y = N := le_antisymm hy hyN
    rw [hy', Nat.mod_self, Nat.mod_eq_of_lt hxN] at h'
    exact ⟨h', hy'⟩
  · right; right
    have hx' : x = N := le_antisymm hx hxN
    rw [hx', Nat.mod_self, Nat.mod_eq_of_lt hyN] at h'
    exact ⟨hx', h'.symm⟩
  · left
    omega

private theorem fiber_e1_le (l : Lbl n) : l.e1 ≤ 2 ^ (2 * n) - 1 := by
  have := l.e1_lt
  omega

private theorem fiber_e2_le (l : Lbl n) : l.e2 ≤ 2 ^ n - 1 := by
  have := l.e2_lt
  omega

private theorem fiber_e1_orient {l l' : Lbl n} (hne : l.e1 ≠ l'.e1)
    (h1 : l.e1 ≡ l'.e1 [MOD 2 ^ (2 * n) - 1]) :
    ((∀ i, l.a i = false ∧ l.c i = false) ∧ (∀ i, l'.a i = true ∧ l'.c i = true)) ∨
      ((∀ i, l.a i = true ∧ l.c i = true) ∧ (∀ i, l'.a i = false ∧ l'.c i = false)) := by
  rcases fiber_modEq_cases (fiber_e1_le l) (fiber_e1_le l') h1 with h | ⟨h0, ht⟩ | ⟨ht, h0⟩
  · exact absurd h hne
  · exact Or.inl ⟨(e1_eq_zero_iff l).mp h0, (e1_eq_top_iff l').mp ht⟩
  · exact Or.inr ⟨(e1_eq_top_iff l).mp ht, (e1_eq_zero_iff l').mp h0⟩

private theorem fiber_e2_orient {l l' : Lbl n} (hne : l.e2 ≠ l'.e2)
    (h2 : l.e2 ≡ l'.e2 [MOD 2 ^ n - 1]) :
    ((∀ i, l.b i = false) ∧ (∀ i, l'.b i = true)) ∨
      ((∀ i, l.b i = true) ∧ (∀ i, l'.b i = false)) := by
  rcases fiber_modEq_cases (fiber_e2_le l) (fiber_e2_le l') h2 with h | ⟨h0, ht⟩ | ⟨ht, h0⟩
  · exact absurd h hne
  · exact Or.inl ⟨(e2_eq_zero_iff l).mp h0, (e2_eq_top_iff l').mp ht⟩
  · exact Or.inr ⟨(e2_eq_top_iff l).mp ht, (e2_eq_zero_iff l').mp h0⟩

private theorem fiber_ac_eq {l l' : Lbl n} (h1 : l.e1 = l'.e1) (i : Fin n) :
    l.a i = l'.a i ∧ l.c i = l'.c i := by
  have hA : l.setA = l'.setA :=
    digits_eq_of_sum_eq (by rw [← e1_eq_sum_setA l, ← e1_eq_sum_setA l']; exact h1)
  have key : ∀ j, j < 2 * n → l.digA j = l'.digA j := by
    intro j hj
    have hmem : j ∈ l.setA ↔ j ∈ l'.setA := by rw [hA]
    rw [mem_setA, mem_setA] at hmem
    rw [Bool.eq_iff_iff]
    exact ⟨fun h => (hmem.mp ⟨hj, h⟩).2, fun h => (hmem.mpr ⟨hj, h⟩).2⟩
  have ha := key i (by have := i.isLt; omega)
  have hc := key (n + i) (by have := i.isLt; omega)
  rw [digA_fin, digA_fin] at ha
  rw [digA_fin_hi, digA_fin_hi] at hc
  exact ⟨ha, hc⟩

private theorem fiber_b_eq {l l' : Lbl n} (h2 : l.e2 = l'.e2) (i : Fin n) :
    l.b i = l'.b i := by
  have hB : l.setB = l'.setB :=
    digits_eq_of_sum_eq (by rw [← e2_eq_sum_setB l, ← e2_eq_sum_setB l']; exact h2)
  have hmem : (i : ℕ) ∈ l.setB ↔ (i : ℕ) ∈ l'.setB := by rw [hB]
  rw [mem_setB, mem_setB] at hmem
  have hi : (i : ℕ) < n := i.isLt
  have key : l.digB i = l'.digB i := by
    rw [Bool.eq_iff_iff]
    exact ⟨fun h => (hmem.mp ⟨hi, h⟩).2, fun h => (hmem.mpr ⟨hi, h⟩).2⟩
  rwa [digB_fin, digB_fin] at key

private theorem fiber_locM_B : ∀ x z : Bool, locM x false z < locM x true z := by
  decide

private theorem fiber_locM_A : ∀ y : Bool, locM false y false < locM true y true := by
  decide

private theorem fiber_locM_AB : locM false false false < locM true true true := by
  decide

private theorem fiber_locM_AB' : locM false true false < locM true false true := by
  decide

private theorem fiber_locM_one : ∀ x y z : Bool, 1 ≤ locM x y z := by
  decide

private theorem fiber_mul_lt_mul {x y P Q : ℕ} (hxy : x < y) (hP : P ≤ Q) (hP1 : 1 ≤ P) :
    x * P < y * Q :=
  lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hxy (by omega)) (Nat.mul_le_mul_left y hP)

private theorem fiber_dim_lt {l l' : Lbl n} (hn : 1 ≤ n)
    (h : ∀ i, locM (l.a i) (l.b i) (l.c i) < locM (l'.a i) (l'.b i) (l'.c i)) :
    l.dim < l'.dim := by
  have i₀ : Fin n := ⟨0, by omega⟩
  unfold Lbl.dim
  rw [← Finset.mul_prod_erase Finset.univ (fun i => locM (l.a i) (l.b i) (l.c i))
      (Finset.mem_univ i₀),
    ← Finset.mul_prod_erase Finset.univ (fun i => locM (l'.a i) (l'.b i) (l'.c i))
      (Finset.mem_univ i₀)]
  have hP : ∏ i ∈ Finset.univ.erase i₀, locM (l.a i) (l.b i) (l.c i) ≤
      ∏ i ∈ Finset.univ.erase i₀, locM (l'.a i) (l'.b i) (l'.c i) :=
    Finset.prod_le_prod (fun i _ => (h i).le)
  have hP1 : 1 ≤ ∏ i ∈ Finset.univ.erase i₀, locM (l.a i) (l.b i) (l.c i) := by
    have h1 : ∏ _i ∈ Finset.univ.erase i₀, (1 : ℕ) ≤
        ∏ i ∈ Finset.univ.erase i₀, locM (l.a i) (l.b i) (l.c i) :=
      Finset.prod_le_prod (fun i _ => fiber_locM_one _ _ _)
    rwa [Finset.prod_const_one] at h1
  exact fiber_mul_lt_mul (h i₀) hP hP1

theorem dim_ne_of_fiber (hn : 1 ≤ n) {l l' : Lbl n} (hne : l ≠ l')
    (h1 : l.e1 ≡ l'.e1 [MOD 2 ^ (2 * n) - 1]) (h2 : l.e2 ≡ l'.e2 [MOD 2 ^ n - 1]) :
    l.dim ≠ l'.dim := by
  by_cases P1 : l.e1 = l'.e1 <;> by_cases P2 : l.e2 = l'.e2
  · exact absurd (ext_of_e P1 P2) hne
  ·
    have hac := fiber_ac_eq P1
    rcases fiber_e2_orient P2 h2 with ⟨hb, hb'⟩ | ⟨hb, hb'⟩
    · have hlt : l.dim < l'.dim := fiber_dim_lt hn (fun i => by
        rw [← (hac i).1, ← (hac i).2, hb i, hb' i]
        exact fiber_locM_B _ _)
      exact hlt.ne
    · have hlt : l'.dim < l.dim := fiber_dim_lt hn (fun i => by
        rw [← (hac i).1, ← (hac i).2, hb i, hb' i]
        exact fiber_locM_B _ _)
      exact hlt.ne'
  ·
    have hb := fiber_b_eq P2
    rcases fiber_e1_orient P1 h1 with ⟨hA, hA'⟩ | ⟨hA, hA'⟩
    · have hlt : l.dim < l'.dim := fiber_dim_lt hn (fun i => by
        rw [(hA i).1, (hA i).2, (hA' i).1, (hA' i).2, ← hb i]
        exact fiber_locM_A _)
      exact hlt.ne
    · have hlt : l'.dim < l.dim := fiber_dim_lt hn (fun i => by
        rw [(hA' i).1, (hA' i).2, (hA i).1, (hA i).2, hb i]
        exact fiber_locM_A _)
      exact hlt.ne'
  ·
    rcases fiber_e1_orient P1 h1 with ⟨hA, hA'⟩ | ⟨hA, hA'⟩ <;>
      rcases fiber_e2_orient P2 h2 with ⟨hB, hB'⟩ | ⟨hB, hB'⟩
    · have hlt : l.dim < l'.dim := fiber_dim_lt hn (fun i => by
        rw [(hA i).1, (hA i).2, hB i, (hA' i).1, (hA' i).2, hB' i]
        exact fiber_locM_AB)
      exact hlt.ne
    · have hlt : l.dim < l'.dim := fiber_dim_lt hn (fun i => by
        rw [(hA i).1, (hA i).2, hB i, (hA' i).1, (hA' i).2, hB' i]
        exact fiber_locM_AB')
      exact hlt.ne
    · have hlt : l'.dim < l.dim := fiber_dim_lt hn (fun i => by
        rw [(hA' i).1, (hA' i).2, hB' i, (hA i).1, (hA i).2, hB i]
        exact fiber_locM_AB')
      exact hlt.ne'
    · have hlt : l'.dim < l.dim := fiber_dim_lt hn (fun i => by
        rw [(hA' i).1, (hA' i).2, hB' i, (hA i).1, (hA i).2, hB i]
        exact fiber_locM_AB)
      exact hlt.ne'

private theorem fiber_card_filter (N M a : ℕ) (hN : 1 ≤ N) (hM : M = N + 1) :
    ((Finset.range M).filter (fun x => x ≡ a [MOD N])).card = if N ∣ a then 2 else 1 := by
  subst hM
  split_ifs with hd
  · have ha0 : a % N = 0 := Nat.mod_eq_zero_of_dvd hd
    have hset : (Finset.range (N + 1)).filter (fun x => x ≡ a [MOD N]) = {0, N} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hx, hxa⟩
        have hxa' : x % N = a % N := hxa
        rw [ha0] at hxa'
        rcases Nat.lt_or_ge x N with h | h
        · left
          rw [Nat.mod_eq_of_lt h] at hxa'
          exact hxa'
        · right
          omega
      · rintro (h | h)
        · rw [h]
          refine ⟨by omega, ?_⟩
          show 0 % N = a % N
          rw [ha0, Nat.zero_mod]
        · rw [h]
          refine ⟨by omega, ?_⟩
          show N % N = a % N
          rw [ha0, Nat.mod_self]
    rw [hset, Finset.card_pair (show (0 : ℕ) ≠ N by omega)]
  · have hset : (Finset.range (N + 1)).filter (fun x => x ≡ a [MOD N]) = {a % N} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hx, hxa⟩
        have hxa' : x % N = a % N := hxa
        rcases Nat.lt_or_ge x N with h | h
        · rw [Nat.mod_eq_of_lt h] at hxa'
          exact hxa'
        · exfalso
          have hxN : x = N := by omega
          apply hd
          apply Nat.dvd_of_mod_eq_zero
          rw [← hxa', hxN, Nat.mod_self]
      · intro hx
        have hlt : a % N < N := Nat.mod_lt a (by omega)
        refine ⟨by omega, ?_⟩
        show x % N = a % N
        rw [hx, Nat.mod_mod]
    rw [hset, Finset.card_singleton]

private theorem fiber_card_eq_prod (a b : ℕ) :
    (Finset.univ.filter fun l : Lbl n =>
        l.e1 ≡ a [MOD 2 ^ (2 * n) - 1] ∧ l.e2 ≡ b [MOD 2 ^ n - 1]).card =
      ((Finset.range (2 ^ (2 * n))).filter (fun x => x ≡ a [MOD 2 ^ (2 * n) - 1])).card *
        ((Finset.range (2 ^ n)).filter (fun y => y ≡ b [MOD 2 ^ n - 1])).card := by
  rw [← Finset.card_product]
  apply Finset.card_nbij (fun l : Lbl n => (l.e1, l.e2))
  · intro l hl
    have hl' := (Finset.mem_filter.mp (Finset.mem_coe.mp hl)).2
    exact Finset.mem_coe.mpr (Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr l.e1_lt, hl'.1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr l.e2_lt, hl'.2⟩⟩)
  · intro l _ l' _ heq
    exact Lbl.ext_of_e (congrArg Prod.fst heq) (congrArg Prod.snd heq)
  · intro p hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hp)
    obtain ⟨hx', hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy', hy2⟩ := Finset.mem_filter.mp hy
    obtain ⟨l, hl1, hl2⟩ :=
      Lbl.exists_of_e (Finset.mem_range.mp hx') (Finset.mem_range.mp hy')
    refine ⟨l, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ l, ?_, ?_⟩),
      Prod.ext hl1 hl2⟩
    · rw [hl1]
      exact hx2
    · rw [hl2]
      exact hy2

theorem card_fiber (hn : 1 ≤ n) (a b : ℕ) :
    (Finset.univ.filter fun l : Lbl n =>
        l.e1 ≡ a [MOD 2 ^ (2 * n) - 1] ∧ l.e2 ≡ b [MOD 2 ^ n - 1]).card =
      2 ^ ((if 2 ^ (2 * n) - 1 ∣ a then 1 else 0) + (if 2 ^ n - 1 ∣ b then 1 else 0)) := by
  have h4 : 4 ≤ 2 ^ (2 * n) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ≤ 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [fiber_card_eq_prod, fiber_card_filter (2 ^ (2 * n) - 1) (2 ^ (2 * n)) a (by omega) (by omega),
    fiber_card_filter (2 ^ n - 1) (2 ^ n) b (by omega) (by omega), pow_add]
  split_ifs <;> norm_num

end Lbl

end CFSG.HardMathSupport.U4FF
