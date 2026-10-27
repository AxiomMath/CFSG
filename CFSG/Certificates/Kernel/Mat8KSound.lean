module

public import Certificates.Data.Kernel.Mat8K

public section

namespace CFSG.KC.Mat8K

open CFSG.Quasithin.H13.Mat8Cert

theorem beq_symm {α : Type} [BEq α] [LawfulBEq α] (x y : α) : (x == y) = (y == x) := by
  by_cases h : x = y
  · subst h
    rfl
  · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (Ne.symm h)]

theorem BT.mem_tip {α : Type} [BEq α] (d k : ℕ) (xs : List α) (y : α) :
    BT.mem d k (.tip xs) y = xs.contains y := by
  cases d <;> rfl

theorem BT.mem_ins {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (d kx ky : ℕ) (t : BT α) (x y : α), (x = y → kx = ky) →
      BT.mem d ky (BT.ins d kx t x) y = (x == y || BT.mem d ky t y)
  | 0, _, _, .tip xs, x, y, _ => by
    simp only [BT.ins, BT.mem_tip, List.contains_cons]
    rw [beq_symm]
  | 0, _, _, .node _ _, x, y, _ => by
    simp only [BT.ins, BT.mem_tip, List.contains_cons, List.contains_nil, BT.mem, Bool.or_false]
    rw [beq_symm]
  | d + 1, kx, ky, .tip xs, x, y, h => by
    have h' : x = y → kx / 2 = ky / 2 := fun e => by rw [h e]
    by_cases hx : kx % 2 = 0 <;> by_cases hy : ky % 2 = 0 <;>
      simp only [BT.ins, BT.mem, hx, hy, beq_self_eq_true, if_true, if_false, BT.mem_tip,
        BT.mem_ins d (kx / 2) (ky / 2) _ x y h', Bool.false_eq_true, beq_iff_eq] <;>
      first
        | rfl
        | (have hne : (x == y) = false := by
             rw [beq_eq_false_iff_ne]; rintro rfl; have := h rfl; omega
           rw [hne, Bool.false_or])
  | d + 1, kx, ky, .node l r, x, y, h => by
    have h' : x = y → kx / 2 = ky / 2 := fun e => by rw [h e]
    by_cases hx : kx % 2 = 0 <;> by_cases hy : ky % 2 = 0 <;>
      simp only [BT.ins, BT.mem, hx, hy, beq_self_eq_true, if_true, if_false,
        BT.mem_ins d (kx / 2) (ky / 2) _ x y h', Bool.false_eq_true, beq_iff_eq] <;>
      first
        | rfl
        | (have hne : (x == y) = false := by
             rw [beq_eq_false_iff_ne]; rintro rfl; have := h rfl; omega
           rw [hne, Bool.false_or])

theorem memL_insL (t : BT (List ℕ)) (x y : List ℕ) : memL (insL t x) y = (x == y || memL t y) :=
  BT.mem_ins 16 _ _ t x y (fun e => by rw [e])

theorem memL_empty (y : List ℕ) : memL (.tip []) y = false := by
  simp [memL, BT.mem_tip]

theorem memL_foldl (L : List (List ℕ)) :
    ∀ (t : BT (List ℕ)) (y : List ℕ), memL (L.foldl insL t) y = (L.contains y || memL t y) := by
  induction L with
  | nil => intro t y; simp
  | cons a L ih =>
    intro t y
    rw [List.foldl_cons, ih, memL_insL, List.contains_cons, beq_symm a y]
    cases L.contains y <;> cases (y == a) <;> cases memL t y <;> rfl

theorem memL_ofListL (L : List (List ℕ)) (y : List ℕ) : memL (ofListL L) y = L.contains y := by
  rw [ofListL, memL_foldl, memL_empty, Bool.or_false]

theorem memN_insN (t : BT ℕ) (x y : ℕ) : memN (insN t x) y = (x == y || memN t y) :=
  BT.mem_ins 16 _ _ t x y (fun e => by rw [e])

theorem memN_empty (y : ℕ) : memN (.tip []) y = false := by
  simp [memN, BT.mem_tip]

theorem hs_contains_ofList (L : List (List ℕ)) (y : List ℕ) :
    (Std.HashSet.ofList L).contains y = memL (ofListL L) y := by
  rw [Std.HashSet.contains_ofList, memL_ofListL]

theorem hs_contains_ofList' (L : List (List ℕ)) :
    (Std.HashSet.ofList L).contains = memL (ofListL L) := by
  funext y
  exact hs_contains_ofList L y

theorem contains_eq_memL (L : List (List ℕ)) (y : List ℕ) : L.contains y = memL (ofListL L) y :=
  (memL_ofListL L y).symm

theorem nodupNAux_iff : ∀ (l : List ℕ) (t : BT ℕ),
    nodupNAux t l = true ↔ l.Nodup ∧ ∀ x ∈ l, memN t x = false
  | [], t => by simp [nodupNAux]
  | x :: l, t => by
    rw [nodupNAux, Bool.and_eq_true, nodupNAux_iff l (insN t x), List.nodup_cons]
    simp only [Bool.not_eq_true', memN_insN, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
      List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨fun hx => (h3 x hx).1 rfl, h2⟩, h1, fun y hy => (h3 y hy).2⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h3, h2, fun y hy => ⟨fun e => h1 (e ▸ hy), h4 y hy⟩⟩

theorem nodupNT_iff (l : List ℕ) : nodupNT l = true ↔ l.Nodup := by
  rw [nodupNT, nodupNAux_iff]
  simp [memN_empty]

theorem isChain_mergeSort_iff (l : List ℕ) :
    (l.mergeSort).IsChain (· < ·) ↔ l.Nodup := by
  have hs : (l.mergeSort).Pairwise (fun a b => decide (a ≤ b) = true) :=
    List.pairwise_mergeSort (fun a b c hab hbc => by simp at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  have hs' : (l.mergeSort).Pairwise (· ≤ ·) := hs.imp (fun h => by simpa using h)
  rw [List.isChain_iff_pairwise, ← (List.mergeSort_perm l _).nodup_iff]
  constructor
  · intro h
    exact h.imp (fun h => ne_of_lt h)
  · intro h
    exact (hs'.and h).imp (fun h => lt_of_le_of_ne h.1 h.2)

theorem decide_isChain_mergeSort (l : List ℕ) :
    decide ((l.mergeSort).IsChain (· < ·)) = nodupNT l := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, nodupNT_iff, isChain_mergeSort_iff]

theorem nodupB_eq (L : List (List ℕ)) : nodupB L = nodupNT (L.map code64) := by
  rw [nodupB, decide_isChain_mergeSort]

theorem mul_and_one (a v i : ℕ) : a * ((v >>> i) &&& 1) = if bt v i then a else 0 := by
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, bt, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ i) with h | h <;> simp [h]

theorem mv8K_eq (A : List ℕ) (v : ℕ) : mv8K A v = mv8 A v := by
  match A with
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: _ =>
    have h0 : v &&& 1 = (v >>> 0) &&& 1 := by rw [Nat.shiftRight_zero]
    simp only [mv8K, mv8, List.getD_cons_zero, List.getD_cons_succ]
    rw [h0]
    simp only [mul_and_one]
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | [_, _, _, _] => rfl
  | [_, _, _, _, _] => rfl
  | [_, _, _, _, _, _] => rfl
  | [_, _, _, _, _, _, _] => rfl

theorem mul8K_eq (A B : List ℕ) : mul8K A B = mul8 A B := by
  simp only [mul8K, mul8]
  exact List.map_congr_left (fun v _ => mv8K_eq A v)

theorem mul8K_eq' : mul8K = mul8 := by
  funext A B
  exact mul8K_eq A B

theorem evalWK_eq : evalWK = evalW := by
  funext gens w
  simp only [evalWK, evalW, mul8K_eq']

theorem mul8_toK (A B : List ℕ) : mul8 A B = mul8K A B := (mul8K_eq A B).symm

theorem mv8_toK (A : List ℕ) (v : ℕ) : mv8 A v = mv8K A v := (mv8K_eq A v).symm

theorem evalW_toK (gens : List (List ℕ)) (w : List ℕ) : evalW gens w = evalWK gens w := by
  rw [evalWK_eq]

def SRel (gens : List (List ℕ)) (a : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ))
    (b : BT (List ℕ) × List (List ℕ × List ℕ) × List (List ℕ × List ℕ)) : Prop :=
  a.2.1 = b.2.1.map Prod.fst ∧ a.2.2 = b.2.2 ∧ (∀ p ∈ b.2.1, p.2 = evalW gens p.1) ∧
    (∀ p ∈ b.2.2, p.2 = evalW gens p.1) ∧ ∀ y, a.1.contains y = memL b.1 y

def stepH (gens : List (List ℕ)) (wx : List ℕ × List ℕ)
    (st : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ)) (i : ℕ) :
    Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ) :=
  let y := mul8 (gens.getD i one8) wx.2
  if st.1.contains y then st else (st.1.insert y, (i :: wx.1) :: st.2.1, (i :: wx.1, y) :: st.2.2)

def stepT (gens : List (List ℕ)) (wx : List ℕ × List ℕ)
    (st : BT (List ℕ) × List (List ℕ × List ℕ) × List (List ℕ × List ℕ)) (i : ℕ) :
    BT (List ℕ) × List (List ℕ × List ℕ) × List (List ℕ × List ℕ) :=
  let y := mul8K (gens.getD i one8) wx.2
  if memL st.1 y then st else (insL st.1 y, (i :: wx.1, y) :: st.2.1, (i :: wx.1, y) :: st.2.2)

theorem stepRel (gens : List (List ℕ)) (wx : List ℕ × List ℕ) (hwx : wx.2 = evalW gens wx.1)
    (i : ℕ) (a : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ))
    (b : BT (List ℕ) × List (List ℕ × List ℕ) × List (List ℕ × List ℕ)) (h : SRel gens a b) :
    SRel gens (stepH gens wx a i) (stepT gens wx b i) := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  obtain ⟨h2, h3, h4, h5, h1⟩ := h
  dsimp only at h2 h3 h4 h5 h1
  subst h2 h3
  unfold stepH stepT
  dsimp only
  rw [h1, mul8K_eq]
  have hy : mul8 (gens.getD i one8) wx.2 = evalW gens (i :: wx.1) := by
    rw [hwx]
    rfl
  by_cases hc : memL b1 (mul8 (gens.getD i one8) wx.2) = true
  · rw [if_pos hc, if_pos hc]
    exact ⟨rfl, rfl, h4, h5, h1⟩
  · rw [if_neg hc, if_neg hc]
    refine ⟨rfl, rfl, ?_, ?_, fun z => ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hy
      · exact h4 p hp
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hy
      · exact h5 p hp
    · dsimp only
      rw [Std.HashSet.contains_insert, memL_insL, h1]

theorem foldl_rel {α β γ : Type} (R : α → β → Prop) (f : α → γ → α) (g : β → γ → β)
    (l : List γ) (hfg : ∀ a b c, c ∈ l → R a b → R (f a c) (g b c)) :
    ∀ (a : α) (b : β), R a b → R (l.foldl f a) (l.foldl g b) := by
  induction l with
  | nil => exact fun _ _ h => h
  | cons c l ih =>
    intro a b h
    exact ih (fun a b c' hc' => hfg a b c' (List.mem_cons_of_mem c hc')) _ _
      (hfg a b c List.mem_cons_self h)

theorem bfsW_eq (gens : List (List ℕ)) (cap : ℕ) :
    ∀ (fuel : ℕ) (seen : Std.HashSet (List ℕ)) (t : BT (List ℕ)) (acc' : List (List ℕ × List ℕ))
      (fr : List (List ℕ × List ℕ)), (∀ y, seen.contains y = memL t y) →
      (∀ p ∈ acc', p.2 = evalW gens p.1) → (∀ p ∈ fr, p.2 = evalW gens p.1) →
      bfsW gens cap fuel seen (acc'.map Prod.fst) fr = (bfsWT gens cap fuel t acc' fr).map Prod.fst ∧
        ∀ p ∈ bfsWT gens cap fuel t acc' fr, p.2 = evalW gens p.1
  | 0, _, _, _, _, _, hacc, _ => ⟨rfl, hacc⟩
  | fuel + 1, seen, t, acc', [], _, hacc, _ => by
    refine ⟨by simp only [bfsW, bfsWT], ?_⟩
    simpa only [bfsWT] using hacc
  | fuel + 1, seen, t, acc', wx :: fr, h, hacc, hfr => by
    simp only [bfsW, bfsWT, List.length_map]
    split_ifs with hc
    · exact ⟨rfl, hacc⟩
    · have hrel := foldl_rel (SRel gens)
        (fun st wx => (List.range gens.length).foldl (stepH gens wx) st)
        (fun st wx => (List.range gens.length).foldl (stepT gens wx) st) (wx :: fr)
        (fun a b wx hwx hab => foldl_rel (SRel gens) _ _ _
          (fun a b i _ hab => stepRel gens wx (hfr wx hwx) i a b hab) a b hab)
        (seen, acc'.map Prod.fst, []) (t, acc', []) ⟨rfl, rfl, hacc, by simp, h⟩
      have key : ∀ (A : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ))
          (B : BT (List ℕ) × List (List ℕ × List ℕ) × List (List ℕ × List ℕ)), SRel gens A B →
          bfsW gens cap fuel A.1 A.2.1 A.2.2 = (bfsWT gens cap fuel B.1 B.2.1 B.2.2).map Prod.fst ∧
            ∀ p ∈ bfsWT gens cap fuel B.1 B.2.1 B.2.2, p.2 = evalW gens p.1 := by
        rintro A B ⟨h2, h3, h4, h5, h1⟩
        rw [h2, h3]
        exact bfsW_eq gens cap fuel _ _ _ _ h1 h4 h5
      exact key _ _ hrel

theorem elemsOf_eq (gens : List (List ℕ)) (cap : ℕ) : elemsOf gens cap = elemsOfT gens cap := by
  have h := bfsW_eq gens cap 200 ((∅ : Std.HashSet (List ℕ)).insert one8) (insL (.tip []) one8)
    [([], one8)] [([], one8)]
    (fun y => by
      rw [Std.HashSet.contains_insert, memL_insL, Std.HashSet.contains_empty, memL_empty])
    (by simp [evalW]) (by simp [evalW])
  rw [elemsOf, wordsOf, elemsOfT]
  change (bfsW gens cap 200 _ ([([], one8)].map Prod.fst) _).map (evalW gens) = _
  rw [h.1, List.map_map]
  exact List.map_congr_left (fun p hp => (h.2 p hp).symm)

end CFSG.KC.Mat8K

end
