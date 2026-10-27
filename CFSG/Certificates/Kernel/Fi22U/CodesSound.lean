module

public import Certificates.Data.Kernel.Fi22U.Codes
public import CFSG.RankThree.Native.Fi22UCheckInputs
import all CFSG.Fischer.F4

public section

namespace CFSG.KC.Fi22U

open CFSG.Fischer CFSG.Monster.B.Fischer CFSG.RankThree.Native.Fi22U

@[expose] def dec (c : Nat) : Fin 6 → F4 := fun i => fi22F4 (co c i)

@[expose] def enc (v : Fin 6 → F4) : Nat :=
  mk6 (v 0).code.val (v 1).code.val (v 2).code.val (v 3).code.val (v 4).code.val (v 5).code.val

theorem co_lt (c i : Nat) : co c i < 4 := Nat.mod_lt _ (by norm_num)

theorem addC_lt (a b : Nat) : addC a b < 4 := by
  unfold addC
  have ha := Nat.mod_lt a (by norm_num : 0 < 4)
  have hb := Nat.mod_lt b (by norm_num : 0 < 4)
  generalize a % 4 = x at ha ⊢
  generalize b % 4 = y at hb ⊢
  interval_cases x <;> interval_cases y <;> decide

theorem mulC_lt (a b : Nat) : mulC a b < 4 := by
  unfold mulC
  omega

theorem co_mk6 {a b c d e f : Nat} (ha : a < 4) (hb : b < 4) (hc : c < 4) (hd : d < 4)
    (he : e < 4) (hf : f < 4) :
    co (mk6 a b c d e f) 0 = a ∧ co (mk6 a b c d e f) 1 = b ∧ co (mk6 a b c d e f) 2 = c ∧
      co (mk6 a b c d e f) 3 = d ∧ co (mk6 a b c d e f) 4 = e ∧ co (mk6 a b c d e f) 5 = f := by
  simp only [co, mk6]
  norm_num
  omega

theorem mk6_lt {a b c d e f : Nat} (ha : a < 4) (hb : b < 4) (hc : c < 4) (hd : d < 4)
    (he : e < 4) (hf : f < 4) : mk6 a b c d e f < 4096 := by
  unfold mk6
  omega

theorem eq_mk6 {c : Nat} (hc : c < 4096) :
    c = mk6 (co c 0) (co c 1) (co c 2) (co c 3) (co c 4) (co c 5) := by
  simp only [co, mk6]
  norm_num
  omega

theorem co_eq_of_lt {i : Nat} (hi : i < 6) {c : Nat} :
    co c i = if i = 0 then co c 0 else if i = 1 then co c 1 else if i = 2 then co c 2
      else if i = 3 then co c 3 else if i = 4 then co c 4 else co c 5 := by
  interval_cases i <;> rfl

theorem fi22F4_mod (a : Nat) : fi22F4 (a % 4) = fi22F4 a := by
  simp [fi22F4, Nat.mod_mod]

theorem addC_mod (a b : Nat) : addC (a % 4) (b % 4) = addC a b := by
  simp [addC, Nat.mod_mod]

theorem mulC_mod (a b : Nat) : mulC (a % 4) (b % 4) = mulC a b := by
  simp [mulC, Nat.mod_mod]

private theorem add_aux : ∀ x < 4, ∀ y < 4, fi22F4 x + fi22F4 y = fi22F4 (addC x y) := by
  decide

private theorem mul_aux : ∀ x < 4, ∀ y < 4, fi22F4 x * fi22F4 y = fi22F4 (mulC x y) := by
  decide

private theorem inv_aux : ∀ x < 4, (fi22F4 x)⁻¹ = fi22F4 (mulC x x) := by
  decide

private theorem zero_aux : ∀ x < 4, (fi22F4 x = 0 ↔ x = 0) := by
  decide

private theorem inj_aux : ∀ x < 4, ∀ y < 4, (fi22F4 x = fi22F4 y ↔ x = y) := by
  decide

theorem f4_add (a b : Nat) : fi22F4 a + fi22F4 b = fi22F4 (addC a b) := by
  rw [← fi22F4_mod a, ← fi22F4_mod b, add_aux _ (Nat.mod_lt _ (by norm_num)) _
    (Nat.mod_lt _ (by norm_num)), addC_mod]

theorem f4_mul (a b : Nat) : fi22F4 a * fi22F4 b = fi22F4 (mulC a b) := by
  rw [← fi22F4_mod a, ← fi22F4_mod b, mul_aux _ (Nat.mod_lt _ (by norm_num)) _
    (Nat.mod_lt _ (by norm_num)), mulC_mod]

theorem f4_sq (a : Nat) : fi22F4 a ^ 2 = fi22F4 (mulC a a) := by
  rw [pow_two, f4_mul]

theorem f4_inv (a : Nat) : (fi22F4 a)⁻¹ = fi22F4 (mulC a a) := by
  rw [← fi22F4_mod a, inv_aux _ (Nat.mod_lt _ (by norm_num)), mulC_mod]

theorem f4_eq_zero {a : Nat} (ha : a < 4) : fi22F4 a = 0 ↔ a = 0 := zero_aux a ha

theorem f4_inj {a b : Nat} (ha : a < 4) (hb : b < 4) : fi22F4 a = fi22F4 b ↔ a = b :=
  inj_aux a ha b hb

theorem fi22F4_code (x : F4) : fi22F4 x.code.val = x := by
  rcases x with ⟨⟨c, hc⟩⟩
  simp [fi22F4, Nat.mod_eq_of_lt hc]

theorem dec_apply (c : Nat) (i : Fin 6) : dec c i = fi22F4 (co c i) := rfl

theorem dec_mk6 {a b c d e f : Nat} (ha : a < 4) (hb : b < 4) (hc : c < 4) (hd : d < 4)
    (he : e < 4) (hf : f < 4) (i : Fin 6) :
    dec (mk6 a b c d e f) i =
      fi22F4 (if (i : Nat) = 0 then a else if (i : Nat) = 1 then b else if (i : Nat) = 2 then c
        else if (i : Nat) = 3 then d else if (i : Nat) = 4 then e else f) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := co_mk6 ha hb hc hd he hf
  fin_cases i <;> simp [dec, h0, h1, h2, h3, h4, h5]

theorem dec_inj {a b : Nat} (ha : a < 4096) (hb : b < 4096) (h : dec a = dec b) : a = b := by
  have e : ∀ i < 6, co a i = co b i := by
    intro i hi
    have := congrFun h ⟨i, hi⟩
    simp only [dec] at this
    exact (f4_inj (co_lt _ _) (co_lt _ _)).1 this
  rw [eq_mk6 ha, eq_mk6 hb, e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num),
    e 3 (by norm_num), e 4 (by norm_num), e 5 (by norm_num)]

theorem enc_lt (v : Fin 6 → F4) : enc v < 4096 :=
  mk6_lt (v 0).code.2 (v 1).code.2 (v 2).code.2 (v 3).code.2 (v 4).code.2 (v 5).code.2

theorem dec_enc (v : Fin 6 → F4) : dec (enc v) = v := by
  funext i
  rw [enc, dec_mk6 (v 0).code.2 (v 1).code.2 (v 2).code.2 (v 3).code.2 (v 4).code.2
    (v 5).code.2]
  fin_cases i <;> simp [fi22F4_code]

theorem dec_eq_zero {c : Nat} (hc : c < 4096) : dec c = 0 ↔ c = 0 := by
  constructor
  · intro h
    have e : ∀ i < 6, co c i = 0 := by
      intro i hi
      have := congrFun h ⟨i, hi⟩
      simp only [dec, Pi.zero_apply] at this
      exact (f4_eq_zero (co_lt _ _)).1 this
    rw [eq_mk6 hc, e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num),
      e 4 (by norm_num), e 5 (by norm_num)]
    rfl
  · rintro rfl
    funext i
    simp only [dec, co, Nat.zero_div, Nat.zero_mod, Pi.zero_apply]
    rfl

theorem scale_dec (s c : Nat) : fi22F4 s • dec c = dec (scaleC s c) := by
  funext i
  rw [scaleC, dec_mk6 (mulC_lt _ _) (mulC_lt _ _) (mulC_lt _ _) (mulC_lt _ _) (mulC_lt _ _)
    (mulC_lt _ _)]
  simp only [Pi.smul_apply, smul_eq_mul, dec_apply, f4_mul]
  fin_cases i <;> rfl

theorem add_dec (x y : Nat) : dec x + dec y = dec (addV x y) := by
  funext i
  rw [addV, dec_mk6 (addC_lt _ _) (addC_lt _ _) (addC_lt _ _) (addC_lt _ _) (addC_lt _ _)
    (addC_lt _ _)]
  simp only [Pi.add_apply, dec_apply, f4_add]
  fin_cases i <;> rfl

theorem scaleC_lt (s c : Nat) : scaleC s c < 4096 :=
  mk6_lt (mulC_lt _ _) (mulC_lt _ _) (mulC_lt _ _) (mulC_lt _ _) (mulC_lt _ _) (mulC_lt _ _)

theorem herm_dec (v x : Nat) : fi22Herm (dec v) (dec x) = fi22F4 (hermC v x) := by
  simp only [fi22Herm, Fin.sum_univ_six, dec_apply, f4_sq, f4_mul, f4_add, hermC, hT]
  rfl

theorem hermC_lt (v x : Nat) : hermC v x < 4 := addC_lt _ _

theorem tv_dec (v x : Nat) : fi22Tv (dec v) (dec x) = dec (tvC v x) := by
  rw [fi22Tv, herm_dec, scale_dec, add_dec, tvC]

theorem norm_dec (c : Nat) : fi22Normalize (dec c) = dec (normC c) := by
  have hz : ∀ i : Fin 6, decide (dec c i ≠ 0) = decide (co c i ≠ 0) := by
    intro i
    rw [dec_apply, Bool.decide_congr (not_congr (f4_eq_zero (co_lt c i)))]
  have hl : List.finRange 6 = [0, 1, 2, 3, 4, 5] := by decide
  have hs : ∀ i : Fin 6, ∀ m : Nat, (i : Nat) = m →
      (dec c i)⁻¹ • dec c = dec (scaleC (mulC (co c m) (co c m)) c) := by
    rintro i m rfl
    rw [dec_apply, f4_inv, scale_dec]
  have v0 : ((0 : Fin 6) : Nat) = 0 := rfl
  have v1 : ((1 : Fin 6) : Nat) = 1 := rfl
  have v2 : ((2 : Fin 6) : Nat) = 2 := rfl
  have v3 : ((3 : Fin 6) : Nat) = 3 := rfl
  have v4 : ((4 : Fin 6) : Nat) = 4 := rfl
  have v5 : ((5 : Fin 6) : Nat) = 5 := rfl
  unfold fi22Normalize normC
  rw [hl]
  simp only [List.find?_cons, List.find?_nil, hz, v0, v1, v2, v3, v4, v5]
  by_cases h0 : co c 0 = 0
  · by_cases h1 : co c 1 = 0
    · by_cases h2 : co c 2 = 0
      · by_cases h3 : co c 3 = 0
        · by_cases h4 : co c 4 = 0
          · by_cases h5 : co c 5 = 0
            · simp [h0, h1, h2, h3, h4, h5]
            · simp only [h0, h1, h2, h3, h4, h5, ne_eq, not_true_eq_false, not_false_eq_true,
                decide_false, decide_true, if_true, if_false]
              exact hs 5 5 rfl
          · simp only [h0, h1, h2, h3, h4, ne_eq, not_true_eq_false, not_false_eq_true,
              decide_false, decide_true, if_true, if_false]
            exact hs 4 4 rfl
        · simp only [h0, h1, h2, h3, ne_eq, not_true_eq_false, not_false_eq_true,
            decide_false, decide_true, if_true, if_false]
          exact hs 3 3 rfl
      · simp only [h0, h1, h2, ne_eq, not_true_eq_false, not_false_eq_true,
          decide_false, decide_true, if_true, if_false]
        exact hs 2 2 rfl
    · simp only [h0, h1, ne_eq, not_true_eq_false, not_false_eq_true,
        decide_false, decide_true, if_true, if_false]
      exact hs 1 1 rfl
  · simp only [h0, ne_eq, not_false_eq_true, decide_true, if_true]
    exact hs 0 0 rfl

theorem normC_lt {c : Nat} (hc : c < 4096) : normC c < 4096 := by
  unfold normC
  split_ifs <;> first | exact hc | exact scaleC_lt _ _

private theorem lex_step {x y : Fin 4} {l₁ l₂ : List (Fin 4)}
    (h : x < y ∨ x = y ∧ List.Lex (· < ·) l₁ l₂) : List.Lex (· < ·) (x :: l₁) (y :: l₂) := by
  rcases h with h | ⟨rfl, h⟩
  · exact List.Lex.rel h
  · exact List.Lex.cons h

theorem code_dec (c : Nat) (i : Fin 6) : (dec c i).code = ⟨co c i, co_lt c i⟩ := by
  simp [dec, fi22F4, Nat.mod_eq_of_lt (co_lt c i)]

theorem lex_dec {a b : Nat} (h : lexC a b = true) : fi22LexLt (dec a) (dec b) := by
  simp only [lexC, lexFrom, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [fi22LexLt, List.ofFn_succ, List.ofFn_zero, code_dec]
  have hf : ∀ {x y : Nat} (hx : x < 4) (hy : y < 4), x = y →
      (⟨x, hx⟩ : Fin 4) = ⟨y, hy⟩ := fun _ _ e => Fin.ext e
  refine lex_step ?_
  rcases h with h | ⟨e, h⟩
  · exact Or.inl h
  refine Or.inr ⟨hf _ _ e, lex_step ?_⟩
  rcases h with h | ⟨e, h⟩
  · exact Or.inl h
  refine Or.inr ⟨hf _ _ e, lex_step ?_⟩
  rcases h with h | ⟨e, h⟩
  · exact Or.inl h
  refine Or.inr ⟨hf _ _ e, lex_step ?_⟩
  rcases h with h | ⟨e, h⟩
  · exact Or.inl h
  refine Or.inr ⟨hf _ _ e, lex_step ?_⟩
  rcases h with h | ⟨e, h⟩
  · exact Or.inl h
  exact Or.inr ⟨hf _ _ e, List.Lex.rel h⟩

theorem lex_trans {α : Type} {r : α → α → Prop} (htr : ∀ a b c, r a b → r b c → r a c) :
    ∀ {l₁ l₂ l₃ : List α}, List.Lex r l₁ l₂ → List.Lex r l₂ l₃ → List.Lex r l₁ l₃
  | _, _, _, .nil, h => by cases h <;> exact .nil
  | _, _, _, .cons h₁, .cons h₂ => .cons (lex_trans htr h₁ h₂)
  | _, _, _, .cons _, .rel h₂ => .rel h₂
  | _, _, _, .rel h₁, .cons _ => .rel h₁
  | _, _, _, .rel h₁, .rel h₂ => .rel (htr _ _ _ h₁ h₂)

theorem fi22LexLt_trans {u v w : Fin 6 → F4} (h₁ : fi22LexLt u v) (h₂ : fi22LexLt v w) :
    fi22LexLt u w := by
  unfold fi22LexLt at *
  exact lex_trans (r := fun x y : Fin 4 => x < y) (fun _ _ _ h h' => lt_trans h h') h₁ h₂

theorem fi22LexLt_of_succ {f : Nat → Fin 6 → F4} {n : Nat}
    (h : ∀ j, j + 1 < n → fi22LexLt (f j) (f (j + 1))) :
    ∀ j < n, ∀ k < n, j < k → fi22LexLt (f j) (f k) := by
  intro j _ k hk hjk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hjk with hlt | rfl
    · exact fi22LexLt_trans (ih (by omega) hlt) (h k hk)
    · exact h j hk

theorem ptOK_iff {c : Nat} (hc : c < 4096) :
    ptOK c = true ↔ dec c ≠ 0 ∧ fi22Herm (dec c) (dec c) = 0 ∧ fi22Normalize (dec c) = dec c := by
  rw [ptOK, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
    beq_iff_eq, beq_iff_eq, and_assoc, ne_eq, ne_eq, dec_eq_zero hc, herm_dec,
    f4_eq_zero (hermC_lt c c), norm_dec]
  exact and_congr_right fun _ => and_congr_right fun _ =>
    ⟨fun e => by rw [e], fun e => dec_inj (normC_lt hc) hc e⟩

theorem cntPt_eq (n : Nat) : cntPt n = ((Finset.range n).filter fun c => ptOK c = true).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cntPt, ih, Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
    · rfl

theorem card_eq_cntPt : (Finset.univ.filter fun v : Fin 6 → F4 =>
    v ≠ 0 ∧ fi22Herm v v = 0 ∧ fi22Normalize v = v).card = cntPt 4096 := by
  rw [cntPt_eq]
  symm
  refine Finset.card_bij (fun c _ => dec c) ?_ ?_ ?_
  · intro c hc
    rw [Finset.mem_filter, Finset.mem_range] at hc
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (ptOK_iff hc.1).1 hc.2⟩
  · intro a ha b hb e
    rw [Finset.mem_filter, Finset.mem_range] at ha hb
    exact dec_inj ha.1 hb.1 e
  · intro v hv
    rw [Finset.mem_filter] at hv
    refine ⟨enc v, ?_, dec_enc v⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨enc_lt v, (ptOK_iff (enc_lt v)).2 ?_⟩
    rw [dec_enc]
    exact hv.2

theorem charsC_digit : ∀ (cs : List Char), (∀ c ∈ cs, c.toNat < 52) →
    ∀ j (hj : j < cs.length), charsC cs / 4 ^ j % 4 = (cs[j]'hj).toNat - 48
  | [], _, j, hj => absurd hj (Nat.not_lt_zero j)
  | c :: cs, h, j, hj => by
    have hc := h c List.mem_cons_self
    cases j with
    | zero =>
      simp only [charsC, pow_zero, Nat.div_one, List.getElem_cons_zero]
      omega
    | succ j =>
      have ih := charsC_digit cs (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) j
        (by simpa using hj)
      rw [charsC, pow_succ', ← Nat.div_div_eq_div_mul,
        show (c.toNat - 48 + 4 * charsC cs) / 4 = charsC cs by omega, ih]
      rfl

theorem co_tabC (T k : Nat) {i : Nat} (hi : i < 6) : co (tabC T k) i = T / 4 ^ (6 * k + i) % 4 := by
  unfold co tabC
  have e : T / 4 ^ (6 * k) % 4096 / 4 ^ i % 4 = T / 4 ^ (6 * k) / 4 ^ i % 4 := by
    generalize T / 4 ^ (6 * k) = y
    interval_cases i <;> norm_num <;> omega
  rw [e, Nat.div_div_eq_div_mul, ← pow_add]

end CFSG.KC.Fi22U

end
