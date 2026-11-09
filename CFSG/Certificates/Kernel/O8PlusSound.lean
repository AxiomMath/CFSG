module

public import CFSG.Certificates.Kernel.O8EnumSound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Lin

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.OmegaEight.Stage2

@[expose] noncomputable def powKK (a : ℕ) : ℕ → ℕ
  | 0 => ID12
  | n + 1 => mul12K (powKK a n) a

theorem powK_eq (a n : ℕ) : powK a n = powKK a n := by
  induction n with
  | zero => simp [powK, powKK, idK_eq]
  | succ n ih => simp [powK, powKK, ih, mulK_eq]

@[expose] noncomputable def fpowAuxK : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | f + 1, b, n, acc =>
    if n = 0 then acc else fpowAuxK f (mul12K b b) (n / 2) (if n % 2 = 1 then mul12K acc b else acc)

theorem fpowAux_eq (f b n acc : ℕ) : fpowAux f b n acc = fpowAuxK f b n acc := by
  induction f generalizing b n acc with
  | zero => simp [fpowAux, fpowAuxK]
  | succ f ih => simp [fpowAux, fpowAuxK, ih, mulK_eq]

theorem fpowK_eq (a n : ℕ) : fpowK a n = fpowAuxK 64 a n ID12 := by
  rw [fpowK, fpowAux_eq, idK_eq]

@[expose] noncomputable def stepKK (R : Array ℕ) (ins : ℕ × ℕ × ℕ) : Array ℕ :=
  R.push (if ins.1 = 0 then mul12K (R.getD ins.2.1 ID12) (R.getD ins.2.2 ID12)
    else powKK (R.getD ins.2.1 ID12) ins.2.2)

theorem stepK_eq : stepK = stepKK := by
  funext R ins
  simp only [stepK, stepKK, mulK_eq, powK_eq, idK_eq]

theorem runK_eq (gens : Array ℕ) (prog : List (ℕ × ℕ × ℕ)) :
    runK gens prog = prog.foldl stepKK gens := by
  rw [runK, stepK_eq]

@[expose] noncomputable def conPartK : List (ℕ × ℕ) → List (List ℕ) → ℕ → ℕ
  | c :: cs, q :: qs, m => linComb q (mul12K c.1 m ^^^ mul12K m c.2) ^^^ conPartK cs qs m
  | _, _, _ => 0

theorem conPart_eq : ∀ (cs : List (ℕ × ℕ)) (qs : List (List ℕ)) (m : ℕ),
    conPart cs qs m = conPartK cs qs m
  | c :: cs, q :: qs, m => by simp only [conPart, conPartK, mulK_eq, conPart_eq cs qs m]
  | [], _, _ => by simp [conPart, conPartK]
  | _ :: _, [], _ => by simp [conPart, conPartK]

theorem spanAll_of_chunks {qf : List ℕ} {d s : ℕ} {P : ℕ → Bool} (hs : s ≤ d)
    (h : ∀ k < 2 ^ (d - s), ((List.range (2 ^ s)).all fun c => P (linComb qf (k * 2 ^ s + c))) =
      true) : spanAll qf d P = true := by
  simp only [spanAll, List.all_eq_true, List.mem_range] at h ⊢
  intro c hc
  have h2 : 0 < 2 ^ s := by positivity
  have hd : 2 ^ d = 2 ^ (d - s) * 2 ^ s := by rw [← pow_add, Nat.sub_add_cancel hs]
  have hk : c / 2 ^ s < 2 ^ (d - s) := by
    rw [Nat.div_lt_iff_lt_mul h2, ← hd]
    exact hc
  have := h (c / 2 ^ s) hk (c % 2 ^ s) (Nat.mod_lt _ h2)
  rwa [Nat.div_add_mod' c (2 ^ s)] at this

@[expose] noncomputable def combAllK (P : ℕ → Bool) : List ℕ → ℕ → Bool
  | [], b => P b
  | q :: qs, b => combAllK P qs b && combAllK P qs (b ^^^ q)

theorem combAllK_imp (P : ℕ → Bool) : ∀ (qs : List ℕ) (b : ℕ), combAllK P qs b = true →
    ∀ c < 2 ^ qs.length, P (b ^^^ linComb qs c) = true
  | [], b, h, c, hc => by
    obtain rfl : c = 0 := by simpa using hc
    simpa [combAllK, linComb] using h
  | q :: qs, b, h, c, hc => by
    simp only [combAllK, Bool.and_eq_true] at h
    rw [List.length_cons, pow_succ] at hc
    have hc2 : c / 2 < 2 ^ qs.length := by omega
    simp only [linComb]
    by_cases ht : c.testBit 0
    · simp only [ht, ↓reduceIte, ← Nat.xor_assoc]
      exact combAllK_imp P qs _ h.2 _ hc2
    · simp only [ht, Bool.false_eq_true, ↓reduceIte, Nat.zero_xor]
      exact combAllK_imp P qs _ h.1 _ hc2

theorem linComb_append : ∀ (xs ys : List ℕ) (k c : ℕ), c < 2 ^ xs.length →
    linComb (xs ++ ys) (k * 2 ^ xs.length + c) = linComb xs c ^^^ linComb ys k
  | [], ys, k, c, hc => by
    obtain rfl : c = 0 := by simpa using hc
    simp [linComb]
  | x :: xs, ys, k, c, hc => by
    rw [List.length_cons, pow_succ] at hc ⊢
    have hc2 : c / 2 < 2 ^ xs.length := by omega
    have e0 : k * (2 ^ xs.length * 2) = 2 * (k * 2 ^ xs.length) := by
      rw [Nat.mul_comm (2 ^ _) 2, Nat.mul_left_comm]
    have e1 : (k * (2 ^ xs.length * 2) + c) / 2 = k * 2 ^ xs.length + c / 2 := by
      rw [e0]
      omega
    have e2 : (k * (2 ^ xs.length * 2) + c).testBit 0 = c.testBit 0 := by
      rw [e0, Nat.testBit_zero, Nat.testBit_zero, Nat.mul_comm 2, Nat.add_comm,
        Nat.add_mul_mod_self_right]
    simp only [List.cons_append, linComb, e1, e2, linComb_append xs ys k (c / 2) hc2,
      Nat.xor_assoc]

theorem spanAll_of_combAllK {qf : List ℕ} {d s : ℕ} {P : ℕ → Bool} (hd : qf.length = d)
    (hs : s ≤ d) (h : ∀ k < 2 ^ (d - s), combAllK P (qf.take s) (linComb (qf.drop s) k) = true) :
    spanAll qf d P = true := by
  have hl : (qf.take s).length = s := by rw [List.length_take, hd, Nat.min_eq_left hs]
  refine spanAll_of_chunks hs fun k hk => ?_
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  have := combAllK_imp P _ _ (h k hk) c (by rwa [hl])
  have hq := linComb_append (qf.take s) (qf.drop s) k c (by rwa [hl])
  rw [List.take_append_drop, hl] at hq
  rwa [hq, Nat.xor_comm]

@[expose] def sqTabK (mul : ℕ → ℕ → ℕ) : List ℕ → List (ℕ × ℕ × List ℕ)
  | [] => []
  | q :: qs => (q, mul q q, qs.map fun r => mul q r ^^^ mul r q) :: sqTabK mul qs

@[expose] noncomputable def sqAllK (Q : ℕ → ℕ → Bool) :
    List (ℕ × ℕ × List ℕ) → ℕ → ℕ → List ℕ → Bool
  | [], b, s, _ => Q b s
  | (q, t, C) :: es, b, s, A => sqAllK Q es b s A.tail &&
      sqAllK Q es (b ^^^ q) (s ^^^ A.headD 0 ^^^ t) (List.zipWith (· ^^^ ·) A.tail C)

theorem sqAllK_imp (mul : ℕ → ℕ → ℕ) (hl : ∀ a b c, mul (a ^^^ b) c = mul a c ^^^ mul b c)
    (hr : ∀ a b c, mul a (b ^^^ c) = mul a b ^^^ mul a c) (Q : ℕ → ℕ → Bool) :
    ∀ (qs : List ℕ) (b : ℕ) (A : List ℕ), A = qs.map (fun r => mul b r ^^^ mul r b) →
      sqAllK Q (sqTabK mul qs) b (mul b b) A = true → combAllK (fun m => Q m (mul m m)) qs b = true
  | [], b, A, _, h => by simpa [sqAllK, sqTabK, combAllK] using h
  | q :: qs, b, A, hA, h => by
    subst hA
    simp only [sqTabK, sqAllK, List.map_cons, List.tail_cons, List.headD_cons,
      Bool.and_eq_true] at h
    simp only [combAllK, Bool.and_eq_true]
    have hs : mul (b ^^^ q) (b ^^^ q) = mul b b ^^^ (mul b q ^^^ mul q b) ^^^ mul q q := by
      rw [hl, hr, hr]
      ac_rfl
    obtain ⟨h1, h2⟩ := h
    rw [← hs] at h2
    refine ⟨sqAllK_imp mul hl hr Q qs b _ rfl h1, sqAllK_imp mul hl hr Q qs (b ^^^ q) _ ?_ h2⟩
    rw [List.zipWith_map, List.zipWith_self]
    congr 1
    funext r
    rw [hl, hr]
    ac_rfl

@[expose] noncomputable def sqChunkK (Q : ℕ → ℕ → Bool) (qs : List ℕ) (s k : ℕ) : Bool :=
  sqAllK Q (sqTabK mul12K (qs.take s)) (linComb (qs.drop s) k)
    (mul12K (linComb (qs.drop s) k) (linComb (qs.drop s) k))
    ((qs.take s).map fun r =>
      mul12K (linComb (qs.drop s) k) r ^^^ mul12K r (linComb (qs.drop s) k))

theorem combAllK_of_sqChunkK {Q : ℕ → ℕ → Bool} {qs : List ℕ} {s k : ℕ}
    (h : sqChunkK Q qs s k = true) :
    combAllK (fun m => Q m (mul12K m m)) (qs.take s) (linComb (qs.drop s) k) = true :=
  sqAllK_imp mul12K (fun a b c => by simp only [← mulK_eq]; exact mulK_xor_left a b c)
    (fun a b c => by simp only [← mulK_eq]; exact mulK_xor_right a b c) Q _ _ _ rfl h

theorem spanAll_of_sqChunkK {qf : List ℕ} {d s : ℕ} {P : ℕ → Bool} {Q : ℕ → ℕ → Bool}
    (hQ : ∀ m, Q m (mul12K m m) = P m) (hd : qf.length = d) (hs : s ≤ d)
    (h : ∀ k < 2 ^ (d - s), sqChunkK Q qf s k = true) : spanAll qf d P = true := by
  have hP : (fun m => Q m (mul12K m m)) = P := funext hQ
  rw [← hP]
  exact spanAll_of_combAllK hd hs fun k hk => combAllK_of_sqChunkK (h k hk)

theorem spanAll_of_sqChunkK_len {qf : List ℕ} {d : ℕ} {P : ℕ → Bool} {Q : ℕ → ℕ → Bool}
    (hQ : ∀ m, Q m (mul12K m m) = P m) (h : (qf.length == d && sqChunkK Q qf d 0) = true) :
    spanAll qf d P = true := by
  rw [Bool.and_eq_true, beq_iff_eq] at h
  exact spanAll_of_sqChunkK hQ h.1 le_rfl fun k hk => by
    obtain rfl : k = 0 := by simpa using hk
    exact h.2

end CFSG.KC.O8

end
