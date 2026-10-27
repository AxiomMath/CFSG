module

public import Certificates.Data.Kernel.G2Three.Syl
public import CFSG.Certificates.Kernel.G2Three.Tables
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G23Check

public section

namespace CFSG.KC.G2Three

open CFSG.KS.Mat3 CFSG.KC.Ord CFSG.KC.Loop CFSG.RankThree.PartTwo.Census.Carrier.G2Three
  CFSG.Quasithin.G2U CFSG.KD.G2Three CFSG.RankThree.PartTwo.Sec4.Item434RemG23

theorem allL_true {p : ℕ → Bool} : ∀ {l : List ℕ}, allL p l = true → ∀ x ∈ l, p x = true
  | [], _, x, hx => absurd hx List.not_mem_nil
  | y :: l, h, x, hx => by
    have h' : Bool.rec (motive := fun _ => Bool) false (allL p l) (p y) = true := h
    obtain ⟨h1, h2⟩ := bAnd_g2 h'
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact allL_true h2 x hx

theorem close_at {X G POS : ℕ → ℕ} {n k hi : ℕ} (h : closeK X G POS n k hi = true)
    (hm : n * k ≤ 64 * hi) :
    ∀ i < n * k, POS i < n ∧ X (POS i) = MUL (X (i / k)) (G (i % k)) := by
  intro i hi'
  have := allBelow_g2 h hm i hi'
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
  exact this

theorem row_at {PP RTP R : ℕ} (h : rowK PP RTP R = true) :
    ∀ k < 728, fR R (k + 1) = fR RTP (3 * fR R (pA PP k) + pB PP k) := by
  intro k hk
  have := allBelow_g2 h (by decide) k hk
  exact Nat.eq_of_beq_eq_true this

theorem beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hq : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hq) h

variable (hc : consts3OK 14 5 196 LO RM CI ONE UP = true) (hone : pk one14 = ONE)

include hc hone in
theorem pow14_pk {c : List ℕ} {E : ℕ} (h : canon14 c = true ∧ pk c = E) (k : ℕ) :
    canon14 (pow14 c k) = true ∧ pk (pow14 c k) = pwK E k := by
  unfold pow14 pwK
  rcases Nat.lt_trichotomy k 1 with hk | rfl | hk
  · have : k = 0 := by omega
    subst this
    rw [if_pos rfl, Nat.beq_refl, cond_true]
    exact ⟨canon14_one14, hone⟩
  · have h0 : Nat.beq 1 0 = false := rfl
    rw [if_neg (by omega), if_pos rfl, h0, cond_false, Nat.beq_refl, cond_true]
    exact h
  · have h0 : Nat.beq k 0 = false := beq_false (by omega)
    have h1 : Nat.beq k 1 = false := beq_false (by omega)
    rw [if_neg (by omega), if_neg (by omega), h0, h1, cond_false, cond_false]
    exact mulE hc h h

theorem blt_false {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hq : Nat.blt a b
  · rfl
  · exact absurd (Nat.blt_eq.mp hq) h

include hc hone in
theorem letterCode_pk {A : ℕ → ℕ}
    (hA : ∀ s < 4, canon14 ([x0c, x1c, y0c, y1c].getD s one14) = true ∧
      pk ([x0c, x1c, y0c, y1c].getD s one14) = A s) (l : ℕ) :
    canon14 (letterCode l) = true ∧ pk (letterCode l) = letK A l := by
  unfold letterCode letK
  by_cases h4 : l < 4
  · rw [if_pos h4, Nat.blt_eq.mpr h4, cond_true]
    exact hA l h4
  · rw [if_neg h4, blt_false h4, cond_false]
    by_cases h8 : l < 8
    · rw [Nat.blt_eq.mpr h8, cond_true]
      have h' := hA (l - 4) (by omega)
      exact mulE hc h' h'
    · rw [blt_false h8, cond_false, List.getD_eq_default _ _ (by simp; omega)]
      exact mulE hc ⟨canon14_one14, hone⟩ ⟨canon14_one14, hone⟩

include hc in
theorem foldl_pk {α : Type} (f : α → List ℕ) (F : α → ℕ)
    (hf : ∀ a, canon14 (f a) = true ∧ pk (f a) = F a) :
    ∀ (w : List α) (acc : List ℕ) (A : ℕ), canon14 acc = true ∧ pk acc = A →
      canon14 (w.foldl (fun c a => mul14 c (f a)) acc) = true ∧
        pk (w.foldl (fun c a => mul14 c (f a)) acc) = w.foldl (fun c a => MUL c (F a)) A
  | [], _, _, h => h
  | a :: w, acc, A, h => foldl_pk f F hf w _ _ (mulE hc h (hf a))

include hc hone in
theorem wordCode_pk {A : ℕ → ℕ}
    (hA : ∀ s < 4, canon14 ([x0c, x1c, y0c, y1c].getD s one14) = true ∧
      pk ([x0c, x1c, y0c, y1c].getD s one14) = A s) (w : List ℕ) :
    canon14 (wordCode w) = true ∧ pk (wordCode w) = wordK A w :=
  foldl_pk hc letterCode (letK A) (letterCode_pk hc hone hA) w one14 ONE ⟨canon14_one14, hone⟩

theorem foldl_push_spec {β : Type} (d : β) (step : β → ℕ × ℕ → β) :
    ∀ (par : List (ℕ × ℕ)) (acc : Array β),
      (∀ i < par.length, (par.getD i (0, 0)).1 < acc.size + i) →
      (par.foldl (fun acc ps => acc.push (step (acc.getD ps.1 d) ps)) acc).size =
          acc.size + par.length ∧
        (∀ t < acc.size,
          (par.foldl (fun acc ps => acc.push (step (acc.getD ps.1 d) ps)) acc).getD t d =
            acc.getD t d) ∧
        ∀ i < par.length,
          (par.foldl (fun acc ps => acc.push (step (acc.getD ps.1 d) ps)) acc).getD
              (acc.size + i) d =
            step ((par.foldl (fun acc ps => acc.push (step (acc.getD ps.1 d) ps)) acc).getD
              (par.getD i (0, 0)).1 d) (par.getD i (0, 0))
  | [], acc, _ => ⟨by simp, fun _ _ => rfl, fun i hi => absurd hi (by simp)⟩
  | ps :: par, acc, hpar => by
    have h0 := hpar 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at h0
    obtain ⟨ih1, ih2, ih3⟩ := foldl_push_spec d step par (acc.push (step (acc.getD ps.1 d) ps))
      (fun i hi => by
        have := hpar (i + 1) (by simp; omega)
        simp only [List.getD_cons_succ, Array.size_push] at this ⊢
        omega)
    simp only [Array.size_push] at ih1 ih2 ih3
    rw [List.foldl_cons, List.length_cons]
    refine ⟨by rw [ih1]; omega, fun t ht => ?_, fun i hi => ?_⟩
    · rw [ih2 t (by omega), getD_push_lt d ht]
    · rcases i with _ | i
      · rw [Nat.add_zero, ih2 _ (by omega), getD_push_eq, List.getD_cons_zero,
          ih2 _ (by omega), getD_push_lt d h0]
      · rw [List.getD_cons_succ, (by omega : acc.size + (i + 1) = acc.size + 1 + i)]
        exact ih3 i (by simpa using hi)

end CFSG.KC.G2Three

end
