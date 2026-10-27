module

public import Certificates.Data.Kernel.G23Code.Defs
public import CFSG.Certificates.Kernel.LocLn.Sound

public section

namespace CFSG.KS.G23C

open CFSG.KD.G23C CFSG.KC.Ord CFSG.KS.Ord CFSG.KD.LocLn CFSG.KS.LocLn
open CFSG.GH74.QTGen4.Recog.G23 CFSG.RankThree.PartTwo.Census.Carrier.G2Three

theorem bAnd_iff {a b : Bool} : Bool.rec (motive := fun _ => Bool) false b a = true ↔
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp

theorem pkL_lt : ∀ l : List ℕ, (∀ d ∈ l, d < 256) → pkL l < 2 ^ (8 * l.length)
  | [], _ => by
    change 0 < _
    exact Nat.two_pow_pos _
  | a :: l, h => by
    have ha : a < 256 := h a (List.mem_cons_self ..)
    have ih := pkL_lt l fun d hd => h d (List.mem_cons_of_mem _ hd)
    change a + (pkL l) <<< 8 < _
    have e : (2 : ℕ) ^ (8 * (a :: l).length) = 2 ^ (8 * l.length) * 2 ^ 8 := by
      rw [← Nat.pow_add, List.length_cons]
      congr 1
    rw [Nat.shiftLeft_eq, e]
    have : pkL l + 1 ≤ 2 ^ (8 * l.length) := ih
    have h8 : (2 : ℕ) ^ 8 = 256 := by norm_num
    rw [h8]
    nlinarith

theorem code_sound {l : List ℕ} (h : codeChk l = true) :
    Canon 3 14 8 (pkL l) ∧ ordMat 3 14 8 112 (pkL l) = dec14 l ∧ canon14 l = true := by
  obtain ⟨h1, h2⟩ := bAnd_iff.1 h
  have hl : l.length = 196 := by rw [← lenL_eq]; exact Nat.eq_of_beq_eq_true h1
  have hs := smallL_spec l h2
  have hs' : ∀ d ∈ l, d < 256 := fun d hd => by have := hs d hd; omega
  have hlane : ∀ t (ht : t < l.length), lane 8 (pkL l) t = l[t] := lane_pkL l hs'
  refine ⟨⟨?_, fun t ht => ?_⟩, ?_, ?_⟩
  · have := pkL_lt l hs'
    have e14 : (14 : ℕ) * 14 = 196 := rfl
    rw [hl] at this
    rw [e14]
    exact this
  · rw [hlane t (by omega)]
    exact hs _ (List.getElem_mem _)
  · funext i j
    have e : (112 : ℕ) = 14 * 8 := rfl
    rw [e, ordMat_lane]
    have hij : 14 * i.val + j.val < l.length := by omega
    simp only [dec14, Matrix.of_apply]
    rw [hlane _ hij, List.getD_eq_getElem _ _ hij]
  · simp only [canon14, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
    exact ⟨hl, hs⟩

theorem mul_sound (hc : constsChk = true) {A B : ℕ} (hA : Canon 3 14 8 A) (hB : Canon 3 14 8 B) :
    Canon 3 14 8 (mul A B) ∧ ordMat 3 14 8 112 (mul A B) =
      ordMat 3 14 8 112 A * ordMat 3 14 8 112 B :=
  mulR_sound (p := 3) (w := 8) (S := 112) (d := 14) (T := 5) hc hA hB

theorem one_sound' (hc : constsChk = true) : Canon 3 14 8 ONE ∧ ordMat 3 14 8 112 ONE = 1 :=
  one_sound (p := 3) (w := 8) (S := 112) (d := 14) (T := 5) hc

theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem letP_eq (l : Fin 6 × Bool) : letP l = pkL (letterCode l) := by
  obtain ⟨i, b⟩ := l
  cases b <;> rfl

theorem letter_sound (hI : ∀ i, invChk i = true) (l : Fin 6 × Bool) :
    Canon 3 14 8 (letP l) ∧ ordMat 3 14 8 112 (letP l) = dec14 (letterCode l) := by
  obtain ⟨h1, h2⟩ := bAnd_iff.1 (hI l.1)
  obtain ⟨h2, -⟩ := bAnd_iff.1 h2
  rw [letP_eq]
  obtain ⟨i, b⟩ := l
  cases b
  · exact ⟨(code_sound h2).1, (code_sound h2).2.1⟩
  · exact ⟨(code_sound h1).1, (code_sound h1).2.1⟩

theorem evalFrom_sound (hc : constsChk = true) (hI : ∀ i, invChk i = true) :
    ∀ (r : List (Fin 6 × Bool)) (accL : List ℕ) (acc : ℕ), Canon 3 14 8 acc →
      ordMat 3 14 8 112 acc = dec14 accL →
      Canon 3 14 8 (evalFrom r acc) ∧ ordMat 3 14 8 112 (evalFrom r acc) =
        dec14 (r.foldl (fun a l => mul14 a (letterCode l)) accL)
  | [], _, _, hA, he => ⟨hA, he⟩
  | l :: r, accL, acc, hA, he => by
    change Canon 3 14 8 (CFSG.KC.Loop.strictN (mul acc (letP l)) (evalFrom r)) ∧
      ordMat 3 14 8 112 (CFSG.KC.Loop.strictN (mul acc (letP l)) (evalFrom r)) = _
    rw [strictN_eq', List.foldl_cons]
    obtain ⟨hL1, hL2⟩ := letter_sound hI l
    obtain ⟨hm1, hm2⟩ := mul_sound hc hA hL1
    refine evalFrom_sound hc hI r _ _ hm1 ?_
    rw [hm2, he, hL2, dec14_mul14]

theorem canon14_foldl : ∀ (r : List (Fin 6 × Bool)) (acc : List ℕ), canon14 acc = true →
    canon14 (r.foldl (fun a l => mul14 a (letterCode l)) acc) = true
  | [], _, h => h
  | l :: r, acc, _ => by
    rw [List.foldl_cons]
    exact canon14_foldl r _ (canon14_mul14 _ _)

theorem wordsChk_spec : ∀ W : List (List (Fin 6 × Bool)), wordsChk W = true →
    ∀ r ∈ W, evalP r = ONE
  | [], _, r, hr => absurd hr List.not_mem_nil
  | a :: W, h, r, hr => by
    change Bool.rec (motive := fun _ => Bool) false (wordsChk W) (Nat.beq (evalP a) ONE) = true at h
    obtain ⟨h1, h2⟩ := bAnd_iff.1 h
    rcases List.mem_cons.1 hr with rfl | hr
    · exact Nat.eq_of_beq_eq_true h1
    · exact wordsChk_spec W h2 r hr

theorem inv_sound (hc : constsChk = true) (hI : ∀ i, invChk i = true) (i : Fin 6) :
    mul14 (eCode i) (eInvCode i) = one14 := by
  obtain ⟨h1, h2⟩ := bAnd_iff.1 (hI i)
  obtain ⟨h2, h3⟩ := bAnd_iff.1 h2
  obtain ⟨a1, a2, -⟩ := code_sound h1
  obtain ⟨b1, b2, -⟩ := code_sound h2
  obtain ⟨-, m2⟩ := mul_sound hc a1 b1
  refine dec14_injective (canon14_mul14 _ _) canon14_one14 ?_
  rw [dec14_mul14, dec14_one14, ← a2, ← b2, ← m2, Nat.eq_of_beq_eq_true h3, (one_sound' hc).2]

theorem rels_sound (hc : constsChk = true) (hI : ∀ i, invChk i = true)
    {W : List (List (Fin 6 × Bool))} (hW : wordsChk W = true) :
    ∀ r ∈ W, evalCode r = one14 := by
  intro r hr
  obtain ⟨o1, o2⟩ := one_sound' hc
  obtain ⟨-, e2⟩ := evalFrom_sound hc hI r one14 ONE o1 (o2.trans dec14_one14.symm)
  refine dec14_injective (canon14_foldl r _ canon14_one14) canon14_one14 ?_
  unfold evalCode
  rw [← e2, dec14_one14]
  change ordMat 3 14 8 112 (evalP r) = 1
  rw [wordsChk_spec W hW r hr, o2]

end CFSG.KS.G23C

end
