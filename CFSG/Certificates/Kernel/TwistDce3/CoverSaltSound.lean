module

public import Certificates.Data.Kernel.TwistDce3.CoverSalt
public import CFSG.Certificates.Kernel.TwistDce3.CoverSound
import CFSG.Certificates.Kernel.TwistDce.Core
import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.Certificates.TwDce3

open CFSG.KC.TwDce hiding evP isOne pathW wsK wsFail wsJ wsMk wsBad dKind dN1 dN2 isFact walkRun
  walkOK recOK nodesOK foldStep foldRange andB
open CFSG.KC (andB)
open CFSG.KC.TwDce2 hiding evP isOne tStep posStep walkRun walkOK recOK foldStep foldRange
  lettersOK coverK coverRange relsOK fixAll stabRange
open CFSG.KC.TwDce3 CFSG.KC.YModel
open CFSG.Certificates.TwDce.Words (sB_eq)
open CFSG.Certificates.TwDce2.Words (kandB_iff)

theorem saltStep_lt (e : ℕ) : saltStep e < 2 ^ 64 := by
  unfold saltStep ones
  change _ &&& (1 <<< 64 - 1) < _
  exact Nat.and_lt_two_pow _ (by rw [Nat.shiftLeft_eq, Nat.one_mul]; omega)

theorem fld_s_one_iff (s q : ℕ) : fld s q 1 = 1 ↔ s.testBit q = true := by
  unfold fld
  change (s >>> q) &&& 1 = 1 ↔ _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq,
    decide_eq_true_iff]

theorem testBit_step (s x d q : ℕ) (hd : d < 2 ^ 64) :
    (Nat.xor (Nat.lor s (Nat.shiftLeft 1 (Nat.add x 64))) d).testBit (q + 64) = true ↔
      s.testBit (q + 64) = true ∨ q = x := by
  change ((s ||| (1 <<< (x + 64))) ^^^ d).testBit (q + 64) = true ↔ _
  have hd' : d.testBit (q + 64) = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hd (Nat.pow_le_pow_right (by norm_num) (by omega)))
  rw [Nat.testBit_xor, hd', Bool.xor_false, Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul,
    Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_iff]
  exact or_congr_right ⟨fun h => by omega, fun h => by rw [h]⟩

noncomputable def coverLoopS (PB : ℕ) (F : ℕ → ℕ) (INVM : ℕ) (RD RW : ℕ → ℕ) (NP n : ℕ)
    (DS : List ℕ) (k : ℕ) (L : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun s => Nat.beq (Nat.shiftRight s (nat_lit 64)) (ones NP))
    (fun e _ ih s =>
      Bool.rec (motive := fun _ => Bool)
        (sB (fld e (nat_lit 1) (ones (nat_lit 21))) (fun c =>
          sB (Nat.shiftRight e (nat_lit 22)) (fun p =>
            andB (andB (isStabOf RD n k (Nat.shiftRight c (nat_lit 1)))
                (Nat.beq (fld s (Nat.add p (nat_lit 64)) (nat_lit 1)) (nat_lit 1)))
              (sB (evP PB F (gWord INVM RW c) p) (fun x =>
                sB (Nat.xor (Nat.lor s (Nat.shiftLeft (nat_lit 1) (Nat.add x (nat_lit 64))))
                  (saltStep e)) ih)))))
        (sB (Nat.shiftRight e (nat_lit 1)) (fun f => sB (RD f) (fun d =>
          andB (andB (Nat.blt f n) (andB (isFact (dKind d))
              (andB (Nat.beq (dN1 d) k) (CFSG.KC.LaneChain.memN (dN2 d) DS))))
            (sB (evP PB F (wInv INVM (RW f)) (nat_lit 0)) (fun x =>
              sB (Nat.xor (Nat.lor s (Nat.shiftLeft (nat_lit 1) (Nat.add x (nat_lit 64))))
                (saltStep e)) ih)))))
        (Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1)))
    L

theorem coverLoopS_nil (PB : ℕ) (F : ℕ → ℕ) (INVM : ℕ) (RD RW : ℕ → ℕ) (NP n : ℕ)
    (DS : List ℕ) (k s : ℕ) :
    coverLoopS PB F INVM RD RW NP n DS k [] s = Nat.beq (Nat.shiftRight s 64) (ones NP) := by
  simp only [coverLoopS]

theorem coverLoopS_cons (PB : ℕ) (F : ℕ → ℕ) (INVM : ℕ) (RD RW : ℕ → ℕ) (NP n : ℕ)
    (DS : List ℕ) (k e : ℕ) (L : List ℕ) (s : ℕ) :
    coverLoopS PB F INVM RD RW NP n DS k (e :: L) s =
      Bool.rec (motive := fun _ => Bool)
        (sB (fld e (nat_lit 1) (ones (nat_lit 21))) (fun c =>
          sB (Nat.shiftRight e (nat_lit 22)) (fun p =>
            andB (andB (isStabOf RD n k (Nat.shiftRight c (nat_lit 1)))
                (Nat.beq (fld s (Nat.add p (nat_lit 64)) (nat_lit 1)) (nat_lit 1)))
              (sB (evP PB F (gWord INVM RW c) p) (fun x =>
                sB (Nat.xor (Nat.lor s (Nat.shiftLeft (nat_lit 1) (Nat.add x (nat_lit 64))))
                  (saltStep e)) (coverLoopS PB F INVM RD RW NP n DS k L))))))
        (sB (Nat.shiftRight e (nat_lit 1)) (fun f => sB (RD f) (fun d =>
          andB (andB (Nat.blt f n) (andB (isFact (dKind d))
              (andB (Nat.beq (dN1 d) k) (CFSG.KC.LaneChain.memN (dN2 d) DS))))
            (sB (evP PB F (wInv INVM (RW f)) (nat_lit 0)) (fun x =>
              sB (Nat.xor (Nat.lor s (Nat.shiftLeft (nat_lit 1) (Nat.add x (nat_lit 64))))
                (saltStep e)) (coverLoopS PB F INVM RD RW NP n DS k L))))))
        (Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1)) := by
  simp only [coverLoopS]

theorem coverLoopS_sound {PB : ℕ} {F : ℕ → ℕ} {INVM : ℕ} {RD RW : ℕ → ℕ} {NP n : ℕ}
    {DS : List ℕ} {k : ℕ} (L : List ℕ) :
    ∀ s, coverLoopS PB F INVM RD RW NP n DS k L s = true →
    (∀ q, s.testBit (q + 64) = true → Reached PB F INVM RD RW n DS k q) →
    ∀ p < NP, Reached PB F INVM RD RW n DS k p := by
  induction L with
  | nil =>
    intro s h hinit p hp
    rw [coverLoopS_nil] at h
    have hm : s >>> 64 = ones NP := Nat.eq_of_beq_eq_true h
    apply hinit p
    have hb : (s >>> 64).testBit p = true := by
      rw [hm]
      unfold ones
      change (1 <<< NP - 1).testBit p = true
      rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
      exact hp
    rwa [Nat.testBit_shiftRight, Nat.add_comm] at hb
  | cons e L ih =>
    intro s h hinit
    rw [coverLoopS_cons] at h
    simp only [sB_eq, CFSG.Certificates.TwDce.Core.brec_eq] at h
    split_ifs at h with he
    · simp only [kandB_iff] at h
      obtain ⟨⟨hf, hfa, hk, hnd⟩, h⟩ := h
      refine ih _ h (fun q hq => ?_)
      rcases (testBit_step _ _ _ _ (saltStep_lt e)).1 hq with hq | rfl
      · exact hinit q hq
      · exact ⟨_, Nat.blt_eq.mp hf, hfa, Nat.eq_of_beq_eq_true hk, memN_sound hnd, [],
          by simp, rfl⟩
    · simp only [kandB_iff] at h
      obtain ⟨⟨hst, hb⟩, h⟩ := h
      obtain ⟨f, hf, hfa, hk, hnd, cs, hcs, hq0⟩ :=
        hinit _ ((fld_s_one_iff _ _).1 (Nat.eq_of_beq_eq_true hb))
      refine ih _ h (fun q hq => ?_)
      rcases (testBit_step _ _ _ _ (saltStep_lt e)).1 hq with hq | rfl
      · exact hinit q hq
      · refine ⟨f, hf, hfa, hk, hnd, cs ++ [fld e 1 (ones 21)], fun c hc => ?_, ?_⟩
        · rcases List.mem_append.1 hc with hc | hc
          · exact hcs c hc
          · rw [List.mem_singleton.1 hc]
            have e2 : fld e 1 (ones 21) / 2 = Nat.shiftRight (fld e 1 (ones 21)) 1 := by
              change _ = _ >>> 1
              rw [Nat.shiftRight_eq_div_pow, pow_one]
            rw [e2]
            exact hst
        · rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← hq0]

theorem coverKS_sound {PB : ℕ} {F : ℕ → ℕ} {INVM : ℕ} {RD RW : ℕ → ℕ} {NP n : ℕ}
    {DS : List ℕ} {k : ℕ} {L : List ℕ} (h : coverKS PB F INVM RD RW NP n DS k L = true) :
    ∀ p < NP, Reached PB F INVM RD RW n DS k p := by
  refine coverLoopS_sound L _ h (fun q hq => absurd hq ?_)
  have h64 : 2 ^ 64 ≤ 2 ^ (q + 64) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : (9876543210123456789 : ℕ) < 2 ^ (q + 64) := lt_of_lt_of_le (by norm_num) h64
  rw [Nat.testBit_lt_two_pow h1]
  exact Bool.false_ne_true

theorem coverRangeS_sound {PB : ℕ} {F : ℕ → ℕ} {INVM : ℕ} {RD RW : ℕ → ℕ} {NP n : ℕ}
    {DS : List ℕ} {CV : List (List ℕ)} {a m : ℕ}
    (h : coverRangeS PB F INVM RD RW NP n DS CV a m = true) :
    ∀ j < m, ∀ p < NP,
      Reached PB F INVM RD RW n DS (CFSG.KC.LaneChain.getN DS (a + j)) p :=
  fun j hj => coverKS_sound (allRange_sound h j hj)

end CFSG.Certificates.TwDce3

end
