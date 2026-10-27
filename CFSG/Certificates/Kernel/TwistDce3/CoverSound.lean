module

public import Certificates.Data.Kernel.TwistDce3.Cover
public import CFSG.Certificates.Kernel.TwistDce3.Words
public import CFSG.Certificates.Kernel.TwistDce2.RelsSound
import CFSG.Certificates.Kernel.TwistDce.Core

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

private theorem fld_one_iff (m p : ℕ) : fld m p 1 = 1 ↔ m.testBit p = true := by
  unfold fld
  change (m >>> p) &&& 1 = 1 ↔ _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq,
    decide_eq_true_iff]

private theorem testBit_lor_shl (m x q : ℕ) :
    (Nat.lor m (Nat.shiftLeft 1 x)).testBit q = true ↔ m.testBit q = true ∨ q = x := by
  change (m ||| (1 <<< x)).testBit q = true ↔ _
  rw [Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow, Bool.or_eq_true,
    decide_eq_true_iff]
  exact or_congr_right eq_comm

theorem memN_sound {r : ℕ} : ∀ {G : List ℕ}, CFSG.KC.LaneChain.memN r G = true → r ∈ G
  | [], h => absurd h Bool.false_ne_true
  | y :: G, h => by
    change Bool.rec (motive := fun _ => Bool) (CFSG.KC.LaneChain.memN r G) true (Nat.beq r y) =
      true at h
    cases hb : Nat.beq r y
    · rw [hb] at h
      exact List.mem_cons_of_mem _ (memN_sound h)
    · rw [Nat.eq_of_beq_eq_true hb]
      exact List.mem_cons_self

private theorem natRec_and {P : ℕ → Bool} : ∀ n,
    (Nat.rec (motive := fun _ => Bool) true (fun c acc => andB acc (P c)) n) = true →
    ∀ c < n, P c = true := by
  intro n
  induction n with
  | zero => intro _ c hc; exact absurd hc (Nat.not_lt_zero _)
  | succ n ih =>
    intro h c hc
    change andB _ (P n) = true at h
    rw [kandB_iff] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
    · exact ih h.1 c hc
    · exact h.2

theorem allRange_sound {P : ℕ → Bool} {a m : ℕ} (h : allRange P a m = true) :
    ∀ j < m, P (a + j) = true :=
  natRec_and (P := fun j => P (Nat.add a j)) m h

noncomputable def coverLoop (PB : ℕ) (F : ℕ → ℕ) (INVM : ℕ) (RD RW : ℕ → ℕ) (NP n : ℕ)
    (DS : List ℕ) (k : ℕ) (L : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun mask => Nat.beq mask (ones NP))
    (fun e _ ih mask =>
      Bool.rec (motive := fun _ => Bool)
        (sB (fld e (nat_lit 1) (ones (nat_lit 21))) (fun c =>
          sB (Nat.shiftRight e (nat_lit 22)) (fun p =>
            andB (andB (isStabOf RD n k (Nat.shiftRight c (nat_lit 1)))
                (Nat.beq (fld mask p (nat_lit 1)) (nat_lit 1)))
              (sB (evP PB F (gWord INVM RW c) p) (fun x =>
                sB (Nat.lor mask (Nat.shiftLeft (nat_lit 1) x)) ih)))))
        (sB (Nat.shiftRight e (nat_lit 1)) (fun f => sB (RD f) (fun d =>
          andB (andB (Nat.blt f n) (andB (isFact (dKind d))
              (andB (Nat.beq (dN1 d) k) (CFSG.KC.LaneChain.memN (dN2 d) DS))))
            (sB (evP PB F (wInv INVM (RW f)) (nat_lit 0)) (fun x =>
              sB (Nat.lor mask (Nat.shiftLeft (nat_lit 1) x)) ih)))))
        (Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1)))
    L

theorem coverLoop_cons (PB : ℕ) (F : ℕ → ℕ) (INVM : ℕ) (RD RW : ℕ → ℕ) (NP n : ℕ)
    (DS : List ℕ) (k e : ℕ) (L : List ℕ) (mask : ℕ) :
    coverLoop PB F INVM RD RW NP n DS k (e :: L) mask =
      Bool.rec (motive := fun _ => Bool)
        (sB (fld e (nat_lit 1) (ones (nat_lit 21))) (fun c =>
          sB (Nat.shiftRight e (nat_lit 22)) (fun p =>
            andB (andB (isStabOf RD n k (Nat.shiftRight c (nat_lit 1)))
                (Nat.beq (fld mask p (nat_lit 1)) (nat_lit 1)))
              (sB (evP PB F (gWord INVM RW c) p) (fun x =>
                sB (Nat.lor mask (Nat.shiftLeft (nat_lit 1) x))
                  (coverLoop PB F INVM RD RW NP n DS k L))))))
        (sB (Nat.shiftRight e (nat_lit 1)) (fun f => sB (RD f) (fun d =>
          andB (andB (Nat.blt f n) (andB (isFact (dKind d))
              (andB (Nat.beq (dN1 d) k) (CFSG.KC.LaneChain.memN (dN2 d) DS))))
            (sB (evP PB F (wInv INVM (RW f)) (nat_lit 0)) (fun x =>
              sB (Nat.lor mask (Nat.shiftLeft (nat_lit 1) x))
                (coverLoop PB F INVM RD RW NP n DS k L))))))
        (Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1)) := by
  simp only [coverLoop]

@[expose] def Reached (PB : ℕ) (F : ℕ → ℕ) (INVM : ℕ) (RD RW : ℕ → ℕ) (n : ℕ) (DS : List ℕ) (k q : ℕ) :
    Prop :=
  ∃ f < n, isFact (dKind (RD f)) = true ∧ dN1 (RD f) = k ∧ dN2 (RD f) ∈ DS ∧
    ∃ cs : List ℕ, (∀ c ∈ cs, isStabOf RD n k (c / 2) = true) ∧
      q = cs.foldl (fun q c => evP PB F (gWord INVM RW c) q) (evP PB F (wInv INVM (RW f)) 0)

theorem coverLoop_sound {PB : ℕ} {F : ℕ → ℕ} {INVM : ℕ} {RD RW : ℕ → ℕ} {NP n : ℕ}
    {DS : List ℕ} {k : ℕ} (L : List ℕ) :
    ∀ mask, coverLoop PB F INVM RD RW NP n DS k L mask = true →
    (∀ q, mask.testBit q = true → Reached PB F INVM RD RW n DS k q) →
    ∀ p < NP, Reached PB F INVM RD RW n DS k p := by
  induction L with
  | nil =>
    intro mask h hinit p hp
    have hm : mask = ones NP := Nat.eq_of_beq_eq_true h
    apply hinit p
    rw [hm]
    unfold ones
    change (1 <<< NP - 1).testBit p = true
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
    exact hp
  | cons e L ih =>
    intro mask h hinit
    rw [coverLoop_cons] at h
    simp only [sB_eq, CFSG.Certificates.TwDce.Core.brec_eq] at h
    split_ifs at h with he
    · simp only [kandB_iff] at h
      obtain ⟨⟨hf, hfa, hk, hnd⟩, h⟩ := h
      refine ih _ h (fun q hq => ?_)
      rcases (testBit_lor_shl _ _ _).1 hq with hq | rfl
      · exact hinit q hq
      · exact ⟨_, Nat.blt_eq.mp hf, hfa, Nat.eq_of_beq_eq_true hk, memN_sound hnd, [],
          by simp, rfl⟩
    · simp only [kandB_iff] at h
      obtain ⟨⟨hst, hb⟩, h⟩ := h
      obtain ⟨f, hf, hfa, hk, hnd, cs, hcs, hq0⟩ :=
        hinit _ ((fld_one_iff _ _).1 (Nat.eq_of_beq_eq_true hb))
      refine ih _ h (fun q hq => ?_)
      rcases (testBit_lor_shl _ _ _).1 hq with hq | rfl
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

theorem coverK_sound {PB : ℕ} {F : ℕ → ℕ} {INVM : ℕ} {RD RW : ℕ → ℕ} {NP n : ℕ} {DS : List ℕ}
    {k : ℕ} {L : List ℕ} (h : coverK PB F INVM RD RW NP n DS k L = true) :
    ∀ p < NP, Reached PB F INVM RD RW n DS k p :=
  coverLoop_sound L 0 h (fun q hq => absurd hq (by rw [Nat.zero_testBit]; exact Bool.false_ne_true))

theorem coverRange_sound {PB : ℕ} {F : ℕ → ℕ} {INVM : ℕ} {RD RW : ℕ → ℕ} {NP n : ℕ}
    {DS : List ℕ} {CV : List (List ℕ)} {a m : ℕ} (h : coverRange PB F INVM RD RW NP n DS CV a m = true) :
    ∀ j < m, ∀ p < NP,
      Reached PB F INVM RD RW n DS (CFSG.KC.LaneChain.getN DS (a + j)) p :=
  fun j hj => coverK_sound (allRange_sound h j hj)

theorem lettersOK_sound {PB : ℕ} {F : ℕ → ℕ} {INVM NL NP : ℕ}
    (h : lettersOK PB F INVM NL NP = true) :
    ∀ c < NL, ivL INVM c < NL ∧ ∀ x < NP, fieldAt PB (F c) x < NP ∧
      fieldAt PB (F (ivL INVM c)) (fieldAt PB (F c) x) = x := by
  intro c hc
  have h1 := natRec_and (P := fun c => andB (Nat.blt (ivL INVM c) NL)
    (Nat.rec (motive := fun _ => Bool) true
      (fun x acc2 => andB acc2 (sB (fieldAt PB (F c) x) (fun y =>
        andB (Nat.blt y NP) (Nat.beq (fieldAt PB (F (ivL INVM c)) y) x)))) NP)) NL h c hc
  rw [kandB_iff, Nat.blt_eq] at h1
  refine ⟨h1.1, fun x hx => ?_⟩
  have h2 := natRec_and (P := fun x => sB (fieldAt PB (F c) x) (fun y =>
    andB (Nat.blt y NP) (Nat.beq (fieldAt PB (F (ivL INVM c)) y) x))) NP h1.2 x hx
  rw [sB_eq, kandB_iff, Nat.blt_eq] at h2
  exact ⟨h2.1, Nat.eq_of_beq_eq_true h2.2⟩

theorem fixAll_sound {PB : ℕ} {F : ℕ → ℕ} {NP v : ℕ} (h : fixAll PB F NP v = true) :
    ∀ x < NP, evP PB F v x = x := fun x hx =>
  Nat.eq_of_beq_eq_true (natRec_and (P := fun x => Nat.beq (evP PB F v x) x) NP h x hx)

theorem relsOK_sound {PB : ℕ} {F : ℕ → ℕ} {NP : ℕ} : ∀ {ws : List (List ℕ)},
    relsOK PB F NP ws = true → (∀ w ∈ ws, w.length < 2 ^ 32) →
    ∀ w ∈ ws, (∀ c ∈ w, c < 12) ∧ ∀ p < NP, w.foldl (fun q c => fieldAt PB (F c) q) p = p
  | [], _, _ => fun _ hw => absurd hw List.not_mem_nil
  | w :: ws, h, hl => by
    change andB (andB (codesOK w) (sB (codesW w) (fun v => fixAll PB F NP v)))
      (relsOK PB F NP ws) = true at h
    rw [kandB_iff, kandB_iff, sB_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · have hc := CFSG.Certificates.TwDce2.Rels.codesOK_sound h1
      obtain ⟨-, -, hlst⟩ := CFSG.Certificates.TwDce2.Rels.codesW_spec v
        (fun c hc' => by have := hc c hc'; omega) (hl v List.mem_cons_self)
      refine ⟨hc, fun p hp => ?_⟩
      have := fixAll_sound h2 p hp
      rwa [CFSG.Certificates.TwDce3.Words.evP_eq, hlst] at this
    · exact relsOK_sound h3 (fun u hu => hl u (List.mem_cons_of_mem _ hu)) v hv

theorem repackOK_sound {PB : ℕ} {F FB : ℕ → ℕ} {NL NQ : ℕ} (h : repackOK PB F FB NL NQ = true) :
    ∀ c < NL, ∀ x < NQ, fieldAt 11 (FB c) x = fieldAt PB (F c) x := by
  intro c hc x hx
  have h2 : Nat.beq (fieldAt 11 (FB (0 + c)) (0 + x)) (fieldAt PB (F (0 + c)) (0 + x)) = true :=
    allRange_sound (allRange_sound h c hc) x hx
  simp only [Nat.zero_add] at h2
  exact Nat.eq_of_beq_eq_true h2

theorem stabRange_sound {FB : ℕ → ℕ} {INVM NQ : ℕ} {RD RW : ℕ → ℕ} {n : ℕ} {DS : List ℕ}
    {CG : List (List ℕ)} {CW CB CS CT : List (List (List ℕ))} {CN : List ℕ} {a m : ℕ}
    (h : stabRange FB INVM NQ RD RW n DS CG CW CB CS CT CN a m = true) :
    ∀ j < m, stabOK FB INVM NQ RD RW n (CFSG.KC.LaneChain.getN DS (a + j))
      (CFSG.KC.LaneChain.getL CG (a + j)) (getLL CW (a + j)) (getLL CB (a + j))
      (getLL CS (a + j)) (getLL CT (a + j)) (CFSG.KC.LaneChain.getN CN (a + j)) = true :=
  fun j hj => allRange_sound h j hj

end CFSG.Certificates.TwDce3

end
