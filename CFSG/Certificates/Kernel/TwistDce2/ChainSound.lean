module

public import Certificates.Data.Kernel.TwistDce2.Cover
public import CFSG.Certificates.Kernel.TwistDce.Sound
import CFSG.Certificates.Kernel.TwistDce2.ChainB
import CFSG.Certificates.Kernel.TwistDce.Core

public section

namespace CFSG.Certificates.TwDce2

open CFSG.KC.TwDce2 CFSG.Certificates.CosetEnumeration CFSG.KC.YModel
  CFSG.Certificates.TwDce

private theorem fld_one_iff (m p : ℕ) : CFSG.KC.TwDce.fld m p 1 = 1 ↔ m.testBit p = true := by
  unfold CFSG.KC.TwDce.fld
  change (m >>> p) &&& 1 = 1 ↔ _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq,
    decide_eq_true_iff]

private theorem testBit_lor_shl (m x q : ℕ) :
    (Nat.lor m (Nat.shiftLeft 1 x)).testBit q = true ↔ m.testBit q = true ∨ q = x := by
  change (m ||| (1 <<< x)).testBit q = true ↔ _
  rw [Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow, Bool.or_eq_true,
    decide_eq_true_iff]
  exact or_congr_right eq_comm

noncomputable def coverLoop (F : ℕ → ℕ) (INVM NP : ℕ) (RD RW : ℕ → ℕ) (n ND k : ℕ)
    (L : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun mask => Nat.beq mask (CFSG.KC.TwDce.ones NP))
    (fun e _ ih mask =>
      Bool.rec (motive := fun _ => Bool)
        (CFSG.KC.TwDce.sB (CFSG.KC.TwDce.fld e (nat_lit 1) (CFSG.KC.TwDce.ones (nat_lit 21)))
          (fun c => CFSG.KC.TwDce.sB (Nat.shiftRight e (nat_lit 22)) (fun p =>
            CFSG.KC.andB (CFSG.KC.andB (isStabOf RD n k (Nat.shiftRight c (nat_lit 1)))
                (Nat.beq (CFSG.KC.TwDce.fld mask p (nat_lit 1)) (nat_lit 1)))
              (CFSG.KC.TwDce.sB (evP F (gWord INVM RW c) p) (fun x =>
                CFSG.KC.TwDce.sB (Nat.lor mask (Nat.shiftLeft (nat_lit 1) x)) ih)))))
        (CFSG.KC.TwDce.sB (Nat.shiftRight e (nat_lit 1)) (fun f =>
          CFSG.KC.TwDce.sB (RD f) (fun d =>
          CFSG.KC.andB (CFSG.KC.andB (Nat.blt f n) (CFSG.KC.andB (isFact (dKind d))
              (CFSG.KC.andB (Nat.beq (dN1 d) k) (Nat.blt (dN2 d) ND))))
            (CFSG.KC.TwDce.sB (evP F (wInv INVM (RW f)) (nat_lit 0)) (fun x =>
              CFSG.KC.TwDce.sB (Nat.lor mask (Nat.shiftLeft (nat_lit 1) x)) ih)))))
        (Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1)))
    L

theorem coverLoop_cons (F : ℕ → ℕ) (INVM NP : ℕ) (RD RW : ℕ → ℕ) (n ND k e : ℕ) (L : List ℕ)
    (mask : ℕ) : coverLoop F INVM NP RD RW n ND k (e :: L) mask =
      Bool.rec (motive := fun _ => Bool)
        (CFSG.KC.TwDce.sB (CFSG.KC.TwDce.fld e (nat_lit 1) (CFSG.KC.TwDce.ones (nat_lit 21)))
          (fun c => CFSG.KC.TwDce.sB (Nat.shiftRight e (nat_lit 22)) (fun p =>
            CFSG.KC.andB (CFSG.KC.andB (isStabOf RD n k (Nat.shiftRight c (nat_lit 1)))
                (Nat.beq (CFSG.KC.TwDce.fld mask p (nat_lit 1)) (nat_lit 1)))
              (CFSG.KC.TwDce.sB (evP F (gWord INVM RW c) p) (fun x =>
                CFSG.KC.TwDce.sB (Nat.lor mask (Nat.shiftLeft (nat_lit 1) x))
                  (coverLoop F INVM NP RD RW n ND k L))))))
        (CFSG.KC.TwDce.sB (Nat.shiftRight e (nat_lit 1)) (fun f =>
          CFSG.KC.TwDce.sB (RD f) (fun d =>
          CFSG.KC.andB (CFSG.KC.andB (Nat.blt f n) (CFSG.KC.andB (isFact (dKind d))
              (CFSG.KC.andB (Nat.beq (dN1 d) k) (Nat.blt (dN2 d) ND))))
            (CFSG.KC.TwDce.sB (evP F (wInv INVM (RW f)) (nat_lit 0)) (fun x =>
              CFSG.KC.TwDce.sB (Nat.lor mask (Nat.shiftLeft (nat_lit 1) x))
                (coverLoop F INVM NP RD RW n ND k L))))))
        (Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1)) := by
  simp only [coverLoop]

theorem coverLoop_sound {F : ℕ → ℕ} {INVM NP : ℕ} {RD RW : ℕ → ℕ} {n ND k : ℕ} (L : List ℕ) :
    ∀ mask, coverLoop F INVM NP RD RW n ND k L mask = true →
    (∀ q, mask.testBit q = true → ∃ f < n, isFact (dKind (RD f)) = true ∧
      dN1 (RD f) = k ∧ dN2 (RD f) < ND ∧
      ∃ cs : List ℕ, (∀ c ∈ cs, isStabOf RD n k (c / 2) = true) ∧
        q = cs.foldl (fun q c => evP F (gWord INVM RW c) q) (evP F (wInv INVM (RW f)) 0)) →
    ∀ p < NP, ∃ f < n, isFact (dKind (RD f)) = true ∧ dN1 (RD f) = k ∧ dN2 (RD f) < ND ∧
      ∃ cs : List ℕ, (∀ c ∈ cs, isStabOf RD n k (c / 2) = true) ∧
        p = cs.foldl (fun q c => evP F (gWord INVM RW c) q) (evP F (wInv INVM (RW f)) 0) := by
  induction L with
  | nil =>
    intro mask h hinit
    intro p hp
    have hm : mask = CFSG.KC.TwDce.ones NP := Nat.eq_of_beq_eq_true h
    apply hinit p
    rw [hm]
    unfold CFSG.KC.TwDce.ones
    change (1 <<< NP - 1).testBit p = true
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
    exact hp
  | cons e L ih =>
    intro mask h hinit
    rw [coverLoop_cons] at h
    simp only [CFSG.Certificates.TwDce.Words.sB_eq, CFSG.Certificates.TwDce.Core.brec_eq] at h
    split_ifs at h with he
    · simp only [CFSG.Certificates.TwDce2.Words.kandB_iff] at h
      obtain ⟨⟨hf, hfa, hk, hnd⟩, h⟩ := h
      refine ih _ h (fun q hq => ?_)
      rcases (testBit_lor_shl _ _ _).1 hq with hq | rfl
      · exact hinit q hq
      · exact ⟨_, Nat.blt_eq.mp hf, hfa, Nat.eq_of_beq_eq_true hk, Nat.blt_eq.mp hnd, [],
          by simp, rfl⟩
    · simp only [CFSG.Certificates.TwDce2.Words.kandB_iff] at h
      obtain ⟨⟨hst, hb⟩, h⟩ := h
      obtain ⟨f, hf, hfa, hk, hnd, cs, hcs, hq0⟩ :=
        hinit _ ((fld_one_iff _ _).1 (Nat.eq_of_beq_eq_true hb))
      refine ih _ h (fun q hq => ?_)
      rcases (testBit_lor_shl _ _ _).1 hq with hq | rfl
      · exact hinit q hq
      · refine ⟨f, hf, hfa, hk, hnd, cs ++ [CFSG.KC.TwDce.fld e 1 (CFSG.KC.TwDce.ones 21)],
          fun c hc => ?_, ?_⟩
        · rcases List.mem_append.1 hc with hc | hc
          · exact hcs c hc
          · rw [List.mem_singleton.1 hc]
            have e2 : CFSG.KC.TwDce.fld e 1 (CFSG.KC.TwDce.ones 21) / 2 =
                Nat.shiftRight (CFSG.KC.TwDce.fld e 1 (CFSG.KC.TwDce.ones 21)) 1 := by
              change _ = _ >>> 1
              rw [Nat.shiftRight_eq_div_pow, pow_one]
            rw [e2]
            exact hst
        · rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← hq0]

theorem coverK_sound {F : ℕ → ℕ} {INVM NP : ℕ} {RD RW : ℕ → ℕ} {n ND k : ℕ} {L : List ℕ}
    (h : coverK F INVM NP RD RW n ND k L = true) :
    ∀ p < NP, ∃ f < n, isFact (dKind (RD f)) = true ∧ dN1 (RD f) = k ∧ dN2 (RD f) < ND ∧
      ∃ cs : List ℕ, (∀ c ∈ cs, isStabOf RD n k (c / 2) = true) ∧
        p = cs.foldl (fun q c => evP F (gWord INVM RW c) q) (evP F (wInv INVM (RW f)) 0) :=
  coverLoop_sound L 0 h (fun q hq => absurd hq (by rw [Nat.zero_testBit]; exact Bool.false_ne_true))

@[expose] def chainLens (L : List ℕ) : List (List ℕ) → List ℕ
  | [] => L
  | w :: W => chainLens ((w.map fun r => L.getD (L.length - 1 - r) 0).sum :: L) W

theorem chainB_sound {F : ℕ → ℕ} {INVM NP : ℕ} {RW : ℕ → ℕ} {G : Type*} [Group G] (x : ℕ → G)
    (pt : G → ℕ → ℕ) (hpt1 : ∀ p, pt 1 p = p) (hptm : ∀ a b p, pt (a * b) p = pt b (pt a p))
    (hF : ∀ c < 12, ∀ p < NP, fieldAt 11 (F c) p < NP)
    (hx : ∀ c < 12, ∀ p < NP, fieldAt 11 (F c) p = pt (x c) p)
    (K : Subgroup G) [Finite K] {CG : List ℕ} {W Bs Gs Ts : List (List ℕ)} {tot : ℕ}
    (hCG : ∀ c ∈ CG, wBelow 12 (gWord INVM RW c) = true ∧ wVal x (gWord INVM RW c) ∈ K)
    (hlen : ∀ m ∈ chainLens ((gRegs INVM RW CG).map fun r => CFSG.KC.TwDce.wLen (r / 2)) W,
      m < 2 ^ 32)
    (h : chainB F NP W Bs Gs Ts (gRegs INVM RW CG) tot = true) :
    tot * Nat.card {g : G // g ∈ K ∧
      ∀ b ∈ Bs, pt g (CFSG.KC.LaneChain.colDat 11 b / 2) = CFSG.KC.LaneChain.colDat 11 b / 2} ≤
      Nat.card K := by
  have e : ∀ (W : List (List ℕ)) (L : List ℕ), chainLens L W = ChainB.chainLens L W := by
    intro W
    induction W with
    | nil => intro L; rfl
    | cons w W ih => intro L; exact ih _
  exact ChainB.chainB_sound' x pt hpt1 hptm hF hx K hCG (fun m hm => hlen m (by rw [e]; exact hm)) h

end CFSG.Certificates.TwDce2

end
