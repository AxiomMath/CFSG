module

public import Certificates.Data.Kernel.SporSch.RuTreeK
public import CFSG.Certificates.Kernel.BenesSound
import Mathlib.Data.Nat.Find

public section

namespace CFSG.KS.RuTree

open CFSG.KLC.Fi22

theorem andB_iff' {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem orB_iff' {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem bnat (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem bbool (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem rngK_spec {a n : Nat} {f : Nat → Bool} (h : rngK a n f = true) :
    ∀ c, a ≤ c → c < a + n → f c = true := by
  induction n with
  | zero => intro c h1 h2; omega
  | succ n ih =>
    change andB (f (Nat.add a n)) (rngK a n f) = true at h
    obtain ⟨h1, h2⟩ := andB_iff'.1 h
    intro c hc1 hc2
    rcases Nat.lt_or_ge c (a + n) with hc | hc
    · exact ih h2 c hc1 hc
    · have : c = a + n := by omega
      subst this
      exact h1

theorem stage_zero (m d : Nat) : stage 0 m d = 0 := by
  have e1 : Nat.land (Nat.xor 0 (Nat.shiftRight 0 d)) m = 0 := by
    change (0 ^^^ (0 >>> d)) &&& m = 0
    simp
  unfold stage sN
  rw [e1]
  change 0 ^^^ (0 ||| (0 <<< d)) = 0
  simp

theorem iterN_zero (c : Nat) (f : Nat → Nat → Nat) (hf : ∀ s, f s 0 = 0) : iterN c f 0 = 0 := by
  unfold iterN
  suffices ∀ j, (Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun i ih s => sN (f (Nat.sub (Nat.sub c 1) i) s) ih) j) 0 = 0 from this c
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    change sN (f (Nat.sub (Nat.sub c 1) j) 0) _ = 0
    rw [hf]
    exact ih

theorem mv_zero (N0 N1 e : Nat) : mv N0 N1 e 0 = 0 := by
  unfold mv applyNW
  rw [bnat]
  split <;> exact iterN_zero _ _ (fun s => stage_zero _ _)

variable {N0 N1 F0 : Nat} {PL FC T D : Nat → Nat} {M B N : Nat} {G : Nat → Nat → Prop}

theorem udK_good (hG0 : G 0 F0) (hpar : ∀ c, 1 ≤ c → c < N → PL c >>> 4 < c)
    (hstep : ∀ c, 1 ≤ c → c < N → ∀ x, G (PL c >>> 4) x → G c (mv N0 N1 (PL c) x)) :
    ∀ f c, c < N → udK N0 N1 F0 PL f c ≠ 0 → G c (udK N0 N1 F0 PL f c) := by
  intro f
  induction f with
  | zero =>
    intro c _ h
    change Bool.rec (motive := fun _ => Nat) (nat_lit 0) F0 (Nat.beq c (nat_lit 0)) ≠ 0 at h
    change G c (Bool.rec (motive := fun _ => Nat) (nat_lit 0) F0 (Nat.beq c (nat_lit 0)))
    rw [bnat] at h ⊢
    split at h
    · rename_i hc
      simp only [hc, ↓reduceIte]
      rw [Nat.eq_of_beq_eq_true hc]
      exact hG0
    · exact absurd rfl h
  | succ f ih =>
    intro c hc h
    change Bool.rec (motive := fun _ => Nat)
      ((fun pl => mv N0 N1 pl (udK N0 N1 F0 PL f (Nat.shiftRight pl (nat_lit 4)))) (PL c)) F0
      (Nat.beq c (nat_lit 0)) ≠ 0 at h
    change G c (Bool.rec (motive := fun _ => Nat)
      ((fun pl => mv N0 N1 pl (udK N0 N1 F0 PL f (Nat.shiftRight pl (nat_lit 4)))) (PL c)) F0
      (Nat.beq c (nat_lit 0)))
    rw [bnat] at h ⊢
    split at h
    · rename_i h0
      simp only [h0, ↓reduceIte]
      rw [Nat.eq_of_beq_eq_true h0]
      exact hG0
    · rename_i h0
      simp only [h0, Bool.false_eq_true, ↓reduceIte]
      have hc0 : c ≠ 0 := fun e => h0 (by rw [e]; rfl)
      have hp := hpar c (by omega) hc
      dsimp only at h ⊢
      have hu : udK N0 N1 F0 PL f (PL c >>> 4) ≠ 0 := by
        intro e
        apply h
        change mv N0 N1 (PL c) (udK N0 N1 F0 PL f (PL c >>> 4)) = 0
        rw [e, mv_zero]
      exact hstep c (by omega) hc _ (ih _ (by omega) hu)

theorem visitK_succ {f j x : Nat} (h : visitK N0 N1 PL FC T D M B (f + 1) j x = true) :
    chkK T D M B j x = true ∧ ∀ c, fcK FC j ≤ c → c < fcK FC j + ncK FC j →
      PL c >>> 4 = j ∧ PL c % 16 < 2 ∧
        (cutK FC c = false → visitK N0 N1 PL FC T D M B f c (mv N0 N1 (PL c) x) = true) := by
  change andB (chkK T D M B j x) (rngK (fcK FC j) (ncK FC j) (fun c => (fun pl =>
        andB (Nat.beq (Nat.shiftRight pl (nat_lit 4)) j)
          (andB (Nat.blt (Nat.land pl (nat_lit 15)) (nat_lit 2))
            (Bool.rec (motive := fun _ => Bool) (visitK N0 N1 PL FC T D M B f c (mv N0 N1 pl x)) true
              (cutK FC c)))) (PL c))) = true at h
  obtain ⟨h1, h2⟩ := andB_iff'.1 h
  refine ⟨h1, fun c hc1 hc2 => ?_⟩
  have h3 := rngK_spec h2 c hc1 hc2
  dsimp only at h3
  obtain ⟨h4, h5⟩ := andB_iff'.1 h3
  obtain ⟨h7, h6⟩ := andB_iff'.1 h5
  have e15 : Nat.land (PL c) 15 = PL c % 16 := Nat.and_two_pow_sub_one_eq_mod (PL c) 4
  refine ⟨Nat.eq_of_beq_eq_true h4, by rw [← e15]; exact Nat.blt_eq.mp h7, fun hcut => ?_⟩
  rw [hcut] at h6
  exact h6

theorem visitK_zero {j x : Nat} : visitK N0 N1 PL FC T D M B 0 j x = false := rfl

theorem owner (h0 : fcK FC 0 = 1) (hN : fcK FC N = N) (hpart : ∀ j < N, partK FC j = true)
    {j : Nat} (hj1 : 1 ≤ j) (hjN : j < N) :
    ∃ h, h < j ∧ fcK FC h ≤ j ∧ j < fcK FC h + ncK FC h := by
  have hex : ∃ k, j < fcK FC (k + 1) := ⟨N - 1, by rw [Nat.sub_add_cancel (by omega), hN]; exact hjN⟩
  obtain ⟨h, hh, hmin⟩ : ∃ h, j < fcK FC (h + 1) ∧ ∀ m < h, ¬ j < fcK FC (m + 1) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hle : h ≤ N - 1 := by
    refine Nat.le_of_not_lt fun hl => hmin (N - 1) hl ?_
    rw [Nat.sub_add_cancel (by omega), hN]
    exact hjN
  have hfc : fcK FC h ≤ j := by
    rcases Nat.eq_zero_or_pos h with e | e
    · rw [e, h0]
      exact hj1
    · have := hmin (h - 1) (by omega)
      rw [Nat.sub_add_cancel e] at this
      omega
  have hp := hpart h (by omega)
  unfold partK at hp
  obtain ⟨h1, h2⟩ := andB_iff'.1 hp
  have e1 : fcK FC (h + 1) = fcK FC h + ncK FC h := Nat.eq_of_beq_eq_true h1
  have hh' : j < fcK FC h + ncK FC h := by rw [← e1]; exact hh
  rcases orB_iff'.1 h2 with h3 | h3
  · have h4 : ncK FC h = 0 := Nat.eq_of_beq_eq_true h3
    rw [h4] at hh'
    omega
  · exact ⟨h, by have := Nat.blt_eq.mp h3; omega, hfc, hh'⟩

theorem visit_sound (hG0 : G 0 F0)
    (hstep : ∀ c, 1 ≤ c → c < N → PL c >>> 4 < c → PL c % 16 < 2 → ∀ x, G (PL c >>> 4) x →
      G c (mv N0 N1 (PL c) x))
    (h0 : fcK FC 0 = 1) (hN : fcK FC N = N) (hpart : ∀ j < N, partK FC j = true)
    (hcut0 : cutK FC 0 = true)
    (hroot : ∀ r < N, cutK FC r = true → rootK N0 N1 F0 PL FC T D M B r = true) :
    ∀ c < N, (1 ≤ c → PL c >>> 4 < c ∧ PL c % 16 < 2) ∧
      ∃ x, G c x ∧ ∃ f, visitK N0 N1 PL FC T D M B (f + 1) c x = true := by
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    intro hc
    have side : 1 ≤ c → PL c >>> 4 < c ∧ PL c % 16 < 2 ∧ ∃ j < c, ∃ x, G j x ∧ ∃ f,
        visitK N0 N1 PL FC T D M B (f + 1) j x = true ∧ PL c >>> 4 = j ∧
        (cutK FC c = false → visitK N0 N1 PL FC T D M B f c (mv N0 N1 (PL c) x) = true) := by
      intro hc1
      obtain ⟨j, hj, hj1, hj2⟩ := owner h0 hN hpart hc1 hc
      obtain ⟨-, x, hx, f, hv⟩ := ih j hj (by omega)
      obtain ⟨-, hch⟩ := visitK_succ hv
      obtain ⟨e1, e2, e3⟩ := hch c hj1 hj2
      exact ⟨by rw [e1]; exact hj, e2, j, hj, x, hx, f, hv, e1, e3⟩
    refine ⟨fun h1 => ⟨(side h1).1, (side h1).2.1⟩, ?_⟩
    cases hcut : cutK FC c with
    | true =>
      have hr := hroot c hc hcut
      unfold rootK at hr
      obtain ⟨h1, h2⟩ := andB_iff'.1 hr
      have hu : udK N0 N1 F0 PL 45 c ≠ 0 := by
        intro e
        rw [e] at h1
        exact absurd h1 (by decide)
      have hpar : ∀ a, 1 ≤ a → a < c + 1 → PL a >>> 4 < a ∧ PL a % 16 < 2 := by
        intro a ha1 ha2
        rcases Nat.lt_or_ge a c with ha | ha
        · exact (ih a ha (by omega)).1 ha1
        · have : a = c := by omega
          subst this
          exact ⟨(side ha1).1, (side ha1).2.1⟩
      have hG := udK_good (N := c + 1) hG0 (fun a ha1 ha2 => (hpar a ha1 ha2).1)
        (fun a ha1 ha2 x hx => hstep a ha1 (by omega) (hpar a ha1 ha2).1 (hpar a ha1 ha2).2 x hx)
        45 c (by omega) hu
      exact ⟨_, hG, 44, h2⟩
    | false =>
      have hc1 : 1 ≤ c := by
        rcases Nat.eq_zero_or_pos c with e | e
        · subst e
          rw [hcut0] at hcut
          exact absurd hcut (by decide)
        · exact e
      obtain ⟨hp, hl, j, -, x, hx, f, -, e1, hv⟩ := side hc1
      have hv' := hv hcut
      cases f with
      | zero => exact absurd hv' (by rw [visitK_zero]; decide)
      | succ f =>
        refine ⟨_, hstep c hc1 hc hp hl x (by rw [e1]; exact hx), f, hv'⟩

theorem chkK_hi {j x y : Nat} (h : x >>> 4096 = y >>> 4096) :
    chkK T D M B j x = chkK T D M B j y := by
  unfold chkK hk
  change Nat.beq (tabK T 20 (slotK D M B ((x >>> 4096) % 2305843009213693951))) j =
    Nat.beq (tabK T 20 (slotK D M B ((y >>> 4096) % 2305843009213693951))) j
  rw [h]

theorem chk_inj {j j' x x' : Nat} (h : chkK T D M B j x = true) (h' : chkK T D M B j' x' = true)
    (e : x >>> 4096 = x' >>> 4096) : j = j' := by
  rw [chkK_hi (T := T) (D := D) (M := M) (B := B) (j := j) e] at h
  unfold chkK at h h'
  exact (Nat.eq_of_beq_eq_true h).symm.trans (Nat.eq_of_beq_eq_true h')

@[expose] noncomputable def mvU (N0 N1 e y : Nat) : Nat :=
  if e % 2 = 1 then applyNW N1 1 y else applyNW N0 1 y

theorem mv_eq (N0 N1 e x : Nat) :
    mv N0 N1 e x = if e % 2 = 1 then applyNW N1 R2 x else applyNW N0 R2 x := by
  unfold mv
  change Bool.rec (motive := fun _ => Nat) (applyNW N0 R2 x) (applyNW N1 R2 x)
    (Nat.beq (e &&& 1) 1) = _
  rw [bnat, show e &&& 1 = e % 2 from Nat.and_two_pow_sub_one_eq_mod e 1]
  by_cases h : e % 2 = 1
  · rw [h]
    rfl
  · have h' : Nat.beq (e % 2) 1 = false := by
      cases hb : Nat.beq (e % 2) 1
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h
    simp only [h', h, Bool.false_eq_true, ↓reduceIte]

theorem R2_eq : R2 = maskN (4096 * 2) / M4096 := by decide

theorem applyNW_hi {NW : Nat} (h : nwValid NW = true) (x : Nat) :
    applyNW NW R2 x >>> 4096 = applyNW NW 1 (x >>> 4096) := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_shiftRight]
  rcases Nat.lt_or_ge p 4096 with hp | hp
  · have A := (CFSG.KC.Benes.testBit_applyNW h R2_eq x).1 1 (by decide) p hp
    have B := (CFSG.KC.Benes.testBit_applyNW h CFSG.KC.Benes.one_eq_rep (x >>> 4096)).1 0
      (by decide) p hp
    rw [Nat.mul_one] at A
    rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add, Nat.testBit_shiftRight] at B
    rw [A, B]
  · have A := (CFSG.KC.Benes.testBit_applyNW h R2_eq x).2 (4096 + p) (by omega)
    have B := (CFSG.KC.Benes.testBit_applyNW h CFSG.KC.Benes.one_eq_rep (x >>> 4096)).2 p
      (by omega)
    rw [A, B, Nat.testBit_shiftRight]

theorem applyNW_img {NW : Nat} (h : nwValid NW = true) {g : Nat → Nat}
    (hg : ∀ s < 4096, CFSG.KC.Benes.nwInv NW s = if s < 4060 then g s else s) (hg' : ∀ s < 4060, g s < 4060)
    {S : Nat → Prop} (hS : ∀ p, S p → p < 4060) {y : Nat} (hy : ∀ p, y.testBit p = true ↔ S p) :
    ∀ p, (applyNW NW 1 y).testBit p = true ↔ ∃ q, S q ∧ g q = p := by
  intro p
  rcases Nat.lt_or_ge p 4096 with hp | hp
  · have A := (CFSG.KC.Benes.testBit_applyNW h CFSG.KC.Benes.one_eq_rep y).1 0 (by decide) p hp
    rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add] at A
    rw [A, hy]
    constructor
    · intro hq
      refine ⟨_, hq, ?_⟩
      have h1 := hS _ hq
      have h2 := hg (CFSG.KC.Benes.nwPerm NW p) (by omega)
      simp only [h1, ↓reduceIte] at h2
      rw [← h2, CFSG.KC.Benes.nwInv_nwPerm h]
    · rintro ⟨q, hq, e⟩
      have h1 := hS _ hq
      have h2 := hg q (by omega)
      simp only [h1, ↓reduceIte] at h2
      rw [e] at h2
      rw [← h2, CFSG.KC.Benes.nwPerm_nwInv h]
      exact hq
  · have A := (CFSG.KC.Benes.testBit_applyNW h CFSG.KC.Benes.one_eq_rep y).2 p (by omega)
    rw [A, hy]
    constructor
    · intro hq
      exact absurd (hS _ hq) (by omega)
    · rintro ⟨q, hq, e⟩
      have := hg' q (hS _ hq)
      omega

theorem mv_hi (h0 : nwValid N0 = true) (h1 : nwValid N1 = true) (e x : Nat) :
    mv N0 N1 e x >>> 4096 = mvU N0 N1 e (x >>> 4096) := by
  rw [mv_eq]
  unfold mvU
  split
  · exact applyNW_hi h1 x
  · exact applyNW_hi h0 x

end CFSG.KS.RuTree

end
