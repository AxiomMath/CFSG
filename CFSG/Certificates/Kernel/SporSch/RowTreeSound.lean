module

public import Certificates.Data.Kernel.SporSch.RowTreeK
public import CFSG.Certificates.Kernel.SporSch.RuTreeSound
public import CFSG.Certificates.Kernel.Enum.Defs
import CFSG.Certificates.Kernel.Spor.Loops
import Aesop.BuiltinRules
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToAdditive

public section

namespace CFSG.KS.RowTree

open CFSG.KLC.Fi22 CFSG.KS.RuTree CFSG.KC.Enum

theorem sB_eq (v : Nat) (k : Nat → Bool) : sB v k = k v := by cases v <;> rfl

theorem land_two_pow (a n : Nat) : a &&& 2 ^ n = if a.testBit n then 2 ^ n else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hj : n = j
  · subst hj
    by_cases h : a.testBit n <;> simp [h, Nat.testBit_two_pow_self]
  · by_cases h : a.testBit n <;> simp [h, hj, Nat.testBit_two_pow_of_ne hj]

theorem bt_eq (x i : Nat) : bt x i = x.testBit i := by
  unfold bt
  change Nat.blt 0 (x &&& 1 <<< i) = _
  rw [Nat.one_shiftLeft, land_two_pow]
  cases h : x.testBit i
  · rfl
  · simp [Nat.blt_eq, Nat.two_pow_pos]

theorem testBit_of_shr {r : Nat} (h : Nat.shiftRight r 4060 = 0) {p : Nat}
    (hp : r.testBit p = true) : p < 4060 := by
  rcases Nat.lt_or_ge p 4060 with h' | h'
  · exact h'
  · exfalso
    have h2 : (r >>> 4060).testBit (p - 4060) = r.testBit p := by
      rw [Nat.testBit_shiftRight, show 4060 + (p - 4060) = p by omega]
    rw [show r >>> 4060 = Nat.shiftRight r 4060 from rfl, h, Nat.zero_testBit, hp] at h2
    exact Bool.false_ne_true h2

@[expose] def NetOf (NW : Nat) (g : Nat → Nat) : Prop :=
  nwValid NW = true ∧ (∀ s < 4096, CFSG.KC.Benes.nwInv NW s = if s < 4060 then g s else s) ∧
    (∀ s < 4060, g s < 4060) ∧ ∀ s < 4060, ∀ t < 4060, g s = g t → s = t

theorem move_spec {NW : Nat} {g : Nat → Nat} (hN : NetOf NW g) {r : Nat}
    (hr : Nat.shiftRight r 4060 = 0) (p : Nat) :
    (applyNW NW 1 r).testBit p = true ↔ ∃ q, r.testBit q = true ∧ g q = p :=
  applyNW_img hN.1 hN.2.1 hN.2.2.1 (S := fun q => r.testBit q = true)
    (fun q hq => testBit_of_shr hr hq) (fun _ => Iff.rfl) p

theorem fwd_spec {NW : Nat} {g h : Nat → Nat} (hN : NetOf NW g)
    (hh : ∀ y < 4060, h y < 4060 ∧ g (h y) = y) {rx rp : Nat} (hrp : Nat.shiftRight rp 4060 = 0)
    (e : applyNW NW 1 rp = rx) {y : Nat} (hy : y < 4060) :
    rx.testBit y = true ↔ rp.testBit (h y) = true := by
  rw [← e, move_spec hN hrp]
  constructor
  · rintro ⟨q, hq, hqy⟩
    have hq' := testBit_of_shr hrp hq
    have := hN.2.2.2 q hq' (h y) (hh y hy).1 (by rw [hqy, (hh y hy).2])
    rwa [← this]
  · intro hq
    exact ⟨h y, hq, (hh y hy).2⟩

theorem bwd_spec {NW : Nat} {g : Nat → Nat} (hN : NetOf NW g) {rx rp : Nat}
    (hrx : Nat.shiftRight rx 4060 = 0) (e : applyNW NW 1 rx = rp) {y : Nat} (hy : y < 4060) :
    rx.testBit y = true ↔ rp.testBit (g y) = true := by
  rw [← e, move_spec hN hrx]
  constructor
  · intro hq
    exact ⟨y, hq, rfl⟩
  · rintro ⟨q, hq, hqy⟩
    have := hN.2.2.2 q (testBit_of_shr hrx hq) y hy hqy
    rwa [← this]

theorem reachK_succ (par : Nat → Nat) (f x : Nat) :
    reachK par (f + 1) x = if x = 0 then true else reachK par f (par x) := by
  change Bool.rec (motive := fun _ => Bool) (sB (par x) (reachK par f)) true (Nat.beq x 0) = _
  rw [sB_eq]
  by_cases hx : x = 0
  · subst hx
    rfl
  · rw [if_neg hx]
    have : Nat.beq x 0 = false := by
      cases h : Nat.beq x 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hx
    rw [this]

theorem beq_true {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem blt_iff {a b : Nat} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

variable {NW0 NW1 : Nat} {g0 g1 : Nat → Nat} {Row par lab : Nat → Nat} {D : Nat → Prop}
  {H : Nat → Nat → Nat} {TI : Nat → Nat → Nat}

theorem rows_sound {lab' : Nat → Nat} {c' : Nat} (h0 : NetOf NW0 g0) (h1 : NetOf NW1 g1)
    (hH1 : ∀ y < 4060, H 1 y < 4060 ∧ g0 (H 1 y) = y)
    (hH2 : ∀ y < 4060, H 2 y < 4060 ∧ g1 (H 2 y) = y)
    (hH3 : ∀ y < 4060, H 3 y = g0 y)
    (hH4 : ∀ c, c ≠ 1 → c ≠ 2 → c ≠ 3 → ∀ y < 4060, H c y = g1 y)
    (hroot : rootK 4060 (Row 0) lab' c' = true) (hD : ∀ y < 4060, D y ↔ lab' y = c')
    (hrow : ∀ x, 0 < x → x < 4060 → rowK NW0 NW1 4060 Row par lab 32 x = true)
    (hpar : ∀ x < 4060, par x < 4060)
    (hT0 : ∀ y < 4060, TI 0 y = y)
    (hT : ∀ x, 0 < x → x < 4060 → ∀ y < 4060, TI x y = TI (par x) (H (lab x) y)) :
    ∀ x < 4060, Nat.shiftRight (Row x) 4060 = 0 ∧
      ∀ y < 4060, ((Row x).testBit y = true ↔ D (TI x y)) := by
  have hR := andB_iff'.1 hroot
  have hroot' : Nat.shiftRight (Row 0) 4060 = 0 ∧
      ∀ y < 4060, ((Row 0).testBit y = true ↔ D (TI 0 y)) := by
    refine ⟨beq_true hR.1, fun y hy => ?_⟩
    have := rngK_spec hR.2 y (Nat.zero_le _) (by omega)
    have hb' : bt (Row 0) y = Nat.beq (lab' y) c' := by
      revert this
      cases bt (Row 0) y <;> cases Nat.beq (lab' y) c' <;> decide
    rw [hT0 y hy, hD y hy, ← bt_eq, hb']
    exact ⟨Nat.eq_of_beq_eq_true, fun h => by rw [h]; exact Nat.beq_refl _⟩
  have key : ∀ f x, x < 4060 → reachK par f x = true → Nat.shiftRight (Row x) 4060 = 0 ∧
      ∀ y < 4060, ((Row x).testBit y = true ↔ D (TI x y)) := by
    intro f
    induction f with
    | zero =>
      intro x _ hx
      rw [beq_true hx]
      exact hroot'
    | succ f ih =>
      intro x hxn hx
      rw [reachK_succ] at hx
      by_cases hx0 : x = 0
      · rw [hx0]
        exact hroot'
      · rw [if_neg hx0] at hx
        have hp := hpar x hxn
        obtain ⟨hpr, hpy⟩ := ih (par x) hp hx
        have hk := andB_iff'.1 (hrow x (Nat.pos_of_ne_zero hx0) hxn)
        rw [sB_eq, sB_eq] at hk
        have he := andB_iff'.1 hk.2
        have hxr := beq_true he.1
        have hT' := hT x (Nat.pos_of_ne_zero hx0) hxn
        refine ⟨hxr, fun y hy => ?_⟩
        have hb := he.2
        rw [hT' y hy]
        by_cases c1 : lab x = 1
        · rw [c1] at hb ⊢
          have e := beq_true hb
          rw [fwd_spec h0 hH1 hpr e hy]
          exact hpy _ (hH1 y hy).1
        · have hb1 : Nat.beq (lab x) 1 = false := by
            cases h : Nat.beq (lab x) 1
            · rfl
            · exact absurd (beq_true h) c1
          rw [hb1] at hb
          by_cases c2 : lab x = 2
          · rw [c2] at hb ⊢
            have e := beq_true hb
            rw [fwd_spec h1 hH2 hpr e hy]
            exact hpy _ (hH2 y hy).1
          · have hb2 : Nat.beq (lab x) 2 = false := by
              cases h : Nat.beq (lab x) 2
              · rfl
              · exact absurd (beq_true h) c2
            rw [hb2] at hb
            by_cases c3 : lab x = 3
            · rw [c3] at hb ⊢
              have e := beq_true hb
              rw [bwd_spec h0 hxr e hy, hH3 y hy]
              exact hpy _ (h0.2.2.1 y hy)
            · have hb3 : Nat.beq (lab x) 3 = false := by
                cases h : Nat.beq (lab x) 3
                · rfl
                · exact absurd (beq_true h) c3
              rw [hb3] at hb
              have e := beq_true hb
              rw [bwd_spec h1 hxr e hy, hH4 (lab x) c1 c2 c3 y hy]
              exact hpy _ (h1.2.2.1 y hy)
  intro x hx
  rcases Nat.eq_zero_or_pos x with h | h
  · rw [h]
    exact hroot'
  · exact key 32 x hx (andB_iff'.1 (hrow x h hx)).1

theorem fp_inj {F Lk Pk : Nat → Nat} {inS : Nat → Bool} {m n : Nat}
    (hk : allN m (keyK F Lk m) = true) (hc : allN n (coverK inS Pk Lk m) = true)
    {x y : Nat} (hx : x < n) (hy : y < n) (hsx : inS x = true) (hsy : inS y = true)
    (e : F x = F y) : x = y := by
  have hmono : ∀ i j, i < j → j < m → F (Lk i) < F (Lk j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      have hs := orB_iff'.1 (allN_spec hk j (by omega))
      have hstep : F (Lk j) < F (Lk (j + 1)) := by
        rcases hs with hs | hs
        · exfalso
          have hb : Nat.blt (Nat.succ j) m = true := blt_iff.2 hj
          rw [hb] at hs
          exact absurd hs (by decide)
        · exact blt_iff.1 hs
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact lt_trans (ih h (by omega)) hstep
      · rw [h]
        exact hstep
  have cov : ∀ z < n, inS z = true → Pk z < m ∧ Lk (Pk z) = z := by
    intro z hz hs
    have := orB_iff'.1 (allN_spec hc z hz)
    rcases this with h | h
    · rw [hs] at h
      exact absurd h (by decide)
    · obtain ⟨h1, h2⟩ := andB_iff'.1 h
      exact ⟨blt_iff.1 h1, beq_true h2⟩
  obtain ⟨hx1, hx2⟩ := cov x hx hsx
  obtain ⟨hy1, hy2⟩ := cov y hy hsy
  rcases Nat.lt_trichotomy (Pk x) (Pk y) with h | h | h
  · have := hmono _ _ h hy1
    rw [hx2, hy2, e] at this
    exact absurd this (lt_irrefl _)
  · rw [← hx2, ← hy2, h]
  · have := hmono _ _ h hx1
    rw [hx2, hy2, e] at this
    exact absurd this (lt_irrefl _)

end CFSG.KS.RowTree

end
