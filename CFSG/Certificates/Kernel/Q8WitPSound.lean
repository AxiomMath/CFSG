module

public import Certificates.Data.Kernel.Q8WitP
import CFSG.Certificates.Kernel.L34KSnd.Tab
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack

public section

namespace CFSG.KC.Q8Wit

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum
open CFSG.KC.L34KSnd (pg_pcomp' pg_pidn' canon_lt)

variable {n w : ℕ}

abbrev Cn (n w p : ℕ) : Prop := canonK n w (mask w) (n * w) p = true

theorem beq_false_of_pg {a b i : ℕ} (h : Nat.beq (pg w (mask w) a i) (pg w (mask w) b i) = false) :
    Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · rw [Nat.eq_of_beq_eq_true e, Nat.beq_refl] at h
    exact absurd h (by decide)

theorem not_beq {a b : ℕ} (h : (!Nat.beq a b) = true) : Nat.beq a b = false := by
  simpa using h

theorem q8EltK_canon {x y s : ℕ} (hsz : szOK n w = true) (hx : Cn n w x) (hy : Cn n w y)
    (hs : Cn n w s) (j : ℕ) : Cn n w (q8EltK n w x y s j) := by
  match j with
  | 0 => exact CFSG.KC.L34KSnd.canon_pidn hsz
  | 1 => exact hx
  | 2 => exact hs
  | 3 => exact canonK_pcomp hs hx
  | 4 => exact hy
  | 5 => exact canonK_pcomp hy hx
  | 6 => exact canonK_pcomp hy hs
  | 7 => exact canonK_pcomp hy (canonK_pcomp hs hx)
  | j + 8 =>
    have hb : ∀ m, m < 8 → Nat.beq (j + 8) m = false := fun m hm =>
      Bool.eq_false_iff.2 fun h => by
        have := Nat.eq_of_beq_eq_true h
        omega
    have e : q8EltK n w x y s (j + 8) = pcomp n w (mask w) y (pcomp n w (mask w) s x) := by
      simp only [q8EltK, hb 0 (by omega), hb 1 (by omega), hb 2 (by omega), hb 3 (by omega),
        hb 4 (by omega), hb 5 (by omega), hb 6 (by omega), cond_false]
    rw [e]
    exact canonK_pcomp hy (canonK_pcomp hs hx)

theorem pg_q8EltK {x y s p : ℕ} (hsz : szOK n w = true) (hx : Cn n w x) (hy : Cn n w y)
    (hs : Cn n w s) (hp : p < n) (j : ℕ) :
    pg w (mask w) (q8EltK n w x y s j) p = q8AtK w x y s j p := by
  have hxp := canon_lt hx hp
  have hsp := canon_lt hs hp
  match j with
  | 0 => exact pg_pidn' hsz hp
  | 1 => rfl
  | 2 => rfl
  | 3 =>
    have e : q8EltK n w x y s 3 = pcomp n w (mask w) s x := rfl
    rw [e, pg_pcomp' hs hp]
    rfl
  | 4 => rfl
  | 5 =>
    have e : q8EltK n w x y s 5 = pcomp n w (mask w) y x := rfl
    rw [e, pg_pcomp' hy hp]
    rfl
  | 6 =>
    have e : q8EltK n w x y s 6 = pcomp n w (mask w) y s := rfl
    rw [e, pg_pcomp' hy hp]
    rfl
  | 7 =>
    have e : q8EltK n w x y s 7 = pcomp n w (mask w) y (pcomp n w (mask w) s x) := rfl
    rw [e, pg_pcomp' hy hp, pg_pcomp' hs hp]
    rfl
  | j + 8 =>
    have hb : ∀ m, m < 8 → Nat.beq (j + 8) m = false := fun m hm =>
      Bool.eq_false_iff.2 fun h => by
        have := Nat.eq_of_beq_eq_true h
        omega
    have e : q8EltK n w x y s (j + 8) = pcomp n w (mask w) y (pcomp n w (mask w) s x) := by
      simp only [q8EltK, hb 0 (by omega), hb 1 (by omega), hb 2 (by omega), hb 3 (by omega),
        hb 4 (by omega), hb 5 (by omega), hb 6 (by omega), cond_false]
    have e2 : q8AtK w x y s (j + 8) p =
        pg w (mask w) y (pg w (mask w) s (pg w (mask w) x p)) := by
      simp only [q8AtK, hb 0 (by omega), hb 1 (by omega), hb 2 (by omega), hb 3 (by omega),
        hb 4 (by omega), hb 5 (by omega), hb 6 (by omega), cond_false]
    rw [e, e2, pg_pcomp' hy hp, pg_pcomp' hs hp]

theorem outsideK_of_P {x y s c a P : ℕ} (hsz : szOK n w = true) (hx : Cn n w x) (hy : Cn n w y)
    (hs : Cn n w s) (hc : Cn n w c) (ha : Cn n w a) (h : outsidePK n w x y s c a P = true) :
    outsideK n w x y s c a = true := by
  unfold outsidePK at h
  unfold outsideK
  rw [allNP_iff] at h ⊢
  intro j hj
  have hj' := h j hj
  simp only [Bool.and_eq_true] at hj'
  obtain ⟨hp, hne⟩ := hj'
  have hp' := Nat.blt_eq.mp hp
  rw [Bool.not_eq_true']
  refine beq_false_of_pg (w := w) (i := fldK 13 P j) ?_
  rw [pg_pcomp' hc hp', pg_pcomp' (q8EltK_canon hsz hx hy hs j) hp',
    pg_q8EltK hsz hx hy hs (canon_lt hc hp') j]
  exact not_beq hne

theorem commK_of_nc {a u c ci p : ℕ} (ha : Cn n w a) (hu : Cn n w u) (hc : Cn n w c)
    (hci : Cn n w ci) (hp : p < n) (h : ncPK w a u c ci p = true) :
    commK n w a (pcomp n w (mask w) (pcomp n w (mask w) c u) ci) = false := by
  unfold commK
  have hb : Cn n w (pcomp n w (mask w) (pcomp n w (mask w) c u) ci) :=
    canonK_pcomp (canonK_pcomp hc hu) hci
  refine beq_false_of_pg (w := w) (i := p) ?_
  rw [pg_pcomp' ha hp, pg_pcomp' hb hp, pg_pcomp' (canonK_pcomp hc hu) hp,
    pg_pcomp' (canonK_pcomp hc hu) (canon_lt ha hp), pg_pcomp' hc (canon_lt hci hp),
    pg_pcomp' hc (canon_lt hci (canon_lt ha hp))]
  exact not_beq h

theorem wit4K_of_P {x y s c ci f P N : ℕ} (hsz : szOK n w = true) (hx : Cn n w x)
    (hy : Cn n w y) (hs : Cn n w s) (hc : Cn n w c) (hci : Cn n w ci)
    (h : wit4PK n w x y s c ci f P N = true) : wit4K n w x y s c ci = true := by
  unfold wit4PK at h
  unfold wit4K
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  have hp := Nat.blt_eq.mp h3
  refine ⟨⟨h1, ?_⟩, ?_⟩
  · simp only [Bool.or_eq_true]
    cases hf : Nat.beq f 1
    · rw [hf, cond_false] at h2
      exact Or.inr (outsideK_of_P hsz hx hy hs hc hy h2)
    · rw [hf, cond_true] at h2
      exact Or.inl (outsideK_of_P hsz hx hy hs hc hx h2)
  · simp only [Bool.or_eq_true, Bool.not_eq_true']
    cases h0 : Nat.beq (Nat.div N 8192) 0
    · rw [h0, cond_false] at h4
      cases h1' : Nat.beq (Nat.div N 8192) 1
      · rw [h1', cond_false] at h4
        cases h2' : Nat.beq (Nat.div N 8192) 2
        · rw [h2', cond_false] at h4
          exact Or.inr (commK_of_nc hy hy hc hci hp h4)
        · rw [h2', cond_true] at h4
          exact Or.inl (Or.inr (commK_of_nc hy hx hc hci hp h4))
      · rw [h1', cond_true] at h4
        exact Or.inl (Or.inl (Or.inr (commK_of_nc hx hy hc hci hp h4)))
    · rw [h0, cond_true] at h4
      exact Or.inl (Or.inl (Or.inl (commK_of_nc hx hx hc hci hp h4)))

end CFSG.KC.Q8Wit

end
