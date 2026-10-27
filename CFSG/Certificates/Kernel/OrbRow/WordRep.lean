module

public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.OrbRow.CentSound

public section

namespace CFSG.KC.OrbRow

open CFSG.KC.Enum CFSG.KC.PGrp CFSG.KS CFSG.KS.Raw.Orb

variable {n : ℕ}

theorem strictN_apply (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem strictB_apply (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem posWord_rec_rep {w : ℕ} (hn : n < 2 ^ 32) {G : ℕ → ℕ} {σ : ℕ → Equiv.Perm (Fin n)} :
    ∀ (wd : List ℕ), (∀ l ∈ wd, PRep n w (G l) (σ l)) → ∀ (acc : ℕ) (g : Equiv.Perm (Fin n)),
      PRep n w acc g →
      PRep n w (List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
        (fun l _ ih acc => strictN (pcomp n w (mask w) acc (G l)) ih) wd acc)
        (g * (wd.map σ).prod)
  | [], _, acc, g, h => by simpa using h
  | l :: wd, hG, acc, g, h => by
    change PRep n w (strictN (pcomp n w (mask w) acc (G l)) _) _
    rw [strictN_apply, List.map_cons, List.prod_cons, ← mul_assoc]
    exact posWord_rec_rep hn wd (fun l' hl' => hG l' (List.mem_cons_of_mem _ hl')) _ _
      (prep_pcomp hn h (hG l List.mem_cons_self))

theorem posWordK_rep {w : ℕ} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {G : ℕ → ℕ}
    {σ : ℕ → Equiv.Perm (Fin n)} {wd : List ℕ} (hG : ∀ l ∈ wd, PRep n w (G l) (σ l)) :
    PRep n w (posWordK n w G wd) (wd.map σ).prod := by
  have h := posWord_rec_rep (w := w) (by omega) wd hG (pidn n w) 1 (prep_pidn hn hw)
  rw [one_mul] at h
  exact h

theorem wordEqK_sound {w : ℕ} {S : List ℕ} {k lv x : ℕ} {wd : List ℕ}
    (h : wordEqK n w S k lv x wd = true) :
    (∀ j ∈ wd, j < k ∧ Nat.beq fld(lv, j, nat_lit 1) (nat_lit 1) = true) ∧
      x = posWordK n w (getS S) wd := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  exact ⟨lettersK_sound h1, Nat.eq_of_beq_eq_true h2⟩

theorem ncAllK_sound {w m idn : ℕ} {G : ℕ → ℕ} {k : ℕ} :
    ∀ {TE : List ℕ}, ncAllK n w m idn G k TE = true → ∀ e ∈ TE, e ≠ idn →
      allN k (fun j => commOK n w m e (G j)) = false
  | [], _, e, he, _ => absurd he List.not_mem_nil
  | t :: TE, h, e, he, hne => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    rcases List.mem_cons.1 he with rfl | he
    · have hb : Nat.beq e idn = false := by
        cases hh : Nat.beq e idn
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hh) hne
      have h1' : Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool) true false (allN k (fun j => commOK n w m e (G j))))
          true (Nat.beq e idn) = true := h1
      rw [hb] at h1'
      cases ha : allN k (fun j => commOK n w m e (G j))
      · rfl
      · rw [ha] at h1'
        exact absurd h1' Bool.false_ne_true
    · exact ncAllK_sound h2 e he hne

end CFSG.KC.OrbRow

end
