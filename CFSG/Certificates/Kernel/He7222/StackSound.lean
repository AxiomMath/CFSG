module

public import Certificates.Data.Kernel.He7222.Cls
public import Certificates.Data.Kernel.He7222.Fix
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.OrbRow.LevelSound

public section

namespace CFSG.KC.HeChain

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.OrbRow CFSG.KS.Raw.Orb CFSG.KS.PF

variable {n w : ℕ}

@[expose] def StkRep (n w : ℕ) (ys : List ℕ) (gs : List (Equiv.Perm (Fin n))) : Prop :=
  List.Forall₂ (fun y g => PRep n w y g) ys gs

theorem evK_rep : ∀ {ys : List ℕ} {gs : List (Equiv.Perm (Fin n))}, StkRep n w ys gs →
    ∀ x : Fin n, evK w (mask w) ys x = (gs.prod x : ℕ)
  | [], [], _, x => rfl
  | y :: ys, g :: gs, h, x => by
    rw [StkRep, List.forall₂_cons] at h
    have e : evK w (mask w) (y :: ys) x = pg w (mask w) y (evK w (mask w) ys x) := rfl
    rw [e, evK_rep h.2 x, h.1, List.prod_cons, Equiv.Perm.mul_apply]

theorem keyF_fld (w : ℕ) (f : ℕ → ℕ) : ∀ nf, (∀ k < nf, f k < 2 ^ w) →
    Fld w (keyF w f nf) (fun i => if i < nf then f i else 0)
  | 0, _ => fld_congr (fld_zero w) (fun i => by simp)
  | nf + 1, hf => by
    have e : keyF w f (nf + 1) = keyF w f nf ||| (f nf <<< (w * nf)) := rfl
    rw [e]
    refine fld_congr (fld_or (keyF_fld w f nf (fun k hk => hf k (by omega)))
      (fld_shl nf (fld_one (hf nf (by omega))))) (fun i => ?_)
    by_cases h1 : i < nf
    · simp [h1, show i < nf + 1 by omega, show ¬ nf ≤ i by omega]
    · by_cases h2 : i = nf
      · subst h2
        simp
      · simp [h1, show ¬ i < nf + 1 by omega, show i - nf ≠ 0 by omega]

theorem keyF_inj {f g : ℕ → ℕ} {nf : ℕ} (hf : ∀ k < nf, f k < 2 ^ w)
    (hg : ∀ k < nf, g k < 2 ^ w) (he : keyF w f nf = keyF w g nf) : ∀ k < nf, f k = g k := by
  intro k hk
  have h1 := pg_of_fld (i := k) (keyF_fld w f nf hf) (by simp only [hk, ↓reduceIte]; exact hf k hk)
  have h2 := pg_of_fld (i := k) (keyF_fld w g nf hg) (by simp only [hk, ↓reduceIte]; exact hg k hk)
  simp only [hk, ↓reduceIte] at h1 h2
  rw [← h1, ← h2, he]

theorem tupOK_spec : ∀ {Ts : List (List ℕ)} {ix : List ℕ}, tupOK Ts ix = true →
    ix.length = Ts.length ∧ ∀ t < Ts.length, ix.getD t 0 < (Ts.getD t []).length
  | [], [], _ => ⟨rfl, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  | [], _ :: _, h => absurd h (by simp [tupOK])
  | _ :: _, [], h => absurd h (by simp [tupOK])
  | T :: Ts, j :: ix, h => by
    have h' : bAnd(Nat.blt j (lenS T), tupOK Ts ix) = true := h
    rw [bAnd_iff, Nat.blt_eq, lenS_eq] at h'
    obtain ⟨hl, ha⟩ := tupOK_spec h'.2
    refine ⟨by simp [hl], fun t ht => ?_⟩
    rcases t with _ | t
    · exact h'.1
    · exact ha t (by simpa using ht)

@[expose] noncomputable def tupL (rec : ℕ → ℕ → Equiv.Perm (Fin n)) (L : ℕ) (ix : List ℕ) :
    List (Equiv.Perm (Fin n)) :=
  (List.range L).map fun t => rec t (ix.getD t 0)

theorem tupL_succ (rec : ℕ → ℕ → Equiv.Perm (Fin n)) (L : ℕ) (j : ℕ) (ix : List ℕ) :
    tupL rec (L + 1) (j :: ix) = rec 0 j :: tupL (fun t => rec (t + 1)) L ix := by
  simp only [tupL, List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

theorem stkK_rep : ∀ {Ts : List (List ℕ)} {ix : List ℕ} (rec : ℕ → ℕ → Equiv.Perm (Fin n)),
    tupOK Ts ix = true →
    (∀ t < Ts.length, ∀ j < (Ts.getD t []).length, PRep n w ((Ts.getD t []).getD j 0) (rec t j)) →
    StkRep n w (stkK Ts ix) (tupL rec Ts.length ix)
  | [], [], _, _, _ => List.Forall₂.nil
  | [], _ :: _, _, h, _ => absurd h (by simp [tupOK])
  | _ :: _, [], _, h, _ => absurd h (by simp [tupOK])
  | T :: Ts, j :: ix, rec, h, hr => by
    have h' : bAnd(Nat.blt j (lenS T), tupOK Ts ix) = true := h
    rw [bAnd_iff, Nat.blt_eq, lenS_eq] at h'
    have e : stkK (T :: Ts) (j :: ix) = getS T j :: stkK Ts ix := rfl
    rw [e, List.length_cons, tupL_succ, StkRep, List.forall₂_cons]
    refine ⟨?_, stkK_rep (fun t => rec (t + 1)) h'.2 (fun t ht j hj => hr (t + 1) (by simpa using ht) j hj)⟩
    rw [getS_eq]
    exact hr 0 (by simp) j h'.1

theorem tupK_rep (hn : n < 16777216) (hw : n + 1 < 2 ^ w) :
    ∀ {Ts : List (List ℕ)} {ix : List ℕ} (rec : ℕ → ℕ → Equiv.Perm (Fin n)),
    tupOK Ts ix = true →
    (∀ t < Ts.length, ∀ j < (Ts.getD t []).length, PRep n w ((Ts.getD t []).getD j 0) (rec t j)) →
    PRep n w (tupK n w (mask w) (pidn n w) Ts ix) (tupL rec Ts.length ix).prod
  | [], [], _, _, _ => prep_pidn hn hw
  | [], _ :: _, _, h, _ => absurd h (by simp [tupOK])
  | _ :: _, [], _, h, _ => absurd h (by simp [tupOK])
  | T :: Ts, j :: ix, rec, h, hr => by
    have h' : bAnd(Nat.blt j (lenS T), tupOK Ts ix) = true := h
    rw [bAnd_iff, Nat.blt_eq, lenS_eq] at h'
    have e : tupK n w (mask w) (pidn n w) (T :: Ts) (j :: ix) =
        pcomp n w (mask w) (getS T j) (tupK n w (mask w) (pidn n w) Ts ix) := rfl
    rw [e, List.length_cons, tupL_succ, List.prod_cons]
    refine prep_pcomp (by omega) ?_ (tupK_rep hn hw (fun t => rec (t + 1)) h'.2
      (fun t ht j hj => hr (t + 1) (by simpa using ht) j hj))
    rw [getS_eq]
    exact hr 0 (by simp) j h'.1

theorem pg_high {T y : ℕ} (hTs : T >>> (n * w) = 0) (hy : n ≤ y) : pg w (mask w) T y = 0 := by
  have h1 : T >>> (w * y) = 0 := by
    have e : w * y = n * w + (w * y - n * w) := by
      have := Nat.mul_le_mul_left w hy
      rw [Nat.mul_comm n w]
      omega
    rw [e, Nat.shiftRight_add, hTs, Nat.zero_shiftRight]
  change Nat.land (T >>> (w * y)) (mask w) = 0
  rw [h1]
  exact Nat.zero_and _

theorem invK_rep {T TI : ℕ} {g : Equiv.Perm (Fin n)} (hn : n < 16777216) (hw : n + 1 < 2 ^ w)
    (h : invK n w (mask w) (pidn n w) T TI = true) (hT : PRep n w T g)
    (hTs : T >>> (n * w) = 0) : PRep n w TI g⁻¹ := by
  unfold invK at h
  rw [bAnd_iff, bAnd_iff, Nat.blt_eq] at h
  obtain ⟨-, h0, he⟩ := h
  have he' := Nat.eq_of_beq_eq_true he
  intro x
  have e1 : pg w (mask w) T (pg w (mask w) TI x) = x := by
    rw [← pg_pcomp (by omega) x.2, he', pg_pidn hn hw x.2]
  by_cases hy : pg w (mask w) TI x < n
  · have e2 : g ⟨_, hy⟩ = x := Fin.ext (by rw [← hT ⟨_, hy⟩]; exact e1)
    have e3 : g⁻¹ x = (⟨_, hy⟩ : Fin n) := by
      have := g.symm_apply_apply (⟨_, hy⟩ : Fin n)
      rw [e2] at this
      exact this
    exact (congrArg Fin.val e3).symm
  · exfalso
    rw [pg_high hTs (Nat.not_lt.mp hy)] at e1
    have hx0 : (x : ℕ) = 0 := e1.symm
    have : pg w (mask w) TI x < n := by
      rw [show (x : ℕ) = 0 from hx0]
      exact h0
    exact hy this

end CFSG.KC.HeChain

end
