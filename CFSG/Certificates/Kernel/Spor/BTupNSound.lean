module

public import Certificates.Data.Kernel.Spor.BTupN
public import CFSG.Certificates.Kernel.Spor.BTupSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.BTup

open CFSG.KC.Enum CFSG.KS.Row

@[expose] noncomputable def evP {n : Nat} (gp : Nat → Equiv.Perm (Fin n)) (e : Nat) :
    Nat → Equiv.Perm (Fin n)
  | 0 => 1
  | j + 1 => if Nat.beq (Nat.land (Nat.shiftRight e j) (nat_lit 1)) (nat_lit 1) = true then
      gp j * evP gp e j else evP gp e j

theorem evP_succ {n : Nat} (gp : Nat → Equiv.Perm (Fin n)) (e j : Nat) :
    evP gp e (j + 1) = if Nat.beq (Nat.land (Nat.shiftRight e j) (nat_lit 1)) (nat_lit 1) = true
      then gp j * evP gp e j else evP gp e j := rfl

theorem evP_mem {n k : Nat} {gp : Nat → Equiv.Perm (Fin n)} (e : Nat) :
    ∀ j ≤ k, evP gp e j ∈ genSub n k gp := by
  intro j
  induction j with
  | zero => exact fun _ => Subgroup.one_mem _
  | succ j ih =>
    intro hj
    rw [evP_succ]
    split_ifs
    · exact Subgroup.mul_mem _ (gp_mem (by omega)) (ih (by omega))
    · exact ih (by omega)

theorem btEv_spec {n w k : Nat} {G : Nat → Nat} {gp : Nat → Equiv.Perm (Fin n)}
    (hg : ∀ j < k, ∀ x : Fin n, pg w (mask w) (G j) x = gp j x) (e : Nat) :
    ∀ j ≤ k, ∀ p : Fin n, btEv w (mask w) G e j p = (evP gp e j p : Nat) := by
  intro j
  induction j with
  | zero => exact fun _ p => rfl
  | succ j ih =>
    intro hj p
    have e1 : btEv w (mask w) G e (j + 1) p = strictN (btEv w (mask w) G e j p) (fun q =>
        nIf(Nat.beq (Nat.land (Nat.shiftRight e j) (nat_lit 1)) (nat_lit 1),
          pg w (mask w) (G j) q, q)) := rfl
    rw [e1, CFSG.KS.Raw.Orb.strictN_eq, CFSG.KS.Raw.Orb.nIf_eq, ih (by omega) p]
    rw [evP_succ]
    split_ifs
    · rw [hg j (by omega), Equiv.Perm.mul_apply]
    · rfl

theorem btNr_spec {n w d k B N Y : Nat} {G : Nat → Nat} {gp : Nat → Equiv.Perm (Fin n)}
    {ν y : Equiv.Perm (Fin n)} {b : Fin d → Fin n}
    (hg : ∀ j < k, ∀ x : Fin n, pg w (mask w) (G j) x = gp j x)
    (hN : ∀ x : Fin n, pg w (mask w) N x = ν x) (hY : ∀ x : Fin n, pg w (mask w) Y x = y x)
    (hB : ∀ t : Fin d, pg w (mask w) B t = b t) (h : btNrK w (mask w) d k G B N Y = true) :
    ∃ l ∈ genSub n k gp, ∀ t : Fin d, ν (y (b t)) = l (ν (b t)) := by
  unfold btNrK at h
  have h' : ¬ ∀ e < Nat.pow 2 k, Bool.not (allN d (fun t =>
      Nat.beq (pg w (mask w) N (pg w (mask w) Y (pg w (mask w) B t)))
        (btEv w (mask w) G e k (pg w (mask w) N (pg w (mask w) B t))))) = true := by
    intro hall
    rw [CFSG.KS.Raw.Orb.allN_iff.2 hall] at h
    exact Bool.false_ne_true h
  push Not at h'
  obtain ⟨e, -, he⟩ := h'
  have he' : allN d (fun t =>
      Nat.beq (pg w (mask w) N (pg w (mask w) Y (pg w (mask w) B t)))
        (btEv w (mask w) G e k (pg w (mask w) N (pg w (mask w) B t)))) = true := by
    cases hc : allN d (fun t =>
      Nat.beq (pg w (mask w) N (pg w (mask w) Y (pg w (mask w) B t)))
        (btEv w (mask w) G e k (pg w (mask w) N (pg w (mask w) B t))))
    · rw [hc] at he
      exact absurd rfl he
    · rfl
  refine ⟨evP gp e k, evP_mem e k le_rfl, fun t => Fin.ext ?_⟩
  have ht := Nat.beq_eq.mp (CFSG.KS.Raw.Orb.allN_iff.1 he' t t.2)
  rw [hB t, hY, hN, hN, btEv_spec hg e k le_rfl] at ht
  exact ht

theorem btCj_spec {n w d kw km k cnt base B C Y : Nat} {G K R POS : Nat → Nat}
    {gp : Nat → Equiv.Perm (Fin n)} {c y : Equiv.Perm (Fin n)} {b : Fin d → Fin n}
    (hg : ∀ j < k, ∀ x : Fin n, pg w (mask w) (G j) x = gp j x)
    (hb : ∀ t : Fin d, pg w (mask w) base t = b t)
    (hp : ∀ i < cnt, btPtK n w (mask w) d kw km k cnt base G K R POS i = true)
    (hC : ∀ x : Fin n, pg w (mask w) C x = c x) (hY : ∀ x : Fin n, pg w (mask w) Y x = y x)
    (hB : ∀ t : Fin d, pg w (mask w) B t = b t)
    (h : btCjK w (mask w) d kw km cnt K B C Y = true) :
    ∃ x ∈ genSub n k gp, ∀ t : Fin d, c (x (b t)) = y (c (b t)) := by
  unfold btCjK at h
  have h' : ¬ ∀ q < cnt, Bool.not (strictB (btKey kw km K q) (fun x => allN d (fun t =>
      Nat.beq (pg w (mask w) C (pg w (mask w) x t))
        (pg w (mask w) Y (pg w (mask w) C (pg w (mask w) B t)))))) = true := by
    intro hall
    rw [CFSG.KS.Raw.Orb.allN_iff.2 hall] at h
    exact Bool.false_ne_true h
  push Not at h'
  obtain ⟨q, hq, he⟩ := h'
  rw [CFSG.KS.Raw.Orb.strictB_eq] at he
  have he' : allN d (fun t => Nat.beq (pg w (mask w) C (pg w (mask w) (btKey kw km K q) t))
      (pg w (mask w) Y (pg w (mask w) C (pg w (mask w) B t)))) = true := by
    cases hc : allN d (fun t => Nat.beq (pg w (mask w) C (pg w (mask w) (btKey kw km K q) t))
      (pg w (mask w) Y (pg w (mask w) C (pg w (mask w) B t))))
    · rw [hc] at he
      exact absurd rfl he
    · rfl
  obtain ⟨x, hx, hk⟩ := btKey_mem hg hb hp hq
  refine ⟨x, hx, fun t => Fin.ext ?_⟩
  have ht := Nat.beq_eq.mp (CFSG.KS.Raw.Orb.allN_iff.1 he' t t.2)
  rw [hk t, hC, hB t, hC, hY] at ht
  exact ht

end CFSG.KS.BTup

end
