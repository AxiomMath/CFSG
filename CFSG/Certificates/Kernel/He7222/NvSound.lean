module

public import Certificates.Data.Kernel.He7222.Nv
import CFSG.Certificates.Kernel.OrbRow.LevelSound
import CFSG.Certificates.Kernel.He7222.ChainSound
import CFSG.Certificates.Kernel.He7222.KChSound
public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.KC.HeChain

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.OrbRow CFSG.KS.PF

theorem nvLW_sound {w m : ℕ} {ss : List ℕ} {ks kts : ℕ} {T TI : List ℕ} :
    ∀ (L : List ℕ) (j : ℕ), L = T.drop j →
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun t _ ih j => strictB (keyF w (cjEv w m (List.cons t List.nil) ss
          (List.cons (getS TI j) List.nil)) (nat_lit 5)) (fun k =>
        bAnd(bIf(Nat.beq k ks, true, Nat.beq k kts), strictB (Nat.succ j) ih))) L j = true →
    ∀ i, j ≤ i → i < T.length →
      keyF w (cjEv w m [T.getD i 0] ss [TI.getD i 0]) 5 = ks ∨
        keyF w (cjEv w m [T.getD i 0] ss [TI.getD i 0]) 5 = kts := by
  intro L
  induction L with
  | nil =>
    intro j hL _ i hi hiT
    have hT : T.length ≤ j := List.drop_eq_nil_iff.mp hL.symm
    exact absurd hiT (by omega)
  | cons t L ih =>
    intro j hL h i hi hiT
    obtain ⟨hjT, htj, hL'⟩ := drop_facts hL
    have h' : strictB (keyF w (cjEv w m (List.cons t List.nil) ss
        (List.cons (getS TI j) List.nil)) (nat_lit 5)) (fun k =>
        bAnd(bIf(Nat.beq k ks, true, Nat.beq k kts), strictB (Nat.succ j)
          (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
            (fun t _ ih j => strictB (keyF w (cjEv w m (List.cons t List.nil) ss
                (List.cons (getS TI j) List.nil)) (nat_lit 5)) (fun k =>
              bAnd(bIf(Nat.beq k ks, true, Nat.beq k kts), strictB (Nat.succ j) ih))) L))) =
        true := h
    rw [strictB_eqP, bAnd_iff, strictB_eqP (Nat.succ j)] at h'
    rcases Nat.lt_or_ge j i with hji | hji
    · exact ih (j + 1) hL' h'.2 i hji hiT
    have : i = j := by omega
    subst this
    rw [List.getD_eq_getElem _ _ hjT, htj, ← getS_eq]
    rcases (bIf_iff _ _ _).1 h'.1 with ⟨hk, -⟩ | ⟨-, hk⟩
    · exact Or.inl (Nat.eq_of_beq_eq_true hk)
    · exact Or.inr (Nat.eq_of_beq_eq_true hk)

theorem nvLK_sound {w m : ℕ} {ss : List ℕ} {ks kts : ℕ} {T TI : List ℕ}
    (h : nvLK w m ss ks kts T TI = true) : ∀ i < T.length,
      keyF w (cjEv w m [T.getD i 0] ss [TI.getD i 0]) 5 = ks ∨
        keyF w (cjEv w m [T.getD i 0] ss [TI.getD i 0]) 5 = kts := fun i hi =>
  nvLW_sound T 0 rfl h i (Nat.zero_le _) hi

end CFSG.KC.HeChain

end
