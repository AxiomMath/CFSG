module

public import Certificates.Data.Kernel.Spor.PNode4
public import CFSG.Certificates.Kernel.Spor.PNodeSound
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.PNode4

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PNode

theorem nodes4K_spec {n w m N : Nat} {T PL : Nat → Nat} {PP SQ : List Nat} :
    ∀ (NW : List Nat) (i0 : Nat), nodes4K n w m N T PL PP SQ NW i0 = true →
      ∀ k < NW.length, node4K n w m N T PL PP SQ (i0 + k) (NW.getD k 0) = true
  | [], _, _, k, hk => absurd hk (by simp)
  | nw :: NW, i0, h, k, hk => by
    change bAnd(node4K n w m N T PL PP SQ i0 nw, nodes4K n w m N T PL PP SQ NW (Nat.succ i0)) =
      true at h
    cases h1 : node4K n w m N T PL PP SQ i0 nw
    · rw [h1] at h
      exact ff h
    · rw [h1] at h
      cases k with
      | zero => exact h1
      | succ k =>
        have := nodes4K_spec NW (Nat.succ i0) h k (by simpa using hk)
        rw [show i0 + (k + 1) = Nat.succ i0 + k by omega]
        exact this

theorem node4K_even {n w m N : Nat} {T PL : Nat → Nat} {PP SQ : List Nat} {i nw : Nat}
    (h : node4K n w m N T PL PP SQ i nw = true) (hev : parK PP (pathK PL i i) ≠ 1) :
    (∃ x < n, pg w m (T i) (pg w m (T i) (pg w m (T i) (pg w m (T i) x))) ≠ x) ∨
      ∃ j < N, (j = 0 ∨ j ∈ SQ) ∧ pcomp n w m (T i) (T i) = T j := by
  unfold node4K at h
  rw [beq_false hev, strictB_app, strictB_app] at h
  change bIf(Nat.beq (Nat.land nw 1) 1,
    bAnd(Nat.blt (nw >>> 1) n, bIf(Nat.beq (pg w m (T i) (pg w m (T i) (pg w m (T i)
      (pg w m (T i) (nw >>> 1))))) (nw >>> 1), false, true)),
    strictB (Nat.sub (nw >>> 1) 1) (fun j =>
      bAnd(Nat.blt j N, bAnd(bIf(Nat.beq j 0, true, memK j SQ),
        Nat.beq (pcomp n w m (T i) (T i)) (T j))))) = true at h
  cases hb : Nat.beq (Nat.land nw 1) 1
  · rw [hb, strictB_app] at h
    change bAnd(Nat.blt (nw >>> 1 - 1) N, bAnd(bIf(Nat.beq (nw >>> 1 - 1) 0, true,
      memK (nw >>> 1 - 1) SQ), Nat.beq (pcomp n w m (T i) (T i)) (T (nw >>> 1 - 1)))) = true at h
    obtain ⟨h1, h2, h3⟩ := (by simpa only [bAnd_iff] using h :
      Nat.blt (nw >>> 1 - 1) N = true ∧ bIf(Nat.beq (nw >>> 1 - 1) 0, true,
        memK (nw >>> 1 - 1) SQ) = true ∧
      Nat.beq (pcomp n w m (T i) (T i)) (T (nw >>> 1 - 1)) = true)
    refine Or.inr ⟨_, Nat.le_of_ble_eq_true h1, ?_, Nat.eq_of_beq_eq_true h3⟩
    cases hj : Nat.beq (nw >>> 1 - 1) 0
    · rw [hj] at h2
      exact Or.inr (memK_spec h2)
    · exact Or.inl (Nat.eq_of_beq_eq_true hj)
  · rw [hb] at h
    obtain ⟨h1, h2⟩ := (by simpa only [bAnd_iff] using h :
      Nat.blt (nw >>> 1) n = true ∧ bIf(Nat.beq (pg w m (T i) (pg w m (T i) (pg w m (T i)
        (pg w m (T i) (nw >>> 1))))) (nw >>> 1), false, true) = true)
    refine Or.inl ⟨_, Nat.le_of_ble_eq_true h1, fun he => ?_⟩
    rw [he, Nat.beq_refl] at h2
    exact ff h2

end CFSG.KS.PNode4

end
