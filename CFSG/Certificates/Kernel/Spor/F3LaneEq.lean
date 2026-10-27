module

public import CFSG.Certificates.Kernel.Spor.F3LaneSound
public import Certificates.Data.Kernel.Spor.F3LaneId

public section

namespace CFSG.KS.F3L

open CFSG.F3.Native CFSG.KC.Enum

theorem idUpTo_spec (d : Nat) (I : V) :
    ∀ n, idUpTo d I n = true → ∀ i < n, blk d I i = ⟨1 <<< i, 0⟩
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    have h' : bAnd(idUpTo d I n, bAnd(Nat.beq (blk d I n).p (Nat.shiftLeft (nat_lit 1) n),
        Nat.beq (blk d I n).m (nat_lit 0))) = true := h
    rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h'
    obtain ⟨h1, h2, h3⟩ := h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact idUpTo_spec d I n h1 i hi
    · exact V.ext' (Nat.eq_of_beq_eq_true h2) (Nat.eq_of_beq_eq_true h3)

theorem idM_of_idOK {d : Nat} {I : V} (h : idOK d I = true) : idM d = unlane d I := by
  have hb := idUpTo_spec d I d h
  apply Array.ext
  · rw [idM_size' d, unlane_size]
  · intro i h1 h2
    have hi : i < d := by rwa [unlane_size] at h2
    rw [← getElem!_pos (unlane d I) i h2, unlane_get I hi, hb i hi]
    simp only [idM, Array.getElem_ofFn]

theorem eq_of_beq {X Y : V} (h : X.beq Y = true) : X = Y :=
  V.ext' (V.beq_iff.1 h).1 (V.beq_iff.1 h).2

theorem eqM_of_beq {d : Nat} {X Y : V} (h : X.beq Y = true) :
    eqM d (unlane d X) (unlane d Y) = true := by
  rw [eq_of_beq h]
  exact eqM_self (unlane_size d Y)

end CFSG.KS.F3L

end
