
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43ModelBase

@[expose] public section

namespace CFSG.EvenSporadicStandard.M24Std.CU43

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative CFSG.LieType.Multipliers.U43

theorem allLt_comm_iff {n : ℕ} {w : List (Array ℕ)} {H : Equiv.Perm (Fin n)} (hw : RepW n w H)
    {r : Array ℕ} {A : Equiv.Perm (Fin n)} (hr : Rep n r A) :
    allLt n (fun i => evR w r[i]! == r[evR w i]!) = true ↔ H * A = A * H := by
  rw [allLt_iff]
  constructor
  · intro h
    refine Equiv.ext fun x => Fin.ext ?_
    have := h x x.2
    rw [beq_iff_eq] at this
    have e1 : r[(x : ℕ)]! = (A x : ℕ) := hr x
    have e2 : evR w (A x : ℕ) = H (A x) := hw (A x)
    have e3 : evR w (x : ℕ) = H x := hw x
    rw [e1, e2, e3] at this
    have e4 : r[(H x : ℕ)]! = (A (H x) : ℕ) := hr (H x)
    rw [e4] at this
    simpa using this
  · intro h i hi
    rw [beq_iff_eq]
    have e1 : r[i]! = (A ⟨i, hi⟩ : ℕ) := hr ⟨i, hi⟩
    have e2 : evR w (A ⟨i, hi⟩ : ℕ) = H (A ⟨i, hi⟩) := hw (A ⟨i, hi⟩)
    have e3 : evR w i = H ⟨i, hi⟩ := hw ⟨i, hi⟩
    have e4 : r[(H ⟨i, hi⟩ : ℕ)]! = (A (H ⟨i, hi⟩) : ℕ) := hr (H ⟨i, hi⟩)
    rw [e1, e2, e3, e4]
    have := congrArg (fun F : Equiv.Perm (Fin n) => (F ⟨i, hi⟩ : ℕ)) h
    simpa using this

theorem allLt_sq_iff {n : ℕ} {w : List (Array ℕ)} {H : Equiv.Perm (Fin n)} (hw : RepW n w H) :
    allLt n (fun i => evR w (evR w i) == i) = true ↔ H * H = 1 := by
  rw [allLt_iff]
  constructor
  · intro h
    refine Equiv.ext fun x => Fin.ext ?_
    have := h x x.2
    rw [beq_iff_eq] at this
    have e2 : evR w (H x : ℕ) = H (H x) := hw (H x)
    have e3 : evR w (x : ℕ) = H x := hw x
    rw [e3, e2] at this
    simpa using this
  · intro h i hi
    rw [beq_iff_eq]
    have e3 : evR w i = H ⟨i, hi⟩ := hw ⟨i, hi⟩
    have e2 : evR w (H ⟨i, hi⟩ : ℕ) = H (H ⟨i, hi⟩) := hw (H ⟨i, hi⟩)
    rw [e3, e2]
    have := congrArg (fun F : Equiv.Perm (Fin n) => (F ⟨i, hi⟩ : ℕ)) h
    simpa using this

section Counts

def CommGens (k : ℕ) (g : Equiv.Perm (Fin 820)) : Prop :=
  g * tP k * psi xElt = psi xElt * (g * tP k) ∧ g * tP k * psi yElt = psi yElt * (g * tP k)

end Counts

end CFSG.EvenSporadicStandard.M24Std.CU43
