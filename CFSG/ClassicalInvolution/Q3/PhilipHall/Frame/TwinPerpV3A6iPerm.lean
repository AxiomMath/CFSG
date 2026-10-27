module

public import Certificates.Certificate398102

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.OmegaEight

@[expose] noncomputable def curtisPerm (i : Fin 8) : Equiv.Perm (Fin 360) :=
  permOfArr 360 genArrs[i.val]!

theorem rep_curtisLetter
    (hv : ∀ i < 8, isInvA 360 genArrs[i]! (invCand 360 genArrs[i]!) = true) (l : Fin 8 × Bool) :
    Rep 360 (if l.2 then genArrs[l.1.val]! else invCand 360 genArrs[l.1.val]!)
      (if l.2 then curtisPerm l.1 else (curtisPerm l.1)⁻¹) := by
  obtain ⟨i, b⟩ := l
  have h := rep_permOfArr (hv i.val i.2)
  cases b
  · exact h.2
  · exact h.1

theorem rep_curtisFoldl
    (hv : ∀ i < 8, isInvA 360 genArrs[i]! (invCand 360 genArrs[i]!) = true) :
    ∀ (w : List (Fin 8 × Bool)) {acc : Array ℕ} {g : Equiv.Perm (Fin 360)}, Rep 360 acc g →
      Rep 360 (w.foldl (fun acc l => compA 360 acc
          (if l.2 then genArrs[l.1.val]! else invCand 360 genArrs[l.1.val]!)) acc)
        (g * FreeGroup.lift curtisPerm (FreeGroup.mk w)) := by
  intro w
  induction w with
  | nil =>
    intro acc g hacc
    simpa [← FreeGroup.one_eq_mk] using hacc
  | cons l w ih =>
    intro acc g hacc
    rw [List.foldl_cons]
    have h1 := ih (rep_compA hacc (rep_curtisLetter hv l))
    have e : FreeGroup.lift curtisPerm (FreeGroup.mk (l :: w)) =
        (if l.2 then curtisPerm l.1 else (curtisPerm l.1)⁻¹) *
          FreeGroup.lift curtisPerm (FreeGroup.mk w) := by
      rw [FreeGroup.lift_mk, FreeGroup.lift_mk, List.map_cons, List.prod_cons]
      cases l.2 <;> rfl
    rw [e, ← mul_assoc]
    exact h1

theorem rep_curtisWordArr
    (hv : ∀ i < 8, isInvA 360 genArrs[i]! (invCand 360 genArrs[i]!) = true)
    (w : List (Fin 8 × Bool)) :
    Rep 360 (curtisWordArr genArrs w) (FreeGroup.lift curtisPerm (FreeGroup.mk w)) := by
  have := rep_curtisFoldl hv w (rep_idA (n := 360))
  rwa [one_mul] at this

theorem lift_curtisPerm_eq_one {r : List (Fin 8 × Bool)} (hr : r ∈ curtisPG) :
    FreeGroup.lift curtisPerm (FreeGroup.mk r) = 1 := by
  have hp := Certificates.certificate398102
  simp only [curtisPermCheck, Bool.and_eq_true, List.all_eq_true] at hp
  obtain ⟨hv, hw⟩ := hp
  have hv' := allLt_iff.1 hv
  exact (eqA_iff (rep_curtisWordArr hv' r) rep_idA).1 (hw r hr)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6
