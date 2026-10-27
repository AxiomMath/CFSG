module

public import Certificates.Data.Kernel.Misc.YamakiGenPos
public import CFSG.Certificates.Kernel.Misc.YamakiA0Sound

public section

namespace CFSG.KC.YamakiGenPos

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec
  CFSG.KD.YamakiGenPos CFSG.KD.BfsK CFSG.KC.BfsEnum CFSG.KC.YamakiS0 CFSG.KC.YamakiA0
  CFSG.KC.Misc.Spec

variable {R : ℕ → ℕ} {o n : ℕ}

theorem genPosK_sound : ∀ {is ps : List ℕ}, genPosK R o n is ps = true →
    ∀ i ∈ is, ∃ p < n, recX R o p = R i
  | [], _, _ => by simp
  | _ :: _, [], h => by simp [genPosK] at h
  | i :: is, p :: ps, h => by
    simp only [genPosK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨hp, he⟩, hr⟩ := h
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj
    · exact ⟨p, hp, he⟩
    · exact genPosK_sound hr j hj

theorem lookups_of_pos {PA PB : ℕ → ℕ} {E : Enum}
    (hE : BInvE (fun t => arrN (recX R o t)) PA PB n E)
    (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) {is ps : List ℕ}
    (h12 : ∀ i ∈ is, i < 12) (h : genPosK R o n is ps = true) :
    is.all (fun i => (E.lookup (genA ())[i]!).isSome) = true := by
  rw [List.all_eq_true]
  intro i hi
  obtain ⟨p, hp, he⟩ := genPosK_sound h i hi
  rw [genA_eq12 hG (h12 i hi), ← he]
  have hl : E.lookup (arrN (recX R o p)) = some p := lookup_of_inv hE hp
  rw [hl]
  rfl

end CFSG.KC.YamakiGenPos

end
