module

public import Certificates.Data.Kernel.AlphaWfK

public section

namespace CFSG.AGLEmbedding.R3

theorem NMod.wf_of_wfK {p : Nat} {m : NMod} (h : m.wfK p = true) : m.wf p = true := by
  unfold NMod.wfK at h
  unfold NMod.wf
  rw [Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  have h3 := h.2
  rw [List.all_eq_true]
  intro c hc
  revert h3 hc
  cases allVecs p m.basis.length with
  | nil => intro _ hc; cases hc
  | cons d ds =>
    intro h3 hc
    rw [Bool.and_eq_true, beq_iff_eq] at h3
    rw [Bool.or_eq_true]
    rcases List.mem_cons.1 hc with rfl | hc
    · exact Or.inl h3.1
    · right
      rw [h3.2] at hc
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hc
      exact List.any_eq_true.2 ⟨q, hq, beq_self_eq_true _⟩

end CFSG.AGLEmbedding.R3

end
