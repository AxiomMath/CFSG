module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepHStmts
public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Ree

public section

namespace CFSG.OddStandard.GH71.S55

open CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

theorem mem_of_normalizesPSub {Y : Type} [Group Y] {r : ℕ} {b : MulAut Y}
    (h : NormalizesPSub r b) :
    ∃ E : Subgroup Y, E ≠ ⊥ ∧ IsPGroup r ↥E ∧ ∀ x ∈ E, b x ∈ E := by
  obtain ⟨E, hE1, hEp, hEb⟩ := h
  refine ⟨E, hE1, hEp, fun x hx => ?_⟩
  have h1 := Subgroup.mem_map_of_mem b.toMonoidHom hx
  rwa [hEb] at h1


theorem ordPInner_fd4d : OrdPInner FD4d := by
  intro r p Y _ _ hr _ hp hp5 _ hY b hb
  obtain ⟨f, hf, hm⟩ := hY
  by_cases hin : b ∈ (MulAut.conj : Y →* MulAut Y).range
  · exact Or.inr hin
  · exact Or.inl (mem_of_normalizesPSub (d4_ordP_noninner hr hf hm hp (by omega) b hb hin).1)

theorem ordPInner_freed : OrdPInner FReed := by
  intro r p Y _ _ _ _ hp hp5 _ hY b hb
  obtain ⟨rfl, f, -, hm⟩ := hY
  by_cases hin : b ∈ (MulAut.conj : Y →* MulAut Y).range
  · exact Or.inr hin
  · exact Or.inl (mem_of_normalizesPSub
      (ree_ordP_noninner_of_lieModel hm hp (by omega) b hb hin).1)

end CFSG.OddStandard.GH71.S55
