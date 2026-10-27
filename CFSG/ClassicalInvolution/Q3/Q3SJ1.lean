module

public import CFSG.ClassicalInvolution.Q3.Q3SCriteria
import CFSG.Walter.J1Props.Hyp

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.ClassicalInvolution

theorem noWeakClassical3_of_jankoHyp {G : Type} [Group G] [Finite G]
    (h : CFSG.Walter.J1.JankoHyp G) : NoWeakClassical3 G := by
  refine NoWeakClassical3.of_conj_reps {h.t} (fun z hz => ?_) ?_
  · obtain ⟨g, hg⟩ := h.exists_conj_eq_t hz
    exact ⟨h.t, rfl, (isConj_iff.mpr ⟨g, hg⟩).symm⟩
  · intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact NoWeakClassical3At.of_index_two h.F (index_F_eq_two h) h.t_not_mem

theorem noWeakClassical3_J1 : NoWeakClassical3 CFSG.Blueprint.NativeSporadic.J1 := by
  have h := noWeakClassical3_of_jankoHyp CFSG.Walter.J1Props.jankoHyp
  rw [← properTwoGenCoreJ1_eq_walterJ1] at h
  exact NoWeakClassical3.of_mulEquiv CFSG.ProperTwoGeneratedCore.j1_exact_model_equiv.symm h

end CFSG.ClassicalInvolution.Q3
