module

public import CFSG.ClassicalInvolution.SmallCases.NobqCriteria
import CFSG.Walter.J1Props.Hyp
public import CFSG.ClassicalInvolution.Generic.Generation.Endgame
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.J1ModelTransport

public section

namespace CFSG.ClassicalInvolution.Nobq

theorem noUniqueInvNormal_of_jankoHyp {G : Type} [Group G] [Finite G]
    (h : CFSG.Walter.J1.JankoHyp G) : NoUniqueInvNormal G := by
  refine NoUniqueInvNormal.of_conj_reps {h.t} (fun z hz => ?_) ?_
  · obtain ⟨g, hg⟩ := h.exists_conj_eq_t hz
    exact ⟨h.t, rfl, g⁻¹, by rw [← hg]; group⟩
  · intro s hs _ N
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact not_uniqueInvNormal_of_index_two h.F (CFSG.ClassicalInvolution.index_F_eq_two h)
      h.t_not_mem

theorem noUniqueInvNormal_J1 : NoUniqueInvNormal CFSG.Blueprint.NativeSporadic.J1 := by
  refine NoUniqueInvNormal.of_mulEquiv CFSG.ProperTwoGeneratedCore.j1_exact_model_equiv.symm ?_
  have h := noUniqueInvNormal_of_jankoHyp CFSG.Walter.J1Props.jankoHyp
  rw [← CFSG.ClassicalInvolution.properTwoGenCoreJ1_eq_walterJ1] at h
  exact h

end CFSG.ClassicalInvolution.Nobq
