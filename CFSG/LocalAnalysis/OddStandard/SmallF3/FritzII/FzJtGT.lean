module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzJtMod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusCl

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup Certificates.FzJ36 Certificates.FzFus Certificates.FzJt

theorem fzInvolT_holds : FzInvolT := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ hset v hv hv2 hv1 hvZ
  obtain ⟨ht2, h1, h2, h12⟩ := fzFus_rels hset
  obtain ⟨π, hd⟩ := fzfus_dict hset.shape ht2 h1 h2 h12
  obtain ⟨hA, hC, hR, hS⟩ := fzFus_facts
  obtain ⟨-, -, -, hrz, hoI, hoJ, hoK⟩ := fzfus_classes hA hC hR hS hset hd
  obtain ⟨m, rfl⟩ := hd.mem_T₂_iff.mp hv
  have hinv : IsInvM m := (hd.isInvM_iff m).mpr ⟨by rw [← pow_two]; exact hv2, hv1⟩
  have hnZ : ¬ InZ m := fun h => hvZ ((fzJt_mem_calZ_iff hd m).mpr h)
  have hcl := hd.cl_eq hC hinv
  have key : ConjClasses.mk (π (rep (clsOf m))) = ConjClasses.mk t := by
    rcases List.mem_append.mp (clsOf_of_not_inZ m hinv hnZ) with h | h
    · exact hrz _ h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h <;> rw [h]
      exacts [hoI, hoJ, hoK]
  exact (ConjClasses.mk_eq_mk_iff_isConj.mp (hcl.trans key)).symm

end CFSG.OddStandard.SmallF3.FritzII
