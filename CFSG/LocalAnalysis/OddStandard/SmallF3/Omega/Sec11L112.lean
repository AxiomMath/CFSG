module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Model

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma112_of (hp : Asc82Pre11) (h111N : Asc82Lemma111N) : Asc82Lemma112 := by
  intro G _ _ t L S z K1 K2 T R hctx
  obtain ⟨Alt, φ, hm⟩ := sec11_model_of hp hctx
  have e : ↥(secMstar t S L) ≃* ↥Alt := hm.perm.autInEquiv le_rfl
  rcases Sec11Model.cent_T_Q hp hctx hm with ⟨hAlt, hC⟩ | ⟨hAlt, r, hr2, hC, hD8, hract⟩
  · exact Or.inl ⟨⟨e.trans (MulEquiv.subgroupCongr hAlt)⟩, hC⟩
  · have hperm := hm.perm.toIsPermModuleMod (le_refl (secM t S L))
    rw [hAlt] at hperm
    exact Or.inr ⟨⟨e.trans ((MulEquiv.subgroupCongr hAlt).trans Subgroup.topEquiv)⟩, r, hr2, hC,
      hD8, φ, hperm, 0, 1, by decide, hract⟩

end CFSG.OddStandard.SmallF3.Omega
