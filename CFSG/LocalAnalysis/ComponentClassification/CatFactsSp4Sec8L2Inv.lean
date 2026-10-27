module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4L2Inv
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Sp4q
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsStab

public section

namespace CFSG.ComponentClassification.CatFactsSp4

open CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.AutL2Facts

theorem cfL2Inv : CFL2Inv := by
  intro Y₀ _ _ p f hp hp2 hf h5 hY φ hφ2 hφ1
  rcases hY with hY | ⟨rfl, rfl, -⟩
  swap
  · norm_num at h5
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  have hF' : Nat.card F = (p ^ f) ^ 2 := by rw [hF, ← pow_mul, mul_comm]
  have hpp : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, 2 * f, hp, hp.odd_of_ne_two hp2, by omega, hF⟩
  have h2 := two_ne_zero_of_isOddPrimePower hpp
  have hg : autEquiv e φ * autEquiv e φ = 1 := by rw [← map_mul, hφ2, map_one]
  have hg1 : autEquiv e φ ≠ 1 := fun h => hφ1 ((autEquiv e).injective (h.trans (map_one _).symm))
  have h := (l2InvConcl_pGammaL2 h2 hpp h5 hF' hg hg1).map (autEquiv e).symm
  rw [MulEquiv.symm_apply_apply] at h
  exact h

end CFSG.ComponentClassification.CatFactsSp4
