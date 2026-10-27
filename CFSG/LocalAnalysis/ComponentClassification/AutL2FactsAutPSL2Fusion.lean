module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisFusion
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisTransport
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFusion

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

theorem cfAutPSL2Fusion : HarrisLit.AutPSL2FusionInput := by
  intro Y _ _ p f hp hp2 hfe h16 hY K hIK T hTK hP v hv ι hι hι2 x hx hx2
  obtain ⟨F, _, _, Φ, hH, hI, hFA, hFAany⟩ := harris_context hp hp2 hfe h16 hY
  have hK' : pGammaL2PSLRange F ≤ K.map Φ.toMonoidHom := hI ▸ Subgroup.map_mono hIK
  have hT' : IsSylowIn (T.map Φ.toMonoidHom) (K.map Φ.toMonoidHom) :=
    ((isSylowIn_iff T K).mpr ⟨hTK, hP⟩).map Φ
  have hv' := SylowShape.pushforward Φ hI hFA hFAany hv
  have hι' : Φ ι ∈ (T.map Φ.toMonoidHom ⊓ pGammaL2PSLRange F) ⊓
      centralizer ((T.map Φ.toMonoidHom ⊓ pGammaL2PSLRange F : Subgroup (PGammaL2 F)) :
        Set (PGammaL2 F)) := by
    have := Subgroup.mem_map_of_mem Φ.toMonoidHom hι
    rwa [map_inf_mulEquiv, map_inf_mulEquiv, map_centralizer_subgroup, map_inf_mulEquiv,
      hI] at this
  have hx' : Φ x ∈ (T.map Φ.toMonoidHom ⊓ pGammaL2PSLRange F) ⊔ zpowers (Φ v) := by
    have := Subgroup.mem_map_of_mem Φ.toMonoidHom hx
    rwa [Subgroup.map_sup, map_inf_mulEquiv, hI, map_zpowers_mulEquiv] at this
  obtain ⟨k', hk'K, hk'⟩ := hH.fusion hK' hT' hv' hι' (by rwa [MulEquiv.orderOf_eq]) hx'
    (by rwa [MulEquiv.orderOf_eq])
  have hkK : Φ.symm k' ∈ K := (Subgroup.mem_map_equiv).mp hk'K
  have hpow : Φ v ^ (orderOf (Φ v) / 2) = Φ (v ^ (orderOf v / 2)) := by
    rw [MulEquiv.orderOf_eq, map_pow]
  have key : ∀ w : MulAut Y, k' * Φ x * k'⁻¹ = Φ w →
      Φ.symm k' * x * (Φ.symm k')⁻¹ = w := by
    intro w hw
    apply Φ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hw
  refine ⟨Φ.symm k', hkK, ?_⟩
  rcases hk' with h | h | h
  · exact Or.inl (key _ h)
  · exact Or.inr (Or.inl (key _ (by rw [h, hpow])))
  · exact Or.inr (Or.inr (key _ (by rw [h, hpow, map_mul])))

end CFSG.ComponentClassification.AutL2Facts
