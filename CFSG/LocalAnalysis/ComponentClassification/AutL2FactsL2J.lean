module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L2b
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsJModel

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

theorem map_centralizer_equiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (S : Subgroup G) :
    (centralizer (S : Set G)).map φ.toMonoidHom = centralizer ((S.map φ.toMonoidHom : Subgroup H) :
      Set H) := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · rintro h _ ⟨s, hs, rfl⟩
    have := h s hs
    apply φ.symm.injective
    simpa using this
  · intro h s hs
    have := h (φ s) ⟨s, hs, rfl⟩
    apply φ.injective
    simpa using this

theorem cfL2J : GSThmB.CFL2J := by
  intro Y _ _ p f hp hp2 hf hY T _ R hR hTR E hER hE2 hE8
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  set Φ := (autEquiv e).toMonoidHom
  have hΦ : Function.Injective Φ := (autEquiv e).injective
  have hTR' : ((sylowMap e T : Sylow 2 (PSL2 F)) : Subgroup (PSL2 F)).map (incl F) ≤ R.map Φ := by
    rw [coe_sylowMap, ← map_autEquiv_innOf]
    exact Subgroup.map_mono hTR
  have h := l2J_model hp hp2 hf hF (sylowMap e T) (R.map Φ) (hR.map _) hTR' (E.map Φ)
    (Subgroup.map_mono hER) (by
      rintro _ ⟨x, hx, rfl⟩
      change autEquiv e x * autEquiv e x = 1
      rw [← map_mul, hE2 x hx, map_one])
    (by rw [Subgroup.card_map_of_injective hΦ, hE8])
  rw [coe_sylowMap, ← map_autEquiv_innOf, ← map_centralizer_equiv,
    ← Subgroup.map_inf_eq _ _ _ hΦ, ← Subgroup.map_sup,
    Subgroup.map_le_map_iff_of_injective hΦ] at h
  exact h

end CFSG.ComponentClassification.AutL2Facts
