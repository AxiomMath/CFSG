module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L2b
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsAModel

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

theorem cfL2A : GSThmB.CFL2A := by
  intro Y _ _ p f hp hp2 hf hY R D₁ E hR hD₁R hER hED hDE hE1 ⟨T, ⟨φ⟩⟩
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Φ := (autEquiv e).toMonoidHom
  have hΦ : Function.Injective Φ := (autEquiv e).injective
  have hED' : ∀ y ∈ E.map Φ, ∀ d ∈ D₁.map Φ, y * d = d * y := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨d, hd, rfl⟩
    have h := mem_centralizer_iff.mp (hED hy) d hd
    change autEquiv e y * autEquiv e d = autEquiv e d * autEquiv e y
    rw [← map_mul, ← map_mul, h]
  have hDE' : D₁.map Φ ⊓ E.map Φ = ⊥ := by
    rw [← Subgroup.map_inf_eq _ _ _ hΦ, hDE, Subgroup.map_bot]
  have hE1' : E.map Φ ≠ ⊥ := by
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hΦ]
  have φ' : D₁.map Φ ≃* (sylowMap e T : Subgroup (PSL2 F)) :=
    ((autEquiv e).subgroupMap D₁).symm.trans (φ.trans ((e.subgroupMap _).trans
      (MulEquiv.subgroupCongr (coe_sylowMap e T).symm)))
  obtain ⟨hcard, h8, T', hT'⟩ := l2A_model hp hp2 hf hF (R.map Φ) (D₁.map Φ) (E.map Φ)
    (hR.map _) (Subgroup.map_mono hD₁R) (Subgroup.map_mono hER) hED' hDE' hE1' (sylowMap e T) φ'
  refine ⟨?_, ?_, ?_⟩
  · rwa [Subgroup.card_map_of_injective hΦ] at hcard
  · intro T₂
    rw [card_sylowMap] at h8
    rwa [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity T]
  · have hT₃ : ((Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective T' :
        Sylow 2 Y) : Subgroup Y) = (T' : Subgroup (PSL2 F)).map e.symm.toMonoidHom :=
      Sylow.coe_mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective T'
    refine ⟨Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective T', ?_⟩
    have hTT : ((T' : Subgroup (PSL2 F)).map e.symm.toMonoidHom).map e.toMonoidHom = T' := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id (T' : Subgroup (PSL2 F))
      ext x
      simp
    rw [← Subgroup.map_le_map_iff_of_injective hΦ, map_autEquiv_innOf, Subgroup.map_sup, hT₃,
      hTT]
    exact hT'

end CFSG.ComponentClassification.AutL2Facts
