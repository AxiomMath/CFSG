module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9BLayer4
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

theorem gl83Generic4_9BLayer_holds : GL83Generic4_9BLayer := by
  intro hInn hWC p _ Y _ _ S R Γ x h hR0
  by_cases hall : ∀ K : Subgroup Y, IsComponentOf K ⊤ → K ≤ Γ
  · left
    have hE : CFSG.layer Y ≤ Γ :=
      sSup_le fun K hK => hall K ((CFSG.isComponent_iff_open K).mp hK)
    refine eq_top_iff.mpr ?_
    rw [← h.gen49bl_layer_sup_normalizer hInn hR0]
    exact sup_le hE h.normalizer_S
  · right
    push Not at hall
    obtain ⟨K, hK, hKΓ⟩ := hall
    refine ⟨K, ?_, h.gen49bl_le_centralizer hInn hWC hR0 hK hKΓ, hKΓ⟩
    have hΓ : Γ ≤ normalizer (K : Set Y) := fun g hg => by
      rw [mem_normalizer_iff_map_conj_eq]
      by_contra hne
      have hK' : IsComponentOf (K.map (MulAut.conj g).toMonoidHom) ⊤ :=
        (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) K).mpr hK
      have hK'Γ : ¬ K.map (MulAut.conj g).toMonoidHom ≤ Γ := fun hle => hKΓ fun k hk => by
        have h1 : g * k * g⁻¹ ∈ Γ := hle ⟨k, hk, rfl⟩
        have h2 := Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hg) h1) hg
        simpa [mul_assoc] using h2
      exact hne (h.gen49bl_eq_of_not_le hR0 hK' hK hK'Γ hKΓ)
    have hE : CFSG.layer Y ≤ normalizer (K : Set Y) :=
      CFSG.LocalCores.layer_le_normalizer ((CFSG.isComponent_iff_open K).mpr hK)
    rw [← normalizer_eq_top_iff]
    refine eq_top_iff.mpr ?_
    rw [← h.gen49bl_layer_sup_normalizer hInn hR0]
    exact sup_le hE (h.normalizer_S.trans hΓ)

end CFSG.LocalAnalysis.RankThreeTheoremC
