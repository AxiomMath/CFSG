module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Defs
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.LemmaR
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Perm5
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Util.OddCore
import CFSG.Adapters.GeneralizedFittingTop
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG.Blueprint CFSG.Open CFSG.EvenSporadicStandard.SolomonRed

theorem harada39One_of_cat (h : CatHaradaAS) : Harada39One := by
  intro G _ _ hK hZ t ht ⟨e⟩
  have hO : fusionOddCore G = ⊥ := fusionOddCore_eq_bot_of_zstar hZ
  rcases lemmaR rhyp_perm5 hO ht e with htc | ⟨hS, hswap | ⟨S, hF, -⟩⟩
  ·
    exfalso
    have ht1 : t = 1 :=
      eq_one_of_central_of_zstar hZ fun y => Subgroup.mem_center_iff.1 htc y
    rw [ht1, orderOf_one] at ht
    omega
  ·
    obtain ⟨S₁, S₂, hs⟩ := hswap
    left
    rw [(CFSG.Adapters.componentLayerOf_top_eq_componentClassification G).trans
      (CFSG.layer_eq_componentClassification G).symm]
    obtain ⟨φ⟩ := swapData_layer_equiv hS hs
    let ψ : ↥S₁ ≃* alternatingGroup (Fin 5) :=
      hs.iso.some.trans (Subgroup.equivMapOfInjective _ (embA e) (embA_injective e)).symm
    exact ⟨φ.trans (MulEquiv.prodCongr ψ ψ)⟩
  ·
    haveI := hF.simple
    have hcat : Catalog ↥S :=
      CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hK S (MonoidHom.id ↥S)
        Function.surjective_id
    obtain ⟨a, ha, b, hb, hab⟩ := hF.nonab
    exact h G S hF.normal hF.simple ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h' => hab (congrArg Subtype.val h')⟩
      hcat hF.cent t ht ⟨e⟩

end CFSG.EvenSporadicStandard.HSStd.InvCent
