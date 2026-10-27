module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Defs
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.Cent4
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.Recog3
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.Struct
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.T1
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Util.OddCore
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG CFSG.Blueprint CFSG.Open CFSG.EvenSporadicStandard.SolomonRed

theorem harada39Two_of_cat (h : CatHaradaTwoAS) (h4 : CatCentFour) : Harada39Two := by
  intro G _ _ hK hZ t v ht hv J hJ hdisj hcomm hcent hcv hctv
  have hO : fusionOddCore G = ⊥ := fusionOddCore_eq_bot_of_zstar hZ
  have cfg : H2Cfg G t v J :=
    { t_order := ht, v_sq := hv, J_iso := hJ, disj := hdisj, comm := hcomm, cent_t := hcent,
      cent_v := hcv, cent_tv := hctv,
      center := fun x hx => eq_one_of_central_of_zstar hZ hx,
      odd := fun N hN hodd => by
        have h1 : N ≤ fusionOddCore G := le_sSup ⟨hN, hodd⟩
        rw [hO] at h1
        exact le_bot_iff.1 h1 }
  rcases cfg.normal_or_fitting_eq_bot with hN | hF
  · exact Or.inl hN
  · right
    rcases cfg.struct hF with ⟨L, hL, hEL⟩ | ⟨S₁, hs⟩
    ·
      exfalso
      haveI : IsSimpleGroup ↥L := component_isSimple hF hL
      have hcat : Catalog ↥L :=
        CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hK L (MonoidHom.id ↥L)
          Function.surjective_id
      have hLn : L.Normal := by
        rw [← hEL]
        haveI : (layer G).Characteristic := CFSG.LocalCores.layer_characteristic
        infer_instance
      obtain ⟨a, ha, b, hb, hab⟩ := component_nonab hF hL
      exact h G L hLn inferInstance
        ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h' => hab (congrArg Subtype.val h')⟩ hcat
        (by rw [← hEL]; exact centralizer_layer_eq_bot hF) t v ht hv J hJ hdisj hcomm hcent hcv
        hctv
    ·
      haveI : IsSimpleGroup ↥S₁ := component_isSimple hF hs.comp₁
      have hcat : Catalog ↥S₁ :=
        CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hK S₁ (MonoidHom.id ↥S₁)
          Function.surjective_id
      obtain ⟨φ⟩ := cfg.exists_equiv_alt5 h4 inferInstance (component_nonab hF hs.comp₁) hcat
        hs.V_le hs.inf_le
      exact H2Two.exists_equiv cfg hF hs φ

end CFSG.EvenSporadicStandard.HSStd.InvCent
