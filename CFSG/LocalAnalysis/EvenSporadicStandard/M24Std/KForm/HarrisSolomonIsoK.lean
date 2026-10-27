module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Cases
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Cat
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Reduction.Quotient

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem harrisSolomonZ2S6IsoK_of_cat (hcat : CatZ2S6) : HarrisSolomonZ2S6IsoK := by
  intro X _ _ hK z hz hζ
  obtain ⟨ζ⟩ := hζ
  have hR := KForm.Reduction.rhyp_perm6
  have hB := KForm.Reduction.fusionOddCore_prod_eq_bot_of_rhyp hR
    KForm.Reduction.even_natCard_alt6
  obtain ⟨hO, hK', hz', hζ'⟩ := KForm.Mod.quotient_setting_mod hK hz hB ζ
  obtain ⟨ζ'⟩ := hζ'
  have hMod := KForm.Mod.modData_of_quotient hz' hR ζ'
  rcases KForm.Mod.layer_cases_mod hR hO hz' _ hMod.surj hMod.odd with
    h1 | h2 | ⟨S, hSn, hSs, hSc, hSe⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · haveI : IsSimpleGroup ↥S := hSs
    have hC : Catalog ↥S :=
      CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hK' S (MonoidHom.id ↥S)
        Function.surjective_id
    have hsoc := hcat (X ⧸ fusionOddCore X) S hSn hSs hC hSc
      (QuotientGroup.mk' (fusionOddCore X) z) hz' ⟨ζ'⟩
    unfold Z2S6Socle at hsoc
    rcases hsoc with h8 | hU42 | hL52 | hU52 | hS42 | hU43
    · exact Or.inr (Or.inr (Or.inl (hSe ▸ h8)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hSe ▸ hU42))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hSe ▸ hL52)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hSe ▸ hU52))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hSe ▸ hS42)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hSe ▸ hU43)))))))

theorem harrisSolomonZ2S6IsoK_of_inputs
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Catalog)
    (hBT : EvenLieInvolutionTwoConstrained) (hEL : EvenOuterA6LeafMod)
    (hOB : OddLieA6TwoComponent) (hL : OddA6ModLeaf) (hSpor : SporadicZ2S6Leaf) :
    HarrisSolomonZ2S6IsoK :=
  harrisSolomonZ2S6IsoK_of_cat (catZ2S6_of_inputs hSch hBT hEL hOB hL hSpor)

end CFSG.EvenSporadicStandard.M24Std
