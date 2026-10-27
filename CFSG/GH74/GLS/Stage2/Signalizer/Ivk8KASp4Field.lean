module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KASp4Easy
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4CoreField

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.CatFactsSp4
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem kaSp4Field_thm : KASp4Field := by
  intro F _ _ hodd A σ hσ1 hσ2 ⟨d, hd⟩ _hcard
  have hoddc : Odd (Nat.card F) := by
    have : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hodd)
  obtain ⟨hqs, -⟩ := fixOf_conjSp_fieldSp hoddc A σ hσ2 hσ1 d hd
  refine kaAll_sp4_of_fix hodd (conjSp 2 F A * fieldSp 2 F σ) (conjAut 2 F A * fieldAut 2 F σ)
    (fieldAlpha_proj A σ) (Subgroup.isPerfect_iff.mp hqs.1) ?_
  refine ka_hRp_of_quasisimple hodd (conjSp 2 F A * fieldSp 2 F σ) hqs fun z hz => ?_
  exact field_centralizer_scalar hodd A σ hσ1 hσ2 d hd z fun g hg => (hz g hg).symm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
