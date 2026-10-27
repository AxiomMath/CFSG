module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.QuotKd
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.QuotIV2

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

theorem false_of_two_eq {C : Type} [Group C] [Finite C] {c : CInv C} {t : C}
    {R J K O Y Y0 : Subgroup C} (hC : CCore c) (hR : RData c R) (hJ : JData c t R J)
    (hK : KDataC c t R J K O Y) (hY0 : Y0Data Y0) (hF : U42Facts)
    (hSch : CatalogOuterSolvable) (hB : DS81Lemma210Strong) (hcat : CatSections C) : False := by
  obtain ⟨L1, hcomp, hlayer, hRle⟩ := exists_component hC hR hJ hK hF
  have h : UniqueComp c R L1 := ⟨hcomp, hlayer, hRle⟩
  haveI := L1_simple hC h
  refine hB c.Qt L1 (L1_nonabelian hC h) (catalog_L1 hC hcat h) (exists_cover hR h)
    (two_pow_19_dvd hC hcat hSch h hY0) (not_two_pow_21_dvd hC L1) (c.qmap t)
    (qmap_t_mem hJ h) (orderOf_qmap_t hJ) _ rfl (card_O2In hR hJ h) (sq_O2In hR hJ h)
    (cent_O2In hR hJ h) ?_
  rw [O2In_eq_bar_R hR hJ h]
  exact quot_cond hC hR hJ hK hF hcat hSch h

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
