module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.GlueCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.GlueIso
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.GlueNonCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.NoFive

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup Glue

noncomputable def threeLocalData (hZ : center M10 = ⊥)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}
    (hRF : RuFacts L) (h3 : RuThreeFacts L) (h5 : RuFiveFacts L) (d : PartThreeData G L t) :
    ThreeLocalData ↥(centralizer ({d.r} : Set G)) where
  r := rCen d.r
  t := tCen d.config d.r_mem
  f := fCen d
  r_ord := by rw [orderOf_rCen]; exact d.r_ord
  r_central := rCen_mem_center d.r
  t_ord := orderOf_tCen d.config d.r_mem
  f_ord := by
    show orderOf (⟨d.f, _⟩ : CenG d.r) = 5
    rw [Subgroup.orderOf_mk]
    exact d.f_ord
  tf_comm := Subtype.ext (d.config.comm d.f d.f_mem).symm
  cen_odd := cen_odd_of d.config h3 d.r_mem d.r_ord
  cen_iso := cen_iso_of d.config h3 d.r_mem d.r_ord
  t_noncentral := t_noncentral_of d.config hRF h3 hZ d.r_mem d.r_ord
  f_nine := f_nine_of d
  f_five := f_five_of d
  count := count_of d h5
  noFive := noFive_of d h3 h5 d.inv_conj

theorem threeLocalData_of_partThree (hZ : center M10 = ⊥)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}
    (hRF : RuFacts L) (h3 : RuThreeFacts L) (h5 : RuFiveFacts L) (d : PartThreeData G L t) :
    Nonempty (ThreeLocalData ↥(centralizer ({d.r} : Set G))) :=
  ⟨threeLocalData hZ hRF h3 h5 d⟩

end CFSG.EvenSporadicStandard.RuStd.S2
