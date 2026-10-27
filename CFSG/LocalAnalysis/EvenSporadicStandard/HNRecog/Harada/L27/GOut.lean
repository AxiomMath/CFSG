module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GOutLemmas
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.VOutside
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.Abstract
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GSmall

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA CFSG.EvenSporadicStandard.HNRecog
  CFSG.RankThree.Literature.FSmith

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G}

theorem lemma27Out_of_inputs [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Blueprint.Catalog)
    (hL : SmallSimpleLookup) (h : Setting25 G t z z₁ ι zv R0 F) (hzt : ¬ IsConj t z)
    (htz : IsConj t (t * z)) (hS5 : CzS5 t z R0) : Lemma27Out h := by
  obtain ⟨n, hn, hnz⟩ := h.exists_n_z₁
  have hdata := wrData_Xgrp h hzt htz hS5 hn hnz
  have hsec : SmallSections ↥(Xgrp h) :=
    smallSections_of_kGroup (isKGroupCat_Xgrp hnonab hKP h) hS hL hdata.card_dvd hdata.card_le
  obtain ⟨e⟩ := abstract_A5WrTwo hdata hsec
  obtain ⟨eF⟩ := hdata.F_iso
  let φ : ↥(normalizer (Rgrp h : Set G)) →* A5WrTwo :=
    (e : ↥(Xgrp h) →* A5WrTwo).comp (rho0 h).rangeRestrict
  have hφ : ∀ g, φ g = e ((rho0 h).rangeRestrict g) := fun g => rfl
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_⟩
  · exact e.surjective.comp (MonoidHom.rangeRestrict_surjective (rho0 h))
  · ext g
    rw [MonoidHom.mem_ker, hφ, map_eq_one_iff e e.injective, Subtype.ext_iff,
      MonoidHom.coe_rangeRestrict, Subgroup.coe_one, rho0_eq_one_iff h g,
      Subgroup.mem_subgroupOf]
  · intro m hm H
    exact mem_Rgrp_of_comm_mem_zpowers h hm H
  · intro m hm hmA hmR
    rw [hφ, rangeRestrict_eq_vbar h hn hnz hm hmA hmR]
    exact not_mem_commutator_A5WrTwo_of_centralizer e (Fbar h n) eF hdata.v_sq hdata.v_ne_one
      hdata.F_comm hdata.centralizer_le
  · obtain ⟨ePS⟩ := Pgrp_iso h hzt htz hS5
    have hmap : Subgroup.map φ
        (Subgroup.subgroupOf (NVgrp t z) (normalizer (Rgrp h : Set G))) =
        (Pgrp h).map (e : ↥(Xgrp h) →* A5WrTwo) := by
      rw [← map_NVgrp_eq_Pgrp h hzt htz, Subgroup.map_map]
    exact ⟨((MulEquiv.subgroupCongr hmap).trans
      (Subgroup.equivMapOfInjective (Pgrp h) (e : ↥(Xgrp h) →* A5WrTwo) e.injective).symm).trans
        ePS⟩

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
