module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GStab2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.Data

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA CFSG.EvenSporadicStandard.HNRecog
  CFSG.RankThree.Literature.FSmith

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G}

theorem wrData_Xgrp (h : Setting25 G t z z₁ ι zv R0 F) (hzt : ¬ IsConj t z)
    (htz : IsConj t (t * z)) (hS5 : CzS5 t z R0) {n : G}
    (hn : n ∈ normalizer (ι.range : Set G)) (hnz : n * z₁ * n⁻¹ = z) :
    WrData ↥(Xgrp h) (rhoX h) (wvec h) (Pgrp h) (Fbar h n) (vbar h hn) :=
  ⟨fun a b hab => Subtype.ext (Subtype.ext hab), finrank_Wsp h, card_Xgrp_dvd h,
    card_Xgrp_le h hzt htz hS5, wvec_ne_zero h hzt htz, Pgrp_fix h, Pgrp_iso h hzt htz hS5,
    Fbar_iso h hn hnz, Fbar_fpf h hn hnz, vbar_mul_self h hn, vbar_ne_one h hn hnz,
    Fbar_comm h hn hnz, centralizer_vbar_le h hn hnz⟩

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
