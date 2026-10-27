module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210QElem
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210QFaith
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210QStab
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L28Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} (h : Setting25 G t z z₁ ι zv R0 F)
  {φ : ↥(normalizer (Rgrp h : Set G)) →* A5WrTwo}

theorem l28Hyp_Aq (hzt : ¬ IsConj t z) (htz : IsConj t (t * z)) (hs : Lemma27Spec h φ) :
    L28Hyp (Aq h) (wq h) (psiq h hs) where
  elemAb := Aq_elemAb h
  card := card_Aq h
  surj := psiq_surjective h hs
  ker := ker_psiq h hs
  faithful := faithful_Aq h hs
  w_mem := wq_mem_Aq h
  w_ne_one := wq_ne_one h hzt htz
  stab := stab_Aq h hzt htz hs

end CFSG.EvenSporadicStandard.HNRecog.Harada
