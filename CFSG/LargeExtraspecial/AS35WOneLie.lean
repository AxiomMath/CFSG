module

public import CFSG.LargeExtraspecial.AS35WOneUse
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abD4
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeWardKleidman
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieCover
public import CFSG.Timmesfeld.Bridge.NoPolarConnected
public import CFSG.GH74.Uniqueness.Section4Bender
public import CFSG.GH74.KGroups.L34Tables
public import CFSG.GH74.GLS.Stage2.Final.ModelOneClass

public section

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Blueprint

namespace AS35W

theorem oneClass_G2
    {X : Type} [Group X] [Finite X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : LieModel X .G2 0 p f) : OneClass X :=
  fun z z' hz hz' => CFSG.GH74.GLS.IVK.Proofs2.ivk_4_7a_G2 X p f hp hp2 h z z' hz hz'

theorem oneClass_D4
    {X : Type} [Group X] [Finite X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : LieModel X .trialityD4 0 p f) : OneClass X :=
  fun z z' hz hz' => CFSG.GH74.GLS.IVK.Proofs2.ivk_4_7a_D4 X p f hp hp2 h z z' hz hz'

open CFSG.ComponentClassification in
theorem oneClass_Ree
    {X : Type} [Group X] {f : ℕ} (h : LieModel X .twistedG2 0 3 f) : OneClass X := by
  have hR := CFSG.ComponentClassification.RankTwoOddLie.reeTitsModel_of_lieModel h
  obtain ⟨hadm, a, hfa, -⟩ := id hR
  obtain ⟨-, -, -, -, -, h3⟩ := hadm
  have ha : 1 ≤ a := by omega
  subst hfa
  exact (LiteratureLocal.ward_kleidman_small_Ree_involution_centralizer_maximal a ha X hR).2.1.2

theorem oneClass_of_fusionIsBenderGroup {X : Type} [Group X]
    [Finite X] (h : Open.fusionIsBenderGroup X) : OneClass X := fun _ _ hx hy =>
  CFSG.GH74.Uniqueness.isConj_of_involutions_of_isBenderGroup
    (CFSG.Timmesfeld.Bridge.isBenderGroup_of_fusionIsBenderGroup h) hx hy

theorem oneClass_L34 {X : Type}
    [Group X] (h : LieModel X .PSL 3 2 2) : OneClass X := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.L34.equiv_of_lieModel h
  intro u v hu hv
  exact isConj_iff.2 (CFSG.GH74.KGroups.one_class_of_model _ e CFSG.GH74.KGroups.L34.x0
    CFSG.GH74.KGroups.L34.one_class_P u v hu hv)

theorem oneClass_L4U4 {X : Type} [Group X] [Finite X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : (p ^ f % 8 = 5 ∧ LieModel X .PSL 4 p f) ∨ (p ^ f % 8 = 3 ∧ LieModel X .PSU 4 p f)) :
    OneClass X :=
  CFSG.GH74.GLS.Stage2.Final.modelOneClass X p f hp hp2 h

end AS35W

end CFSG.LargeExtraspecial
