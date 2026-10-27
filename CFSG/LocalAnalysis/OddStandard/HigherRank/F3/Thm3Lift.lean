module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Thm2Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Tools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Lift
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalInvolution.Generic.StepDefs
public import CFSG.ClassicalInvolution.Q3.Step
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogSchreierCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesC
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Two
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporMult
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.OddSelector
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdFamilies
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.Monster.B.TwoA.Base.FourNorm
public import CFSG.Monster.SteinbergMY443SimpleIsomorphism
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.Walter.J1
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckW
public import Certificates.Certificate10025
public import Certificates.Certificate7233Base
public import Certificates.Certificate8171
public import Certificates.Kernel.J4Count.FixC
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification CFSG.ComponentClassification.HarrisLit

theorem exists_lift_component {X : Type} [Group X] [Finite X] {w : X}
    {k : ↥(centralizer ({w} : Set X))} (hk2 : orderOf (k : X) = 2) {Y : Subgroup (MBar w)}
    (hY : IsComponent Y) (hkY : (QuotientGroup.mk k : MBar w) ∈ Y)
    (hYk : ∀ y ∈ Y, y * QuotientGroup.mk k = QuotientGroup.mk k * y) :
    ∃ J : Subgroup X, IsTwoComponentIn J (centralizer {w} ⊓ centralizer {(k : X)}) ∧
      (k : X) ∈ J ∧ Nonempty (↥J ⧸ pPrimeCore 2 ↥J ≃* ↥Y ⧸ pPrimeCore 2 ↥Y) := by
  have hres : ∀ {Y C : Subgroup (MBar w)}, Y ≤ C →
      IsPComponent 2 Y → IsPComponent 2 (Y.subgroupOf C) := by
    intro Y C hYC h
    rw [← isTwoComponent_iff_isPComponent] at h ⊢
    exact ⟨h.1.subgroupOf, isTwoQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hYC).symm h.2⟩
  have hpc : ∀ {Y : Subgroup (MBar w)}, IsComponent Y → IsPComponent 2 Y := fun hY =>
    (isTwoComponent_iff_isPComponent _).mp
      ((isTwoComponent_iff_isComponent (pPrimeCore_quotient_pPrimeCore_eq_bot 2) _).mpr hY)
  have hYle : Y ≤ centralizer {(QuotientGroup.mk ⟨(k : X), k.2⟩ : MBar w)} := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    exact hYk y hy
  obtain ⟨J, hJle, hJp, hkJ, -, g, hg, hgk⟩ :=
    Lemma47.exists_lift_two_component k.2 hk2 hYle (hres hYle (hpc hY)) hkY
  exact ⟨J, (isTwoComponentIn_iff hJle).mpr hJp, hkJ,
    GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective g hg hgk⟩

theorem false_of_four_group (hT2 : Theorem2ClassB) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog G) (hcat : ¬ Blueprint.Catalog G) {w k : G}
    (hw2 : orderOf w = 2) (hk2 : orderOf k = 2) (hwk : w * k = k * w) (hne : k ≠ w)
    {J₁ J₂ : Subgroup G} (hJ₁ : IsTwoComponentIn J₁ (centralizer {w} ⊓ centralizer {k}))
    (hJ₂ : IsTwoComponentIn J₂ (centralizer {w} ⊓ centralizer {w * k})) (hkJ₁ : k ∈ J₁)
    (hwkJ₂ : w * k ∈ J₂) (hM : IsMTypeSchur 3 ↥J₁) (hS : ClassBShape ↥J₁) : False := by
  have hww : w * w = 1 := by
    have h := pow_orderOf_eq_one w
    rwa [hw2, pow_two] at h
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hw2
    omega
  have hk1 : k ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hk2
    omega
  have hwkne : w * k ≠ 1 := fun h => hne (by
    rw [eq_inv_of_mul_eq_one_right h, hwinv])
  have hkwk : k ≠ w * k := fun h => hw1 (by
    have h1 := h.symm
    rwa [mul_eq_right] at h1)
  have hV := Lemma47.fourGroup_closure_pair hw2 hk2 hne hwk
  have hCV := Lemma47.centralizer_closure_pair w k
  have hkV : k ∈ (closure {w, k} : Subgroup G) :=
    subset_closure (Set.mem_insert_of_mem _ rfl)
  have hwkV : w * k ∈ (closure {w, k} : Subgroup G) :=
    mul_mem (subset_closure (Set.mem_insert _ _)) hkV
  have hJ₁V : IsTwoComponentIn J₁ (centralizer ((closure {w, k} : Subgroup G) : Set G)) :=
    hCV ▸ hJ₁
  have hJ₂V : IsTwoComponentIn J₂ (centralizer ((closure {w, k} : Subgroup G) : Set G)) := by
    rw [hCV, ← T23.centralizer_inf_mul]
    exact hJ₂
  exact hT2 G hnonab hK hcat (closure {w, k}) hV.1 hV.2 k hkV (w * k) hwkV hk1 hwkne hkwk
    J₁ J₂ hJ₁V hJ₂V hkJ₁ hwkJ₂ hM hS

end CFSG.OddStandard.HigherRank.F3
