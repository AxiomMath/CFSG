module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.Noncat
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.CatFS46
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.CatFS412
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.ChildrenHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Sol78LitHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.OrderFacts

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus
open CFSG.ComponentClassification.GrSLit (HeldNotProperFixedInput)
open CFSG.ComponentClassification.GrSLit.L34Sec5S (SuzONanNotProperFixedCatalog)

section NoncatHered

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem oddCore_bot_of_noncat_of_uhered (hU : Balance.UHered G)
    (hna : ∃ a b : G, a * b ≠ b * a) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hnc : ¬ CFSG.Blueprint.Catalog G) :
    ∀ z : G, orderOf z = 2 →
      CFSG.Open.standardComponentOddCore (centralizer ({z} : Set G)) = ⊥ := by
  intro z hz
  by_contra hne
  rcases hU G (CFSG.SignalizerFunctorTheorem.IsSectionOf.refl G) hna hkp z hz hne with
    hodd | ⟨n, h7, -, ⟨e⟩⟩
  · exact hnc (catalog_of_oddLieType hodd)
  · exact hnc (catalog_of_alt (by omega) e)

theorem catalog_of_childL34WHered (hL34 : ChildL34WHered) (hU : Balance.UHered G)
    (hna : ∃ a b : G, a * b ≠ b * a) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {L : Subgroup G} (hL : CFSG.Open.standardComponentIsStandard L)
    (h : LieModel (↥L ⧸ center ↥L) .PSL 3 2 2) : CFSG.Blueprint.Catalog G := by
  rcases hL34 G hU L ⟨inferInstance, hna, hkp, hL⟩ h with hodd | hsp | hsp | hsp
  · exact catalog_of_oddLieType hodd
  all_goals exact catalog_of_isSporadic hsp

theorem catalog_of_childHeWHered (hHe : ChildHeWHered) (hU : Balance.UHered G)
    (hna : ∃ a b : G, a * b ≠ b * a) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {L : Subgroup G} (hL : CFSG.Open.standardComponentIsStandard L)
    (h : IsSporadic (↥L ⧸ center ↥L) .He) : CFSG.Blueprint.Catalog G := by
  exact catalog_of_oddLieType (hHe G hU L ⟨inferInstance, hna, hkp, hL⟩ h)

end NoncatHered

theorem sol78Thm46Noncat_of_inputs_of_uhered (hRK : Outer.RankTwoStdRec)
    (thm24_1 : Sol78Thm24_1Use)
    (hExc : ∀ (X : Type) [Group X], 29120 ≤ Nat.card X → Nat.card X ≠ 4030387200 →
      ¬ Recognition.Exact.EvenStandardException X)
    (hChL34 : ChildL34WHered) (hChHe : ChildHeWHered)
    (hCTE : CTEvenResidualStatement) (hSmall : CTEvenSmallLieStatement) (hord : Thm46Orders)
    (hSuzRow : SuzCentralTwo) (hSuz : Sol78Thm46SuzEven)
    {G : Type} [Group G] [Finite G] (hU : Balance.UHered G) (hs : IsSimpleGroup G)
    (hna : ∃ a b : G, a * b ≠ b * a) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hnc : ¬ CFSG.Blueprint.Catalog G) (P : Subgroup G) (hP : SolStd P)
    (hPq : CFSG.IsQuasisimple ↥P)
    (hty : (∃ n : ℕ, 2 ≤ n ∧ LieModel (↥P ⧸ center ↥P) .PSL 3 2 n) ∨
      IsSporadic (↥P ⧸ center ↥P) .Suz ∨ IsSporadic (↥P ⧸ center ↥P) .He)
    (hsuz : IsSporadic (↥P ⧸ center ↥P) .Suz → Even (Nat.card ↥(center ↥P))) : False := by
  haveI := hs
  have hL := standardComponentIsStandard_of_solStd hP hPq
  have hcore := oddCore_bot_of_noncat_of_uhered hU hna hkp hnc
  haveI : IsSimpleGroup (↥P ⧸ center ↥P) := hPq.2.1
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(centralizer (P : Set G))) := inferInstance
  rcases hty with ⟨n, hn, hL3⟩ | hSz | hHe
  · rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have h2 : n = 2 := by omega
      subst h2
      exact hnc (catalog_of_childL34WHered hChL34 hU hna hkp hL hL3)
    · have hgt := hord.psl3_gt _ n hn3 hL3
      have hcyc := isCyclic_sylow_of_noncat hRK thm24_1 hna hkp hnc hP hPq
        (not_card_dvd_95040_of_gt hgt) S
      have hsp := sporadicRep_of_even_cyclic hCTE hSmall hna hkp hnc hL hcore S hcyc
        (Or.inl ⟨.PSL, 3, n, hL3.admissible, hL3⟩)
        (hExc _ (by omega) (hord.psl3_ne_he _ n hn3 hL3))
      exact hord.psl3_not_sporadic _ n hn3 hL3 hsp
  · have hev := hsuz hSz
    have hgt := hord.suz_gt _ hSz
    have hcyc := isCyclic_sylow_of_noncat hRK thm24_1 hna hkp hnc hP hPq
      (not_card_dvd_95040_of_gt hgt) S
    obtain ⟨t, ht2, hcomp⟩ := hP.exists_involution
    have hZ2 : IsPGroup 2 ↥(center ↥P) := isPGroup_center_of_balance hP ht2 hcomp (hcore t ht2)
    have hdvd := hSuzRow ↥P ((CFSG.Foundations.SteinbergCA.quasisimple_iff ↥P).2.2.1.1 hPq) hZ2 hSz
    have hZ : Nat.card ↥(center ↥P) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact absurd (by rw [h]; exact odd_one) (Nat.not_odd_iff_even.2 hev)
      · exact h
    exact hnc (hSuz G P ⟨inferInstance, hna, hkp, hL, hcore, ⟨S, hcyc⟩, hZ2⟩ hZ hSz)
  · exact hnc (catalog_of_childHeWHered hChHe hU hna hkp hL hHe)

theorem sol78Thm412Noncat_of_inputs_of_uhered (hRK : Outer.RankTwoStdRec)
    (thm24_1 : Sol78Thm24_1Use)
    (hExc : ∀ (X : Type) [Group X], 29120 ≤ Nat.card X → Nat.card X ≠ 4030387200 →
      ¬ Recognition.Exact.EvenStandardException X)
    (hCTE : CTEvenResidualStatement) (hSmall : CTEvenSmallLieStatement) (hord : Thm46Orders)
    {G : Type} [Group G] [Finite G] (hU : Balance.UHered G) (hs : IsSimpleGroup G)
    (hna : ∃ a b : G, a * b ≠ b * a) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hnc : ¬ CFSG.Blueprint.Catalog G) (P : Subgroup G) (hP : SolStd P)
    (hPq : CFSG.IsQuasisimple ↥P) (hG2 : ∃ n : ℕ, 2 ≤ n ∧ LieModel (↥P ⧸ center ↥P) .G2 0 2 n) :
    False := by
  obtain ⟨n, hn, hG2⟩ := hG2
  haveI := hs
  have hL := standardComponentIsStandard_of_solStd hP hPq
  have hcore := oddCore_bot_of_noncat_of_uhered hU hna hkp hnc
  haveI : IsSimpleGroup (↥P ⧸ center ↥P) := hPq.2.1
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(centralizer (P : Set G))) := inferInstance
  have hgt := hord.g2_gt _ n hn hG2
  have hcyc := isCyclic_sylow_of_noncat hRK thm24_1 hna hkp hnc hP hPq
    (not_card_dvd_95040_of_gt hgt) S
  have hsp := sporadicRep_of_even_cyclic hCTE hSmall hna hkp hnc hL hcore S hcyc
    (Or.inl ⟨.G2, 0, n, hG2.admissible, hG2⟩) (hExc _ (by omega) (hord.g2_ne_he _ n hn hG2))
  exact hord.g2_not_sporadic _ n hn hG2 hsp

theorem sol78Thm46FSHered_of_inputs (hRK : Outer.RankTwoStdRec) (thm24_1 : Sol78Thm24_1Use)
    (hExc : ∀ (X : Type) [Group X], 29120 ≤ Nat.card X → Nat.card X ≠ 4030387200 →
      ¬ Recognition.Exact.EvenStandardException X)
    (hChL34 : ChildL34WHered) (hChHe : ChildHeWHered)
    (hCTE : CTEvenResidualStatement) (hSmall : CTEvenSmallLieStatement) (hord : Thm46Orders)
    (hSuzRow : SuzCentralTwo) (hSuzEven : Sol78Thm46SuzEven) (hSuz : SuzONanNotProperFixedCatalog)
    (hHe : HeldNotProperFixedInput) (hL3 : L3FixedCatalogGe3) (hL34 : L34FixedCatalog)
    (hCen : Sol78Thm46SporL34Centre) : Sol78Thm46FSHered := by
  intro Y _ _ hU N' hN hidx hkp P hP hPq hty hsuz
  by_cases hcat : CFSG.Blueprint.Catalog ↥N'
  · exact sol78Thm46CatFS_of_inputs hSuz hHe hL3 hL34 hCen Y N' hN hidx hkp hcat P hP hPq hty
      hsuz
  · have hNtop := catalog_or_top hN hidx hkp hcat
    subst hNtop
    haveI : IsSimpleGroup Y := by
      have := hN.isSimpleGroup
      exact (Subgroup.topEquiv (G := Y)).symm.isSimpleGroup
    have hna : ∃ a b : Y, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hN.nonabelian
      exact ⟨a, b, fun h => hab (Subtype.ext h)⟩
    exact (sol78Thm46Noncat_of_inputs_of_uhered hRK thm24_1 hExc hChL34 hChHe hCTE hSmall hord
      hSuzRow hSuzEven hU inferInstance hna hkp
      (fun h => hcat (CFSG.SectionRank.catalog_of_mulEquiv Subgroup.topEquiv h))
      P hP hPq hty hsuz).elim

theorem sol78Thm412FSHered_of_inputs (hRK : Outer.RankTwoStdRec) (thm24_1 : Sol78Thm24_1Use)
    (hExc : ∀ (X : Type) [Group X], 29120 ≤ Nat.card X → Nat.card X ≠ 4030387200 →
      ¬ Recognition.Exact.EvenStandardException X)
    (hCTE : CTEvenResidualStatement) (hSmall : CTEvenSmallLieStatement) (hord : Thm46Orders)
    (hG2 : G2FixedCatalog) (hCo1 : Co1G24Centre) : Sol78Thm412FSHered := by
  intro Y _ _ hU N' hN hidx hkp P hP hPq hty
  by_cases hcat : CFSG.Blueprint.Catalog ↥N'
  · exact sol78Thm412CatFS_of_inputs hG2 hCo1 Y N' hN hidx hkp hcat P hP hPq hty
  · have hNtop := catalog_or_top hN hidx hkp hcat
    subst hNtop
    haveI : IsSimpleGroup Y := by
      have := hN.isSimpleGroup
      exact (Subgroup.topEquiv (G := Y)).symm.isSimpleGroup
    have hna : ∃ a b : Y, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hN.nonabelian
      exact ⟨a, b, fun h => hab (Subtype.ext h)⟩
    exact (sol78Thm412Noncat_of_inputs_of_uhered hRK thm24_1 hExc hCTE hSmall hord hU
      inferInstance hna hkp
      (fun h => hcat (CFSG.SectionRank.catalog_of_mulEquiv Subgroup.topEquiv h))
      P hP hPq hty).elim

end CFSG.EvenSporadicStandard.Induction
