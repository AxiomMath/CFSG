module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuThm54ReachHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.ReduceHered
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.EvenCoverStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.CTEvenResidual
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.ResidualOrders

public section

namespace CFSG.EvenSporadicStandard.Induction.Thm54Reach

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer (RankTwoStdRec)

theorem false_of_simple_not_catalog_of_uhered (I : CatInputs) (hRK : RankTwoStdRec)
    (hcit : Sol78Thm24_1Use) (hcte : CTEvenResidualStatement) (hexc : ExcInput)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hU : Balance.UHered G)
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hncat : ¬ CFSG.Blueprint.Catalog ↥(⊤ : Subgroup G)) {P : Subgroup G} (hP : SolStd P)
    (hq : CFSG.IsQuasisimple ↥P) (hT : Sol78Thm54Types (↥P ⧸ center ↥P)) : False := by
  have hO := I.arm.order
  have hfs := fStarSimple_top G hnonab
  have hbal : ∀ z : G, orderOf z = 2 →
      CFSG.Open.standardComponentOddCore (centralizer ({z} : Set G)) = ⊥ := by
    intro z hz
    by_contra hne
    exact hncat (Balance.catalog_of_unbalanced_of_uhered hU hfs (by simp [Subgroup.index_top])
      hkp hz hne)
  have hstd : CFSG.Open.standardComponentIsStandard P :=
    standardComponentIsStandard_of_solStd hP hq
  have hc : Thm54Order (Nat.card (↥P ⧸ center ↥P)) := thm54Order_of_types hO hT
  have hr1 : CFSG.pRank 2 ↥(centralizer (P : Set G)) ≤ 1 := by
    by_contra hr
    have hr2 : 2 ≤ CFSG.Open.pRank 2 (centralizer (P : Set G)) := by
      rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
      omega
    have hG : CFSG.Blueprint.Catalog G := by
      rcases hRK G hnonab hkp P hstd hr2 with ⟨n, hn, he⟩ | h | h | h | h | h
      · exact Or.inr (Or.inl ⟨n, by omega, he⟩)
      all_goals exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, h⟩)))
    exact hncat (CFSG.SectionRank.catalog_of_mulEquiv Subgroup.topEquiv hG)
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(centralizer (P : Set G))) := inferInstance
  have hcyc : IsCyclic ↥(S : Subgroup ↥(centralizer (P : Set G))) := by
    have hrS : CFSG.pRank 2 ↥(S : Subgroup ↥(centralizer (P : Set G))) ≤ 1 :=
      (Hyp.pRank_two_le_of_injective (S : Subgroup ↥(centralizer (P : Set G))).subtype
        (S : Subgroup ↥(centralizer (P : Set G))).subtype_injective).trans hr1
    rcases Hyp.isCyclic_or_genQuaternion_of_pRank_le_one S.isPGroup' hrS with hcy | hgq
    · exact hcy
    · exfalso
      have hnd : ¬ Nat.card ↥(⊤ : Subgroup G) ∣ 95040 := fun h =>
        hc.not_dvd_95040 ((Subgroup.card_quotient_dvd_card _).trans
          ((Subgroup.card_dvd_of_le (le_top : P ≤ ⊤)).trans h))
      obtain ⟨t, n, p, f, -, -, -, hm⟩ := hcit G ⊤ hfs hnd P hP ⟨S, hgq⟩
      exact hncat (lieModel_catalog _ t n p f hm)
  have hres := hcte G hnonab hkp P hstd hbal S hcyc
    (Or.inl (evenLieType_of_thm54Types hT)) (hexc hc)
  exact not_evenStandardResidual_of_thm54Order hO I.cardAll hc hres

theorem sol78Thm54ReachHered_of_inputs (I : CatInputs) (hRK : RankTwoStdRec)
    (hcit : Sol78Thm24_1Use) (hcte : CTEvenResidualStatement) (hexc : ExcInput) :
    Sol78Thm54ReachHered := by
  intro Y _ _ hU N' hN hidx hkp P hP hq hT h29
  have hpos : 0 < N'.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  rcases (show N'.index = 1 ∨ N'.index = 2 by omega) with h | h
  · have hNtop : N' = ⊤ := Subgroup.index_eq_one.1 h
    subst hNtop
    haveI : IsSimpleGroup ↥(⊤ : Subgroup Y) := hN.isSimpleGroup
    haveI : IsSimpleGroup Y :=
      (Subgroup.topEquiv.symm : Y ≃* ↥(⊤ : Subgroup Y)).isSimpleGroup
    obtain ⟨a, b, hab⟩ := hN.nonabelian
    have hnonab : ∃ a b : Y, a * b ≠ b * a := ⟨a.1, b.1, fun h => hab (Subtype.ext h)⟩
    by_cases hcat : CFSG.Blueprint.Catalog ↥(⊤ : Subgroup Y)
    · exact reach_of_catalog I hN (by omega) hcat hP hq hT h29
    · exact (false_of_simple_not_catalog_of_uhered I hRK hcit hcte hexc hU hnonab hkp hcat
        hP hq hT).elim
  · exact sol78Thm54ReachIndex_two I Y N' hN h hkp P hP hq hT h29

end CFSG.EvenSporadicStandard.Induction.Thm54Reach
