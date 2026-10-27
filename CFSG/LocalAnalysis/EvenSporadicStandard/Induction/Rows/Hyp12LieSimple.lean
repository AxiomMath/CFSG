module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.EvenCoverStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpKill
import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Prelim

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp12Lie

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer (RankTwoStdRec)

@[expose] def Hyp12RankOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → ¬ CFSG.Blueprint.Catalog ↥(⊤ : Subgroup G) →
      ∀ L : Subgroup G, SolStd L → CFSG.IsQuasisimple ↥L →
        (LieModel (↥L ⧸ center ↥L) .PSU 6 2 1 ∨ LieModel (↥L ⧸ center ↥L) .twistedE6 0 2 1) →
          CFSG.pRank 2 ↥(centralizer (L : Set G)) ≤ 1

theorem hyp12RankOne_of_rankTwo (hrec : RankTwoStdRec) : Hyp12RankOne := by
  intro G _ _ _ hnonab hkp hncat L hL hq _
  by_contra hr
  have hr2 : 2 ≤ CFSG.Open.pRank 2 (centralizer (L : Set G)) := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
    omega
  have hG : CFSG.Blueprint.Catalog G := by
    rcases hrec G hnonab hkp L (standardComponentIsStandard_of_solStd hL hq) hr2 with
      ⟨n, hn, he⟩ | h | h | h | h | h
    · exact Or.inr (Or.inl ⟨n, by omega, he⟩)
    all_goals exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, h⟩)))
  exact hncat (CFSG.SectionRank.catalog_of_mulEquiv Subgroup.topEquiv hG)

theorem isCyclic_sylow_of_lie (thm24_1 : Sol78Thm24_1Use) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hncat : ¬ CFSG.Blueprint.Catalog ↥(⊤ : Subgroup G)) (hlarge : 95040 < Nat.card G)
    {L : Subgroup G} (hL : SolStd L)
    (hr : CFSG.pRank 2 ↥(centralizer (L : Set G)) ≤ 1) (S : Sylow 2 ↥(centralizer (L : Set G))) :
    IsCyclic ↥(S : Subgroup ↥(centralizer (L : Set G))) := by
  have hrS : CFSG.pRank 2 ↥(S : Subgroup ↥(centralizer (L : Set G))) ≤ 1 :=
    (Hyp.pRank_two_le_of_injective (S : Subgroup ↥(centralizer (L : Set G))).subtype
      (S : Subgroup ↥(centralizer (L : Set G))).subtype_injective).trans hr
  rcases Hyp.isCyclic_or_genQuaternion_of_pRank_le_one S.isPGroup' hrS with hc | hq
  · exact hc
  · exfalso
    have hnd : ¬ Nat.card ↥(⊤ : Subgroup G) ∣ 95040 := fun h => by
      rw [Subgroup.card_top] at h
      have := Nat.le_of_dvd (by norm_num) h
      omega
    obtain ⟨t, n, p, f, -, -, -, hm⟩ :=
      thm24_1 G ⊤ (fStarSimple_top G hnonab) hnd L hL ⟨S, hq⟩
    exact hncat (lieModel_catalog _ t n p f hm)

theorem isCyclic_center_of_sylow {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hcyc : ∀ S : Sylow 2 ↥(centralizer (L : Set G)),
      IsCyclic ↥(S : Subgroup ↥(centralizer (L : Set G))))
    (h2 : IsPGroup 2 ↥(center ↥L)) : IsCyclic ↥(center ↥L) := by
  have hzC : ∀ z : ↥(center ↥L), ((z : ↥L) : G) ∈ centralizer (L : Set G) := fun z =>
    mem_centralizer_iff.2 fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨y, hy⟩)
  let ι : ↥(center ↥L) →* ↥(centralizer (L : Set G)) :=
    { toFun := fun z => ⟨((z : ↥L) : G), hzC z⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun a b h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have hP : IsPGroup 2 ↥ι.range := h2.of_surjective ι.rangeRestrict ι.rangeRestrict_surjective
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  have e1 : ↥(ι.range.subgroupOf (S : Subgroup ↥(centralizer (L : Set G)))) ≃* ↥ι.range :=
    Subgroup.subgroupOfEquivOfLe hS
  haveI := hcyc S
  haveI : IsCyclic ↥ι.range := isCyclic_of_surjective e1.toMonoidHom e1.surjective
  exact isCyclic_of_surjective (MonoidHom.ofInjective hι).symm.toMonoidHom
    (MonoidHom.ofInjective hι).symm.surjective

end CFSG.EvenSporadicStandard.Induction.Hyp12Lie
