module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Hyp12LieSimple
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.ReduceHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Hyp12LieCat
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Hyp12LieTwoE6

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp12Lie

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

@[expose] def Sol78Hyp12LieUseAt (Y : Type) [Group Y] [Finite Y] : Prop :=
  ∀ (N' : Subgroup Y), FStarSimple N' → N'.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y → ¬ CFSG.Blueprint.Catalog ↥N' →
      ∀ L' : Subgroup Y, SolStd L' → CFSG.IsQuasisimple ↥L' → Even (Nat.card ↥(center ↥L')) →
        (LieModel (↥L' ⧸ center ↥L') .PSU 6 2 1 → IsSporadic ↥N' .Fi22) ∧
          (LieModel (↥L' ⧸ center ↥L') .twistedE6 0 2 1 → IsSporadic ↥N' .B)

@[expose] def Sol78Hyp12LieUseHered : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Balance.UHered Y → Sol78Hyp12LieUseAt Y

theorem hyp12Lie_simple_of_uhered {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : Balance.UHered G) (thm24_1 : Sol78Thm24_1Use) (hr1 : Hyp12RankOne)
    (hO : LieOrderFormulasInput)
    (hrow : CFSG.LieType.Steinberg.CentralExt.GriessTwistedE6Two.TwistedE6TwoMultiplier)
    (c6 : EvenSmallLie.ChildU6Cover) (c2 : EvenSmallLie.Child2E6)
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hncat : ¬ CFSG.Blueprint.Catalog ↥(⊤ : Subgroup G))
    {L : Subgroup G} (hL : SolStd L) (hq : CFSG.IsQuasisimple ↥L)
    (hev : Even (Nat.card ↥(center ↥L))) :
    (LieModel (↥L ⧸ center ↥L) .PSU 6 2 1 → IsSporadic G .Fi22) ∧
      (LieModel (↥L ⧸ center ↥L) .twistedE6 0 2 1 → IsSporadic G .B) := by
  have hfs := fStarSimple_top G hnonab
  have hbal : ∀ z : G, orderOf z = 2 →
      CFSG.Open.standardComponentOddCore (centralizer ({z} : Set G)) = ⊥ := by
    intro z hz
    by_contra hne
    exact hncat
      (Balance.catalog_of_unbalanced_of_uhered hG hfs (by simp [Subgroup.index_top]) hkp hz hne)
  obtain ⟨t, ht2, hcomp⟩ := hL.exists_involution
  have hZ2 : IsPGroup 2 ↥(center ↥L) := isPGroup_center_of_balance hL ht2 hcomp (hbal t ht2)
  have hZne : center ↥L ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hev
    exact Nat.not_even_one hev
  have hstd : CFSG.Open.standardComponentIsStandard L := standardComponentIsStandard_of_solStd hL hq
  have hle : Nat.card (↥L ⧸ center ↥L) ≤ Nat.card G :=
    (Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective).trans
      (Subgroup.card_le_card_group L)
  have hcyc_of : (LieModel (↥L ⧸ center ↥L) .PSU 6 2 1 ∨
      LieModel (↥L ⧸ center ↥L) .twistedE6 0 2 1) → 95040 < Nat.card (↥L ⧸ center ↥L) →
        ∀ S : Sylow 2 ↥(centralizer (L : Set G)),
          IsCyclic ↥(S : Subgroup ↥(centralizer (L : Set G))) :=
    fun hM hbig S =>
      isCyclic_sylow_of_lie thm24_1 hnonab hncat (by omega) hL
        (hr1 G hnonab hkp hncat L hL hq hM) S
  have hset : (∀ S : Sylow 2 ↥(centralizer (L : Set G)),
      IsCyclic ↥(S : Subgroup ↥(centralizer (L : Set G)))) → EvenSmallLie.StandardSetting G L :=
    fun hcyc => by
      obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(centralizer (L : Set G))) := inferInstance
      exact ⟨inferInstance, hnonab, hkp, hstd, hbal, ⟨S, hcyc S⟩⟩
  refine ⟨fun hU62 => ?_, fun hE62 => ?_⟩
  · have hc : Nat.card (↥L ⧸ center ↥L) = 9196830720 := card_psu_six_two hO hU62
    exact c6 G L (hset (hcyc_of (Or.inl hU62) (by omega))) hZne hZ2 hU62
  · have hc : Nat.card (↥L ⧸ center ↥L) = 76532479683774853939200 :=
      card_twistedE6_two hO hE62
    have hcyc := hcyc_of (Or.inr hE62) (by omega)
    haveI : Group.IsPerfect ↥L := hq.1
    have hle : Nat.card ↥(center ↥L) ≤ 2 :=
      card_center_le_two_of_twistedE6 hrow hE62 hZ2 (isCyclic_center_of_sylow hcyc hZ2)
    have h2 : Nat.card ↥(center ↥L) = 2 := by
      obtain ⟨k, hk⟩ := hev
      have : 0 < Nat.card ↥(center ↥L) := Nat.card_pos
      omega
    exact c2 G L (hset hcyc) h2 hE62

theorem sol78Hyp12LieUseAt_of_uhered {Y : Type} [Group Y] [Finite Y] (hY : Balance.UHered Y)
    (thm24_1 : Sol78Thm24_1Use) (hr1 : Hyp12RankOne) (hO : LieOrderFormulasInput)
    (hrow : CFSG.LieType.Steinberg.CentralExt.GriessTwistedE6Two.TwistedE6TwoMultiplier)
    (c6 : EvenSmallLie.ChildU6Cover) (c2 : EvenSmallLie.Child2E6) : Sol78Hyp12LieUseAt Y := by
  intro N' hN hidx hkp hcat L' hsol hq hev
  have hN2 : N'.index ≠ 2 := fun h => hcat (Balance.catalog_of_index_two hN h hkp)
  have hNtop : N' = ⊤ := Balance.eq_top_of_index_ne_two hidx hN2
  subst hNtop
  have := hN.isSimpleGroup
  haveI : IsSimpleGroup Y := (Subgroup.topEquiv.symm : Y ≃* ↥(⊤ : Subgroup Y)).isSimpleGroup
  obtain ⟨a, b, hab⟩ := hN.nonabelian
  have hnonab : ∃ a b : Y, a * b ≠ b * a := ⟨a.1, b.1, fun h => hab (Subtype.ext h)⟩
  have key :=
    hyp12Lie_simple_of_uhered hY thm24_1 hr1 hO hrow c6 c2 hnonab hkp hcat hsol hq hev
  exact ⟨fun h => by
      obtain ⟨e⟩ := key.1 h
      exact ⟨Subgroup.topEquiv.trans e⟩,
    fun h => by
      obtain ⟨e⟩ := key.2 h
      exact ⟨Subgroup.topEquiv.trans e⟩⟩

theorem sol78Hyp12LieHered_of_use (hCat : Sol78Hyp12LieCat) (hUse : Sol78Hyp12LieUseHered) :
    Sol78Hyp12LieHered := by
  intro Y _ _ hY N' hN hidx hkp L' hsol hq hev
  by_cases hcat : CFSG.Blueprint.Catalog ↥N'
  · exact hCat Y N' hN hidx hcat L' hsol hq hev
  · exact hUse Y hY N' hN hidx hkp hcat L' hsol hq hev

end CFSG.EvenSporadicStandard.Induction.Hyp12Lie
