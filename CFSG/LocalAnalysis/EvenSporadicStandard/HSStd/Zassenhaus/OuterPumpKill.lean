module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpExcludeE
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.CentralCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.HSStd

@[expose] def RankTwoStdRec : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → ∀ L : Subgroup G,
      CFSG.Open.standardComponentIsStandard L →
      2 ≤ CFSG.Open.pRank 2 (centralizer (L : Set G)) →
        (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
          (IsSporadic G .J2 ∨ IsSporadic G .Suz ∨ IsSporadic G .He ∨ IsSporadic G .Ru ∨
            IsSporadic G .Co1)

section Setting

variable {G : Type} [Group G] [Finite G]

theorem pRank_sylow_le_one_of_le_one {M : Subgroup G}
    (hr : CFSG.Open.pRank 2 (centralizer (M : Set G)) ≤ 1)
    (S : Sylow 2 (centralizer (M : Set G))) :
    CFSG.pRank 2 ↥(S : Subgroup ↥(centralizer (M : Set G))) ≤ 1 := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  have hinj : Function.Injective
      ((centralizer (M : Set G)).subtype.comp
        (S : Subgroup ↥(centralizer (M : Set G))).subtype) :=
    (Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _)
  have h1 := CFSG.SectionRank.pRank_le_map (p := 2) one_lt_two _ hinj
    (⊤ : Subgroup ↥(S : Subgroup ↥(centralizer (M : Set G))))
  have h2 : (⊤ : Subgroup ↥(S : Subgroup ↥(centralizer (M : Set G)))).map
      ((centralizer (M : Set G)).subtype.comp
        (S : Subgroup ↥(centralizer (M : Set G))).subtype) ≤ centralizer (M : Set G) := by
    rintro _ ⟨x, -, rfl⟩
    exact (x : ↥(centralizer (M : Set G))).2
  have h3 := CFSG.SectionRank.pRank_mono (p := 2) one_lt_two h2
  exact h1.trans (h3.trans hr)

theorem false_of_standard_pumpType_rank_two
    (hrec : RankTwoStdRec) (hCo1 : Co1InvCentralizers)
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (hHS : 44352000 ∣ Nat.card G)
    (ht : ∃ t : G, orderOf t = 2 ∧ Nat.card (centralizer ({t} : Set G)) = 177408000)
    {M : Subgroup G} (hM : CFSG.Open.standardComponentIsStandard M)
    (hr : 2 ≤ CFSG.Open.pRank 2 (centralizer (M : Set G))) : False :=
  false_of_lemmaE hCo1 hHS ht (hrec G hnonab hK M hM hr)

end Setting

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
