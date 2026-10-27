module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Sol78Thm22Guarded
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Thm24OneUse
public import CFSG.CharacterTheory.TwoRankLowerBound.RankOneClassification

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup Relation CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H] {N : Subgroup H}

theorem pRank_two_le_of_injective {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (hf : Function.Injective f) : CFSG.pRank 2 X ≤ CFSG.pRank 2 Y := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.pRank_top_le_of_injective one_lt_two f hf

theorem isCyclic_or_genQuaternion_of_pRank_le_one {P : Type} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (hr : CFSG.pRank 2 P ≤ 1) : IsCyclic P ∨ IsGenQuaternion P := by
  have h : CFSG.Open.twoRank P ≤ 1 := by
    have := CFSG.SectionRank.pRank_eq_open_pRank_top 2 P
    unfold CFSG.Open.twoRank
    omega
  exact CFSG.TwoRankLowerBound.Helpers.rank_one_two_group_cyclic_or_quaternion P hP h

theorem stdBare_of_maximal (thm22 : Sol78Thm22At H)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hN : FStarSimple N)
    (hidx : N.index ≤ 2) {M : Subgroup H}
    (hmax : Maximal M) (hrank : 3 ≤ CFSG.pRank 2 ↥M) : StdBare M :=
  thm22 hkp N hN hidx M hmax hrank

@[expose] def OddLieExcl (s' : TauCeti.SporadicName) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (N' : Subgroup Y), FStarSimple N' →
    CFSG.Blueprint.OddLieType ↥N' → ∀ A : Subgroup Y, SolStd A → OddCover s' A → False

theorem cyclic_sylow_of_std (thm24_1 : Sol78Thm24_1Use) (hN : FStarSimple N)
    (hord : ¬ Nat.card ↥N ∣ 95040) {A : Subgroup H} (hA : SolStd A) {s' : TauCeti.SporadicName}
    (hcov : OddCover s' A) (hrk : CFSG.pRank 2 ↥(centralizer (A : Set H)) ≤ 1)
    (hlie : OddLieExcl s') : ∃ P : Sylow 2 (centralizer (A : Set H)), IsCyclic ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥(centralizer (A : Set H))) := inferInstance
  refine ⟨P, ?_⟩
  have hrP : CFSG.pRank 2 ↥(P : Subgroup ↥(centralizer (A : Set H))) ≤ 1 :=
    (pRank_two_le_of_injective (P : Subgroup ↥(centralizer (A : Set H))).subtype
      (Subgroup.subtype_injective _)).trans hrk
  rcases isCyclic_or_genQuaternion_of_pRank_le_one P.isPGroup' hrP with hc | hq
  · exact hc
  · exact (hlie H N hN (thm24_1 H N hN hord A hA ⟨P, hq⟩) A hA hcov).elim

end CFSG.EvenSporadicStandard.Induction.Hyp
