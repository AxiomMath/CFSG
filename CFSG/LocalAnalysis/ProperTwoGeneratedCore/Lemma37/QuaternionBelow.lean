module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuaternionReduction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Final
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Cyclic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CoverExcl
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverUnitary
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEight
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneSwapFusion

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

@[expose] def QuasisimpleQuaternionCoreClassificationBelow : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CanonicalBelow (Nat.card J) → QuasisimpleQuaternionCore J

@[expose] def SquareCaseQuaternionImpossibleBelow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G) (z : G),
    CanonicalBelow (Nat.card G) → SquareCaseSetting G S H z →
    ∀ J : Subgroup (EscapingQuotient z), CFSG.IsComponent J → ¬ J ≤ escapingImage H z →
      (∃ x ∈ J, orderOf x = 2 ∧ x ≠ escapingBar z) →
      ((∀ k ∈ escapingSylowImage S z, k ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) →
        k = 1 ∨ k = escapingBar z) ∨
       (∃ c ∈ Subgroup.center J, (c : EscapingQuotient z) ≠ 1 ∧
        (c : EscapingQuotient z) ≠ escapingBar z)) →
      ¬ TwoPointCyclic H z J → False

theorem CanonicalBelow.mono {m n : ℕ} (h : CanonicalBelow n) (hmn : m ≤ n) : CanonicalBelow m :=
  fun K _ _ hK => h K (lt_of_lt_of_le hK hmn)

theorem card_component_lt {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G}
    {z : G} (hsq : SquareCaseSetting G S H z) (J : Subgroup (EscapingQuotient z)) :
    Nat.card J < Nat.card G := by
  have htop : Subgroup.centralizer ({z} : Set G) ≠ ⊤ := by
    intro htop
    have : IsSimpleGroup G := hsq.core.simple
    have hzc : z ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g =>
      Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
    rcases (Subgroup.center G).normal_of_characteristic.eq_bot_or_eq_top with h | h
    · rw [h, Subgroup.mem_bot] at hzc
      have h2 := hsq.central.2.1
      rw [hzc, orderOf_one] at h2
      exact absurd h2 (by decide)
    · obtain ⟨a, b, hab⟩ := hsq.core.nonabelian
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  calc Nat.card J ≤ Nat.card (EscapingQuotient z) := Subgroup.card_le_card_group J
    _ ≤ Nat.card (Subgroup.centralizer ({z} : Set G)) :=
        Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    _ < Nat.card G :=
        (Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr htop)).trans_eq Subgroup.card_top

theorem squareCaseQuaternionImpossibleBelow_of
    (hL : QuasisimpleQuaternionCoreClassificationBelow)
    (hG : TwoANine.NoTwoANineQuaternionComponent) : SquareCaseQuaternionImpossibleBelow :=
  fun _ _ _ _ _ _ IH hsq J hJ hJH hrank hK hnc => false_of_quaternionCore hsq hJ hJH hrank hK hnc
    (hL J (IH.mono (card_component_lt hsq J).le)) hG

theorem squareCaseQuasisimpleImpossibleBelow_of_splitBelow (hc : SquareCaseCyclicImpossibleBelow)
    (hq : SquareCaseQuaternionImpossibleBelow) : SquareCaseQuasisimpleImpossibleBelow := by
  intro G _ _ S H z IH hS J hJ hJH hrank hK
  by_cases hcyc : TwoPointCyclic H z J
  · exact hc G S H z IH hS J hJ hJH hrank hK hcyc
  · exact hq G S H z IH hS J hJ hJH hrank hK hcyc

theorem aschbacher_proper_two_generated_core_of_quaternionBelow
    (hq : SquareCaseQuaternionImpossibleBelow)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) (hrank : 3 ≤ CFSG.Open.pRank 2 (S : Subgroup G))
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≠ ⊤) :
    properTwoGenCoreGamma (S : Subgroup G) 1 ≠ ⊤ ∨ Nonempty (G ≃* properTwoGenCoreJ1) :=
  aschbacher_proper_two_generated_core_of_square_parts squareCaseRankOneImpossible
    (squareCaseHighRankCentralizerImpossible_of_covers benderCoverStatement)
    (squareCaseQuasisimpleImpossibleBelow_of_splitBelow
      (squareCaseCyclicImpossibleBelow_of
        (squareCaseCoverExcluded_of rankTwoCoverStatement squareCaseSzEightExcluded)
        rankTwoCoverStatement) hq) G hnonab S hrank hcore

theorem aschbacher_proper_two_generated_core_of_quasisimpleCore
    (hL : QuasisimpleQuaternionCoreClassificationBelow) (hG : TwoANine.NoTwoANineQuaternionComponent)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) (hrank : 3 ≤ CFSG.Open.pRank 2 (S : Subgroup G))
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≠ ⊤) :
    properTwoGenCoreGamma (S : Subgroup G) 1 ≠ ⊤ ∨ Nonempty (G ≃* properTwoGenCoreJ1) :=
  aschbacher_proper_two_generated_core_of_quaternionBelow
    (squareCaseQuaternionImpossibleBelow_of hL hG) G hnonab S hrank hcore

end CFSG.ProperTwoGeneratedCore.Lemma37
