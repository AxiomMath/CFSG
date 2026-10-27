module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralizerSylow
public import CFSG.StronglyEmbedded
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.CyclicCase

open CFSG.Open

variable {X : Type*} [Group X] [Finite X]

theorem one_le_pRank_closure_of_orderOf_eq_two {t : X} (ht : orderOf t = 2) :
    1 ≤ CFSG.Open.pRank 2 (Subgroup.closure ({t} : Set X)) := by
  have ht2 : t ^ 2 = 1 := (orderOf_eq_prime_iff.mp ht).1
  rw [← Subgroup.zpowers_eq_closure]
  refine CFSG.SectionRank.le_pRank (by decide) le_rfl ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩,
    fun y hy => ?_⟩ (by rw [Nat.card_zpowers, ht, pow_one])
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
    exact (Commute.zpow_zpow_self t i j).eq
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]

theorem centralizer_le_gamma_one (S : Sylow 2 X) (hrank : 1 ≤ CFSG.Open.pRank 2 (S : Subgroup X))
    {t : X} (htΓ : t ∈ properTwoGenCoreGamma (S : Subgroup X) 1) (ht : orderOf t = 2) :
    Subgroup.centralizer ({t} : Set X) ≤ properTwoGenCoreGamma (S : Subgroup X) 1 := by
  have hp : IsPGroup 2 (Subgroup.closure ({t} : Set X)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [← Subgroup.zpowers_eq_closure]
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  refine ((Subgroup.centralizer_le_normalizer _).trans
    (Subgroup.normalizer_le_normalizer_closure _)).trans ?_
  exact normalizer_le_overgroup S _ 1 (sylow_le_gamma S hrank) le_rfl _ hp
    ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr htΓ))
    (one_le_pRank_closure_of_orderOf_eq_two ht)

theorem isBenderGroup_of_gamma_one_ne_top
    [IsSimpleGroup X] (S : Sylow 2 X)
    (hrank : 2 ≤ CFSG.Open.twoRank X) (hΓ : properTwoGenCoreGamma (S : Subgroup X) 1 ≠ ⊤) :
    CFSG.BenderSuzuki.IsBenderGroup X := by
  have hS : 1 ≤ CFSG.Open.pRank 2 (S : Subgroup X) := by
    rw [sylow_two_rank_eq S]
    omega
  exact CFSG.BenderSuzuki.bender_suzuki _
    (strongly_embedded_order_of_full_core_centralizer_closure S _ hΓ (sylow_le_gamma S hS)
      hrank (gamma_antitone _ (by decide)) fun _ htΓ ht => centralizer_le_gamma_one S hS htΓ ht)

end CFSG.ProperTwoGeneratedCore.Lemma37.CyclicCase
