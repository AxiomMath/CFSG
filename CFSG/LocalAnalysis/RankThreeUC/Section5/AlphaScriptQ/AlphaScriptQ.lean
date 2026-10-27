module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context
public import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient
import all CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

namespace AlphaScriptQ

variable {G : Type} [Group G] [Finite G]

theorem mem_scriptQ {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h51 : OddPrimeClassTwoAction G p P T B e) (h53 : FaithfulBinaryIrreducibleAction G p P T B ρ)
    (hderived : P ≤ commutator G) : P ∈ scriptQ G p := by
  have hs := h51.setting
  refine ⟨h53.normal, hs.pGroup, ?_, hs.exponent, hs.class_le_two, hderived⟩
  intro hcyc
  have h1 : CFSG.Open.pRank p P ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.pRank_le_one_of_sylow_cyclic hs.prime fun S =>
      Subgroup.isCyclic _
  have := h53.rank_gt
  omega

theorem mem_alpha {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h51 : OddPrimeClassTwoAction G p P T B e) (h53 : FaithfulBinaryIrreducibleAction G p P T B ρ)
    (hderived : P ≤ commutator G) : p ∈ alphaSet G := by
  have le_pCoreOf_commutator {p : ℕ} {P : Subgroup G} (hN : P.Normal) (hp : IsPGroup p P)
      (hle : P ≤ commutator G) : P ≤ CFSG.Open.pCoreOf p (commutator G) := by
    have hn : (P.subgroupOf (commutator G)).Normal := hN.subgroupOf _
    have hpg : IsPGroup p (P.subgroupOf (commutator G)) :=
      hp.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
    have h1 : P.subgroupOf (commutator G) ≤ CFSG.Open.pCore p (commutator G) :=
      le_sSup ⟨hn, hpg⟩
    intro x hx
    exact ⟨⟨x, hle hx⟩, h1 hx, rfl⟩
  have hs := h51.setting
  refine show p.Prime ∧ _ from ⟨hs.prime, lt_of_lt_of_le h53.rank_gt ?_⟩
  exact CFSG.SectionRank.pRank_mono hs.prime.one_lt
    (le_pCoreOf_commutator h53.normal hs.pGroup hderived)

end AlphaScriptQ

end Section5

end CFSG.LocalAnalysis.RankThreeUC
