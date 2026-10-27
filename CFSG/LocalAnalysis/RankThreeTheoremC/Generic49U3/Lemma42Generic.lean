module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Struct
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericListPrune3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.RankThree.PartOne.Census3 (IsoLie)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G}

@[expose] def GenericComponentClass (G : Type) [Group G] [Finite G] : Prop :=
  GenericAt G fun p _ M a => 5 ≤ p → ∃ J : Subgroup G,
    J ≤ Subgroup.centralizer ({a} : Set G) ∧
    Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (J : Set G) ∧ Group.IsPerfect J ∧
    rankThreePrimeCore p J < J ∧
    (∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
      N = rankThreePrimeCore p J ∨ N = J) ∧ ¬ J ≤ M ∧
    ∃ (Q : Type) (_ : Group Q) (ψ : ↥J →* Q), Function.Surjective ψ ∧
      ψ.ker = (rankThreePrimeCore p J).subgroupOf J ∧
      (IsRankTwoSEGroupE3 p Q ∨ (p = 5 ∧ IsoLie Q (.suzuki 2))) ∧
      ¬ Nonempty (Q ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group)

theorem u3_P_le_centralizer_of_mem_U0 (hc : U3Config G p P M x J)
    (hPx : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) {a : G}
    (ha : a ∈ u3U0 P x J) : (P : Subgroup G) ≤ Subgroup.centralizer ({a} : Set G) := by
  obtain ⟨-, -, -, -, hcent, -, -⟩ := u3U0_facts hc
  intro g hg
  have hgS : g ∈ u3S P x := ⟨hg, hPx hg⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hcent g hgS a ha)

theorem u3_bad_isGenericPoint (hS : Setting G) (hc : U3Config G p P M x J)
    (hPx : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) {a : G}
    (ha : a ∈ u3U0 P x J) (hax : a ∉ Subgroup.zpowers x)
    (hbad : ¬ Subgroup.centralizer ({a} : Set G) ≤ M) : IsGenericPoint p P M a := by
  have hprime := hc.prime
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core
  have hPa := u3_P_le_centralizer_of_mem_U0 hc hPx ha
  obtain ⟨hell, -, hle, -, -, -, -⟩ := u3U0_facts hc
  have haS : a ∈ u3S P x := hle ha
  have haP : a ∈ (P : Subgroup G) := haS.1
  have ha1 : a ≠ 1 := fun h => hax (h ▸ Subgroup.one_mem _)
  have hap : a ^ p = 1 := hell.2 a ha
  have hinf : (P : Subgroup G) ⊓ Subgroup.centralizer ({a} : Set G) = (P : Subgroup G) :=
    inf_eq_left.mpr hPa
  refine ⟨haP, ⟨hPM haP, ha1, hap, hP3.ge.trans (pRank_mono p hprime.one_lt hPa), hbad⟩, ?_, ?_⟩
  · rw [hinf]
    exact ⟨P.subtype hPa, by rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPa]⟩
  · rw [hinf]
    exact hP3

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
