module

public import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal
public import CFSG.LocalAnalysis.RankThreeTheoremC.PSLTwoRank
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseExtremal
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem not_le_of_normal_of_two_le_pRank (hS : Setting G) (hU0 : FullCoreLocal G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {C S N : Subgroup G} (hSC : CFSG.ABGLocalTools.IsSylowOf p S C) (hSP : S ≤ P)
    (hCM : ¬ C ≤ M) (hNC : N ≤ C) (hCN : C ≤ normalizer (N : Set G))
    (h2 : 2 ≤ CFSG.Open.pRank p (S ⊓ N)) : ¬ N ≤ M := by
  intro hNM
  have hfact : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hNSsyl := hSC.inf_of_le_normalizer hNC hCN
  have hNS : normalizer ((S ⊓ N : Subgroup G) : Set G) ≤ M :=
    normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM hNSsyl.isPGroup
      (inf_le_left.trans (hSP.trans hPM)) h2
  exact hCM ((le_sup_normalizer_of_isSylowOf hCN hNSsyl).trans (sup_le hNM hNS))

theorem not_rankThreeLayer_le_of_mulEquiv_psl (hS : Setting G) (hU0 : FullCoreLocal G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {x : G} (hxM : ¬ centralizer ({x} : Set G) ≤ M)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf p ((P : Subgroup G) ⊓ centralizer ({x} : Set G))
      (centralizer ({x} : Set G)))
    [Fact p.Prime] {m : ℕ} (hm : 2 ≤ m)
    (e : rankThreeLayer (centralizer ({x} : Set G)) ≃* PSL(2, GaloisField p m)) :
    ¬ rankThreeLayer (centralizer ({x} : Set G)) ≤ M := by
  have hprime : p.Prime := Fact.out
  set L := rankThreeLayer (centralizer ({x} : Set G)) with hL
  have hLC : L ≤ centralizer ({x} : Set G) := rankThreeLayer_le _
  have hCL : centralizer ({x} : Set G) ≤ normalizer (L : Set G) :=
    le_normalizer_rankThreeLayer _
  have hLrank : 2 ≤ CFSG.Open.pRank p L := by
    rw [pRank_subgroup_eq_internal_top p hprime.one_lt L,
      pRank_top_eq_of_equiv p hprime.one_lt e]
    exact hm.trans (le_pRank_psl_two p m (by omega))
  have hLsyl := hsyl.inf_of_le_normalizer hLC hCL
  exact not_le_of_normal_of_two_le_pRank hS hU0 hp hM hsyl inf_le_left hxM hLC hCL
    (hLrank.trans (pRank_le_of_isSylowOf hLsyl))

end CFSG.LocalAnalysis.RankThreeTheoremC
