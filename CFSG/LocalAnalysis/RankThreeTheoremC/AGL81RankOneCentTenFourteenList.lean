module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentTenFourteenOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentTenFourteenNarrow
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeListOf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem tenFourteenOneGroup_of_nineThreeList (hKF : KFactTenFourteenNarrow) (hS : Setting G)
    {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G} (he : D1Escape p P M H₁ R₁) {a : G}
    (hao : orderOf a = p) {U : Subgroup G} (hUC : U ≤ Subgroup.centralizer ({a} : Set G))
    (hUQ : IsAGLQ p M U) (hK : d1KBar p M (Subgroup.centralizer ({a} : Set G)) ≠ ⊥)
    (hL : NineThreeListGroup p ↥(d1KBar p M (Subgroup.centralizer ({a} : Set G))))
    (hZ : Subgroup.center ↥(d1KBar p M (Subgroup.centralizer ({a} : Set G))) = ⊥) :
    TenFourteenOneGroup p ↥(d1KBar p M (Subgroup.centralizer ({a} : Set G))) := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set N := Subgroup.centralizer ({a} : Set G) with hN
  set O := primeComplementCore (G := N) p
  set π := QuotientGroup.mk' O with hπ
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  obtain ⟨R, -, hRM, hR, -⟩ := exists_isSylowIn_of_isAGLQ he hUQ hUC
  set Rb : Sylow p (N ⧸ O) := hR.toSylow.mapSurjective (QuotientGroup.mk'_surjective O) with hRb
  have hRbeq : (Rb : Subgroup (N ⧸ O)) = (R.subgroupOf N).map π := by
    rw [hRb, Sylow.coe_mapSurjective, CFSG.Quasithin.IsSylowIn.coe_toSylow]
  have haN : a ∈ N := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set c : N ⧸ O := π ⟨a, haN⟩ with hc
  have hcZ : c ∈ Subgroup.center (N ⧸ O) := by
    refine Subgroup.mem_center_iff.mpr fun y => ?_
    induction y using QuotientGroup.induction_on with | H n => ?_
    rw [hc, hπ, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp n.2)
  have hco : orderOf c = p := by
    have hap : (⟨a, haN⟩ : N) ^ p = 1 :=
      Subtype.ext (by simpa [hao] using pow_orderOf_eq_one a)
    have hcp : c ^ p = 1 := by rw [hc, ← map_pow, hap, map_one]
    refine orderOf_eq_prime hcp fun h1 => ?_
    have hmem : (⟨a, haN⟩ : N) ∈ O := by
      rw [← QuotientGroup.ker_mk' O]
      exact h1
    have hdvd : orderOf (⟨a, haN⟩ : N) ∣ Nat.card O :=
      Subgroup.orderOf_coe (⟨⟨a, haN⟩, hmem⟩ : O) ▸ orderOf_dvd_natCard _
    rw [show orderOf (⟨a, haN⟩ : N) = p by rw [← Subgroup.orderOf_coe]; exact hao] at hdvd
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hO hdvd)
  have hKn := d1KBar_normal_of_escape he hUQ hUC hK
  have hKX : ¬ d1KBar p M N ≤ d1X0 p M N := fun hle => by
    obtain ⟨L, hL', hLX⟩ := exists_component_of_d1KBar_ne_bot hK
    exact hLX ((le_iSup₂_of_le L ⟨hL', hLX⟩ le_rfl : L ≤ d1KBar p M N).trans hle)
  have hrank : Open.pRank p (Rb : Subgroup (N ⧸ O)) ≤ 3 := by
    rw [hRbeq, pRank_map_mk_eq_pRank_map_subtype hp O hO, Subgroup.map_subgroupOf_eq_of_le hR.le]
    exact ((CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hRM).trans
      (local_pRank_le_evenRank p hp he.ne_two M he.maxTwoLocal_M.1)).trans hS.rank.le
  refine hKF p (N ⧸ O) (d1KBar p M N) (d1X0 p M N) Rb c hp he.ne_two hKn hL hZ hKX hcZ hco hrank
    fun A hA hAe hAc h3 => ?_
  rw [hRbeq] at hA h3
  exact normalizer_le_d1X0_of_escape he hR.le hRM hR.isPGroup A hA hAe hAc h3

variable (G) in
theorem agl81TenFourteenCentRestCfg_of_kfacts
    (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (h93O : KFactNineThreeOutPClosed) (hR2 : KFactNineThreeRankTwo)
    (hKF : KFactTenFourteenNarrowGamma) : AGL81TenFourteenCentRestCfg G := by
  intro hS p P M H Q K hd a _ hao _ hU
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  obtain ⟨U, hUC, hUQ⟩ := hU
  have ha : a ≠ 1 := fun ha1 => he.prime.one_lt.ne' (hao ▸ ha1 ▸ orderOf_one)
  have hCtop := centralizer_ne_top_of_setting hS ha
  have hlist := fun hK => nineThreeListGroup_d1KBar_of_escape h31 h75 hR2 hS hS.kProper he hUQ
    hUC hCtop hK
  exact ⟨fun hK => factor_of_escape h93O he hUQ hUC hK (hlist hK),
    fun hK => tenFourteenOneGroup_of_nineThreeList (kFactTenFourteenNarrow_of_gamma hKF) hS he hao
      hUC hUQ hK (hlist hK) (center_d1KBar_eq_bot_of_escape h31 hS.kProper he hUQ hUC hCtop hK)⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
