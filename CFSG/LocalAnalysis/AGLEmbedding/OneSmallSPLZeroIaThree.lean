module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroThreeSplit
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIaThreeTorus
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIaThreeNine
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIaThreePairM

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D1OneSmallData.not_coprime_card_component (hKSz : KFactSuzukiThreeCent)
    (hβ : KFactBeta) (hKO : KFactOneLie) (hTor : KFactOneLieTorus)
    (hd : D1OneSmallData 3 P M H R Rbar K) (h3 : D1PhaseThree 3 P M H R) {z : G}
    (hz : D1SmallCZElt 3 H R K z) (hSP : D1CzSP 3 z) (hout : D1CzOutside 3 z) (hzM : z ∈ M)
    (hzb3 : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩) ^ 3 = 1)
    (hZ : ∀ D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅D, D⁆ = D →
      D ≤ Subgroup.centralizer ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩} :
        Set (↥M ⧸ CFSG.pCore 2 ↥M)) → D = ⊥)
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤) :
    ¬ Nat.Coprime 3 (Nat.card Lb) := by
  intro hcop
  have hodd := hd.odd_card_inf_centralizer_of_component hβ hKO hTor hz hSP hout hzM hLb hcop
  have hMtop : M ≠ ⊤ := fun hM => h3.not_le (hM ▸ le_top)
  have hcat : IsCatalogGroup (↥Lb ⧸ Subgroup.center ↥Lb) :=
    ((catalogSimpleSections_of_isKProper h3.glob.kProper M hMtop).quotient
      _).isCatalogGroup_center_quotient hLb
  have h2 := hKSz _ Lb hLb hcat hcop _ (mem_normalizer_of_no_perfect_centralizer hLb hzb3 hZ)
    hzb3 (not_mem_centralizer_of_no_perfect_centralizer hLb hZ)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem d1SmallSPLZeroIaThree_of (hKB : KFactBlockThreeCentCoprime)
    (hKSz : KFactSuzukiThreeCent) (hUP : KFactUPrimeSmall) (hSTO : KFactSmallThreeOrders)
    (hSch : KFactCatalogSchreier) (hβ : KFactBeta) (hKO : KFactOneLie)
    (hΓ : KFactOneLieBorelSolvable) (hTor : KFactOneLieTorus) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) : D1SmallSPLZeroIaThree := by
  intro G _ _ P M H R Rbar K hd _ z hz hspl hSP hout _ hO hI
  obtain ⟨T, hT, h3, hUPK, houtK, hsT⟩ := hd.exists_kFacts_three hUP hSTO hSch hspl
  have hperf : ∀ U : Subgroup G, U ≤ H ⊓ M → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U) :=
    fun U hU hUp => hd.coprime_card_of_perfect hI hT hUPK houtK hsT hU hUp
  have hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L := fun L hL =>
    stmtBlockThree_of h85 h86 h93 hD2 hK2 hC3 hK5 h3 hL
  have hrank : CFSG.Open.pRank 3 (H ⊓ M) ≤ 3 := hd.pRank_le_three_of_le_H inf_le_left
  obtain ⟨hzR, hzp, -, -⟩ := id hz
  have hzM : z ∈ M := hd.cfg.ext.le_M hzR
  set zb := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ with hzb
  have hzb3 : zb ^ 3 = 1 := by
    have h1 : (⟨z, hzM⟩ : M) ^ 3 = 1 := Subtype.ext (by simp [← hzp, pow_orderOf_eq_one])
    rw [hzb, ← map_pow, h1, map_one]
  have hZ : ∀ D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅D, D⁆ = D →
      D ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → D = ⊥ :=
    fun D hD hDz => hd.eq_bot_of_perfect_le_centralizer hβ hKO hΓ hSch hz hSP hout hzM hD hDz
  have hno3 : ∀ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ →
      ¬ Nat.Coprime 3 (Nat.card Lb) := fun Lb hLb =>
    hd.not_coprime_card_component hKSz hβ hKO hTor h3 hz hSP hout hzM hzb3 hZ hLb
  obtain ⟨n, e, X, φ, hn2, he, hXCM, htor, hpair⟩ := hd.exists_torus_pair_cz hβ hTor hz hSP hout
  by_cases hn3 : 3 ≤ n
  · obtain ⟨r, tb, hr5, hXel, hXcard, ht6, htz, htX, hnt, hirr⟩ :=
      mside_torus_of_big hzM φ hn3 he hXCM htor
    have hX27 : 3 ^ 3 ≤ Nat.card (barM M X) := by
      rw [← hXcard]
      exact Nat.pow_le_pow_right (by norm_num) hn3
    have hirr1 : ∀ F : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), F ≤ barM M X →
        tb ∈ Subgroup.normalizer (F : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → F = ⊥ ∨ F = barM M X :=
      fun F hF htF => hirr 1 (fun h => by have := Nat.le_of_dvd one_pos h; omega) F hF
        (by rwa [pow_one])
    have hX1 : barM M X ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hX27
      norm_num at hX27
    refine hd.false_of_le_centralizer_comps h3 hUPK h84 hD2 hO
      (IsPGroup.of_card (n := n) hXcard.symm) hX1 (fun Lb hLb => ?_) ?_
    · exact le_centralizer_threeComponents_of_torus hKB h3 h85 h93 hD2 hB3 hrank hperf hzb3 hZ
        hXel.1 (le_trans (by norm_num) hX27) ht6 htz htX hnt hirr1 hLb (hno3 Lb hLb)
    · intro s hs hs2 hs3
      exact oddCore_dichotomy_of_torus hXel (le_trans (by norm_num) hX27) (by omega : 4 ≤ r) htX
        hirr s hs hs2 hs3
  ·
    have h2 : n = 2 := by omega
    subst h2
    have he1 : e = 1 := by
      rcases he with h | ⟨-, h⟩
      · exact h
      · omega
    subst he1
    obtain ⟨W, t, hXW, hWCM, hW3, hW6, hcen, hXder, htCM, htW, htX, ht6, hnt, hlay⟩ :=
      hpair rfl
    have hXM : X ≤ M := fun x hx => (hXCM hx).2
    obtain ⟨hXel, hXcard⟩ := barM_galois hXM (by norm_num) φ
    obtain ⟨μ, hμ⟩ := exists_gen_gf9
    obtain ⟨t₈, ht₈, ht₈a⟩ := htor μ
    obtain ⟨ht₈X, hirr⟩ := mside_torus_two hXM φ ht₈.2 hμ (fun a => by rw [ht₈a a, pow_one])
    have hX1 : barM M X ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hXcard
      norm_num at hXcard
    refine hd.false_of_le_centralizer_comps h3 hUPK h84 hD2 hO
      (IsPGroup.of_card (n := 2) hXcard) hX1 (fun Lb hLb => ?_) ?_
    · exact le_centralizer_threeComponents_of_pair_G hKB h3 h85 h93 hD2 hB3 hrank hperf hzM hZ
        hzb3 hXW hWCM hW3 hW6 (isElemAbelian_of_galois (by norm_num) φ).2 hcen hXder htCM htW
        htX ht6 hnt hlay hLb (hno3 Lb hLb)
    · intro s hs hs2 hs3
      exact oddCore_dichotomy_of_torus hXel hXcard.ge (le_refl 4) ht₈X hirr s hs hs2 hs3

end CFSG.AGLEmbedding
