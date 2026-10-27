module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Quot
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Exp
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Plumb
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_PComp
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_J0
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Apply
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup Equiv
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem ZJFrame.exists_alt {p : ℕ} {Y : Type} [Group Y] [Finite Y] {K D V : Subgroup Y} [K.Normal]
    (hK1 : KFactZJFactorization) (hK2 : KFactAlmostSimpleRankTwo) (hZ : ZJFrame p K D V) :
    ∃ L : Subgroup (Y ⧸ K), CFSG.IsComponent L ∧
      ∃ n : ℕ, Nonempty (L ⧸ center L ≃* alternatingGroup (Fin n)) := by
  classical
  have hp := hZ.pre.prime
  have hp2 := hZ.pre.odd
  have hKcop := hZ.pre.coprime
  have hF := hZ.pre.quotient
  obtain ⟨L, hL, hpL, hcat⟩ := hZ.exists_component
  obtain ⟨hLn, hLz, hLc, hLs, hLnab⟩ := hF.component_data hL
  let q1 : L ⧸ Subgroup.center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hLz).trans QuotientGroup.quotientBot
  by_cases halt : ∃ n : ℕ, Nonempty (L ≃* alternatingGroup (Fin n))
  · obtain ⟨n, ⟨e⟩⟩ := halt
    exact ⟨L, hL, n, ⟨q1.trans e⟩⟩
  · exfalso
    have hcatL : IsCatalogGroup L := CFSG.AGLEmbedding.IsCatalogGroup.of_mulEquiv q1.symm hcat
    have hK2' := hK2 p hp hp2 (Y ⧸ K) L hLs hLnab hcatL halt hLc hF.rank_le
    obtain ⟨hcl, hchev⟩ := hK2'
    have hjoin : p ∣ Nat.card (invariantTwoJoinIn (D.map (QuotientGroup.mk' K)) L) :=
      hF.dvd_card_join_of_pClosed hLn hcl
    have hKeq : CFSG.pPrimeCore p Y = K := hZ.pre.pPrimeCore_eq
    subst hKeq
    have hpL' : p ∣ Nat.card L := by
      rw [← Nat.card_congr q1.toEquiv]
      exact hpL
    obtain ⟨J, hJn, hJc, hJL, hJp, hJJ, hJK⟩ := exists_pComponent_normal hp hL hLn hLz hpL'
    have hJ0 := zj_J0 hZ hLs hLc hJn hJL hJp hJJ hJK
    have hDp : IsPGroup p D := IsPGroup.of_card hZ.pre.card
    have hnc : ∀ Z : Subgroup Y, Z ≤ V → Z ≠ ⊥ → (Z.subgroupOf V).Characteristic →
        ¬ J ≤ normalizer (Z : Set Y) ⊔ CFSG.pPrimeCore p Y := by
      intro Z hZV hZ1 hZc hJZ
      have hDZ : D ≤ normalizer (Z : Set Y) := hZ.D_norm.trans (zjq_normalizer_le hZV hZc)
      refine zj_not_covers hp hp2 hKcop hDp hjoin hDZ (hZ.noncover Z hZV hZ1 hZc) ?_
      rw [← hJL]
      refine (Subgroup.map_mono hJZ).trans ?_
      rw [Subgroup.map_sup]
      have : (CFSG.pPrimeCore p Y).map (QuotientGroup.mk' (CFSG.pPrimeCore p Y)) = ⊥ :=
        (QuotientGroup.map_mk'_self _)
      rw [this, sup_bot_eq]
    rcases zj_apply hp hp2 hK1 hZ.sections hZ.charTwo hZ.pre.rank_le hZ.rank3 hZ.sylow2 hJn hJc hLs
        hLnab hLn hLc hJL hJp hZ.V_two hZ.core_le hJ0 hnc with hchevL | ⟨n, hn⟩
    · exact hchev hchevL (D.map (QuotientGroup.mk' _)) hF
        (NormalizerExponent.quotient hp hKcop hDp hZ.exp) hjoin
    · exact halt ⟨n, hn⟩

section G
variable {G : Type} [Group G] [Finite G]

theorem gl83RelPair2ThompsonAlt_of_kfacts (hS : Setting G) (hD1 : TheoremD1 G)
    (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    (hK1 : KFactZJFactorization) (hK2 : KFactAlmostSimpleRankTwo) :
    GL83RelPair2ThompsonAlt G := by
  intro p hp P M D R T H V hd hopt hfacts
  obtain ⟨L, hL, hn⟩ := (hopt.zjFrame hS hD1 hR h13 hp hd hfacts).exists_alt hK1 hK2
  exact ⟨L, (CFSG.isComponent_iff_open L).mp hL, hn⟩

end G

end CFSG.LocalAnalysis.RankThreeTheoremC
