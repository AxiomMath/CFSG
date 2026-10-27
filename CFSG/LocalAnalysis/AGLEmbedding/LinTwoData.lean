module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorel
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorelAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoDataAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoReduced
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorus
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoUnipotentCentralizer
import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

section Extremal

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {P : Sylow p G}
  {M H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1Extremal.d1L2Data (hext : D1Extremal p P M H R)
    (hglob : CFSG.AGLEmbeddingD2.AGLGlobal G) (hind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q)
    (hrbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hred : ReducedNongeneration p (H ⧸ primeComplementCore (G := H) p) Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))))
    (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype)
    {n : ℕ} {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex p n d)
    (e : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    D1L2Data p n P M H R (d1LiftX p H R K) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hred.ne_two
  have hn1 : 1 ≤ n := by
    obtain ⟨q, -, -, rfl⟩ := hd
    exact q.exponent_pos
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  obtain ⟨⟨eK⟩, hC⟩ := hred.nonempty_mulEquiv_psl2GF_and_centralizer_eq_bot hK huniq hcent hd e
  have hrankH : Open.pRank p (⊤ : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤ n :=
    pRank_top_le_of_psl2GF hp2 hn1 ⟨eK⟩ hC
  have h3 : 3 ≤ n := hred.three_le_pRank.trans ((pRank_mono p hp le_top).trans hrankH)
  obtain ⟨hX₀K, hD1, hDp, hsolv, -⟩ := stmtLinTwoBorel Rbar _ K hred h3 hKn ⟨eK⟩ hC
  have hNHM : GLBPrimeCore p H ≤ H ⊓ M := hext.primeCore_le_inf'.1
  have hXH : d1LiftX p H R K ≤ H := d1LiftX_le_H p H R K
  have hX : IsPGroup p (d1LiftX p H R K) := hext.isPGroup.to_le (d1LiftX_le p H R K)
  have hXU : ((d1LiftX p H R K).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K := by
    rw [map_d1LiftX, hrbar]
  refine ⟨?_, hind, h3, d1LiftX_le p H R K, ?_,
    fun Y hY hYN => le_glbPrimeCore_or_le_of_forall hext.primeCore_le hXH hX
      (by rw [hXU]; exact hD1) hY hYN,
    fun Y hY hYN hYp => le_sup_glbPrimeCore_of_forall (by rw [hXU]; exact hDp) hY hYN hYp,
    pRank_inf_le_of_pRank_top_le hp hrankH, fun L hL hLL => le_glbPrimeCore_of_perfect hsolv hL hLL⟩
  ·
    exact hext.toPhaseThreeU hglob (hext.primeCore_inf_eq_iff.mpr
      (primeComplementCore_eq_bot_of_psl2GF kFactL2UnipotentCentralizer Rbar _ hred h3 hKn
        ⟨eK⟩ hC))
  ·
    have : K.Normal := hKn
    obtain ⟨-, hUcard⟩ := isElemAbelian_sylow_inf_of_psl2GF hn1 eK Rbar
    obtain ⟨ψ, hψinj, hψU, hψc⟩ :=
      exists_torus_param_of_mulEquiv_psl2GF hp2 hn1 eK _ inf_le_right hUcard
    refine exists_torus_of_map_subgroupOf_eq hXH hX hNHM ψ hψinj (hψU.trans hXU.symm)
      fun μ => ?_
    obtain ⟨c, hcK, hc⟩ := hψc μ
    have hcN := mem_normalizer_range_of_torus ψ μ.ne_zero hc
    rw [hψU] at hcN
    have hcX₀ : c ∈ (((H ⊓ M).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p))) ⊓ K := by
      rw [hX₀K]
      exact ⟨hcK, hcN⟩
    exact ⟨c, hcX₀.1, hc⟩

end Extremal

namespace D1ComponentConfig

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {P : Sylow p G}
  {M H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem d1L2Data (hcfg : D1ComponentConfig p P M H R Rbar) (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype)
    {n : ℕ} {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex p n d)
    (e : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    D1L2Data p n P M H R (d1LiftX p H R K) :=
  hcfg.ext.d1L2Data hcfg.glob.toAGLGlobal hcfg.ind hcfg.rbar hcfg.red hK huniq hcent hd e

end D1ComponentConfig

theorem stmtL2Data : StmtL2Data := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hcent n d hd e
  exact hcfg.d1L2Data hK huniq hcent hd e

end CFSG.AGLEmbedding
