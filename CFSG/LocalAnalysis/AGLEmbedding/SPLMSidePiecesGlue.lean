module

public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePieces
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallCentralizer

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem SPLMSide.splBar_pow {G : Type} [Group G] {M : Subgroup G} {g : G} (hg : g ∈ M) (n : ℕ) :
    splBar hg ^ n = splBar (M.pow_mem hg n) := by
  unfold splBar
  rw [← map_pow]
  rfl

theorem d1SPLMSideBridge_of_pieces (h1 : D1SPLPieceCentralizer) (h2 : D1SPLPieceCtilde)
    (h3 : D1SPLPieceTorus) (hZK : D1SPLPieceZK) (h4 : D1SPLPieceLemmaT)
    (h5 : D1SPLPieceBlocks) : D1SPLMSideBridge := by
  intro G _ _ p P M H R Rbar K hd huniq z hz hLA hSP hout hVK hVC hIa hN
  have D : D1SPLPairData p P M H R Rbar K z :=
    ⟨hd, huniq, hz, hLA, hSP, hout, hVK, hVC, hIa, hN⟩
  have hzM : z ∈ M := hd.cfg.ext.le_M hz.1
  obtain ⟨P', Pbar, KC, -, hP'M, hRP', hRC⟩ := hd.exists_reducedCentralizer hz hSP
  have hCt := h2 G p P M H R Rbar K z D P' Pbar KC hRC hRP' hP'M
  have hCz := h1 G p P M H R Rbar K z D hzM P' Pbar KC hRC hRP' hP'M hCt
  have hBl := h5 G p P M H R Rbar K z D
  obtain ⟨T₀, c₀, hc₀, r, hTo, hcr⟩ :=
    h3 G p P M H R Rbar K z D hzM P' Pbar KC hRC hRP' hP'M hCt hCz hBl
  have hEl := h4 G p P M H R Rbar K z D hzM hCz hBl (hZK G p P M H R Rbar K z D hzM) T₀ c₀ hc₀ r
    hTo
  have hzp : z ^ p = 1 := by rw [← hz.2.1]; exact pow_orderOf_eq_one z
  refine ⟨splBar hzM, splBar hc₀, r, barM M T₀, barM M (d1LiftX p H R K),
    barM M (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))), ?_⟩
  exact
    { prime := hd.cfg.red.prime
      ne_two := hd.cfg.red.ne_two
      u_pow := by
        rw [SPLMSide.splBar_pow]
        unfold splBar
        simp only [hzp]
        rfl
      u_norm := hCz.u_norm
      u_noncent := hCz.u_noncent
      solv := hCz.solv
      T_le := hTo.T_le
      X_le := hTo.X_le
      T_p := hTo.T_p
      O_coprime := by
        refine Nat.Coprime.coprime_dvd_right ?_
          (glbPrimeCore_coprime p (Subgroup.centralizer ({z} : Set G)))
        refine (Subgroup.card_map_dvd _ _).trans ?_
        rw [← Subgroup.card_map_of_injective M.subtype_injective, Subgroup.subgroupOf_map_subtype]
        exact Subgroup.card_dvd_of_le inf_le_left
      TO_norm := hTo.TO_norm
      T_X := hTo.T_X
      T_O := hTo.T_O
      TT := hTo.TT
      Tp := hTo.Tp
      index := hTo.index
      E_le := hEl
      c_mem := hTo.c_mem
      c_T := hTo.c_T
      c_X := hTo.c_X
      c_pow := hcr
      r_prime := hTo.r_prime
      r_dvd := hTo.r_dvd
      r_ndvd := hTo.r_ndvd
      irr := hTo.irr
      X_elem := hBl.X_elem
      X_card := hBl.X_card
      X_E := hBl.X_E
      Z_X := hBl.Z_X
      rank := hCz.rank
      CT_odd := hTo.CT_odd
      catalog := hBl.catalog
      types := hBl.types }

end CFSG.AGLEmbedding
