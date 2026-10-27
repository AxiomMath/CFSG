module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVEven
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIdent
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVComponents
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGuest
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeakCentral

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem stmtSmallGEV_of_residues3 (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp)
    (hNo2 : KFactSmallNoTwo) (hShape : KFactSmallSylowShape) (hOrb : KFactSmallOrbits)
    (hT : ThompsonNormalAbelianGen) (hK6 : KFactFi22GuestRank) (hβ : KFactBeta)
    (hα : KFactAlphaW) (hN : D1SmallGEVNormal) (hIb : D1SmallGEVStarIb)
    (hFr : D1SmallGEVStarFree) : StmtSmallGEV := by
  intro G _ _ p P M H R Rbar K hd huniq z hz hIa hB0 hEv hIso hA6 hU3 hL hFi
  have hgp : ¬ (IsAltTwoP p K ∧ 7 ≤ p ∧ (11 ≤ p ∨ 3 ∈ GLBBetaFour G)) :=
    fun h => stmtSmallGuest_of hT hK6 G p P M H R Rbar K hd (Or.inl h)
  obtain ⟨hcardR, -⟩ := hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 (d1SmallLa_of_not hL)
  have hcomm := hd.twoCore_comm_mem_core hNo2 hz hB0 hIso hFi hcardR
  have hnot := hd.not_twoCore_inf_le hOut hExp hShape hOrb hz hB0 hA6 hL hFi
  have hne := hd.twoCore_inf_core_ne_bot hOut hExp hNo2 hShape hOrb hz hB0 hIso hA6 hL hFi
  have hV := hd.pCoreOf_two_glbPrimeCore_ne_bot hz hne
  have hcfg_of : ∀ Hs : Subgroup G, GLBIsMaxTwoLocal Hs →
      Subgroup.normalizer
        (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ Hs →
      ∃ Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p),
        D1ComponentConfig p P M Hs R Rbars := by
    intro Hs hHs hVHs
    obtain ⟨-, -, hext⟩ := hd.extremal_of_normalizer_le hz hHs hVHs
    have hcon : ¬ HasPrimeConstraint (G := Hs) p := fun hc =>
      d1ConstrainedCase_of_kFactsW hβ hα G hd.cfg.glob p P M hd.cfg.loc Hs R hext hc
    exact hext.exists_componentConfig hd.cfg.glob hd.cfg.loc hcon hd.cfg.ind
  by_cases hex : ∃ Hs : Subgroup G, GLBIsMaxTwoLocal Hs ∧
      Subgroup.normalizer
        (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ Hs ∧
      ∃ hzHs : z ∈ Hs, (Subgroup.zpowers
        (QuotientGroup.mk' (primeComplementCore (G := Hs) p) ⟨z, hzHs⟩)).Normal
  · obtain ⟨Hs, hHs, hVHs, hzHs, hA⟩ := hex
    obtain ⟨hCHs, -, -⟩ := hd.extremal_of_normalizer_le hz hHs hVHs
    obtain ⟨Rbars, hcfg⟩ := hcfg_of Hs hHs hVHs
    obtain ⟨Ls, hds, hzs, hIas, ⟨eL⟩, hcore⟩ :=
      hd.smallDataIa_of_normal_zpowers hz hIso hCHs hcfg hA
    exact hN G p P M Hs R Rbars Ls hds z hzs hIas hB0 hEv
      (fun KC hKC => (hIso KC hKC).map fun f => f.trans eL.symm)
      (fun ⟨h3, ⟨f⟩⟩ => hA6 ⟨h3, ⟨eL.symm.trans f⟩⟩)
      (fun ⟨h3, d, hd', ⟨f⟩⟩ => hU3 ⟨h3, d, hd', ⟨eL.symm.trans f⟩⟩)
      (fun ⟨h3, d, hd', ⟨f⟩⟩ => hL ⟨h3, d, hd', ⟨eL.symm.trans f⟩⟩)
      (fun ⟨h5, ⟨f⟩⟩ => hFi ⟨h5, ⟨eL.symm.trans f⟩⟩)
      (fun ⟨⟨f⟩, h7, h11⟩ => hgp ⟨⟨eL.symm.trans f⟩, h7, h11⟩)
      hcomm hnot hVHs hCHs hcore (fun _ => hA)
  have hall : ∀ Hs : Subgroup G, GLBIsMaxTwoLocal Hs →
      Subgroup.normalizer
        (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ Hs →
      ∀ hzHs : z ∈ Hs, ¬ (Subgroup.zpowers
        (QuotientGroup.mk' (primeComplementCore (G := Hs) p) ⟨z, hzHs⟩)).Normal :=
    fun Hs' hHs' hVHs' hzHs' hA' => hex ⟨Hs', hHs', hVHs', hzHs', hA'⟩
  have hNH : ¬ Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ H := by
    intro hle
    obtain ⟨-, -, hzH, -⟩ := id hz
    exact hex ⟨H, hd.cfg.ext.maxTwoLocal_H, hle, hzH,
      hd.zpowers_normal_of_ia hOut hExp hz hB0 (d1SmallLa_of_not hL) hIa hzH⟩
  obtain ⟨Hs, hHs, hVHs, hCHs, -, -⟩ := hd.exists_maxTwoLocal_normalizer_le hz hV
  obtain ⟨Rbars, hcfg⟩ := hcfg_of Hs hHs hVHs
  by_cases hB1 : ∃ Ls : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p), IsComponentOf Ls ⊤ ∧
      d1StarElt p hCHs ∈ Subgroup.centralizer (Ls : Set _)
  ·
    obtain ⟨Ls, hLs, hzsC⟩ := hB1
    obtain ⟨eL⟩ := hd.iso_of_centralized_component hz hIso hCHs hcfg hLs hzsC
    obtain ⟨hds, hzs⟩ := hd.smallData_of_component_iso hz hCHs hcfg hLs hzsC eL
    have hnIa : ¬ D1SmallIa p Hs Ls := by
      intro hIas
      have hL' : ¬ (p = 3 ∧ IsLinThreeFour Ls) := fun ⟨h3, d, hd', ⟨f⟩⟩ =>
        hL ⟨h3, d, hd', ⟨eL.symm.trans f⟩⟩
      exact hall Hs hHs hVHs (mem_of_centralizer_le hCHs)
        (hds.zpowers_normal_of_ia hOut hExp hzs hB0 (d1SmallLa_of_not hL') hIas
          (mem_of_centralizer_le hCHs))
    exact hIb G p P M H R Rbar K hd huniq z hz hIa hB0 hEv hIso hA6 hU3 hL hFi hgp hcomm hnot
      hall hNH Hs Rbars Ls hHs hVHs hCHs hds hzs hnIa
      (fun KC hKC => (hIso KC hKC).map fun f => f.trans eL.symm) ⟨eL⟩
  ·
    exact hFr G p P M H R Rbar K hd huniq z hz hIa hB0 hEv hIso hA6 hU3 hL hFi hgp hcomm hnot
      hall hNH Hs Rbars hHs hVHs hcfg fun _ L hL =>
        ⟨hd.mem_normalizer_component hz hCHs hcfg hL, fun hc => hB1 ⟨L, hL, hc⟩⟩

end CFSG.AGLEmbedding
