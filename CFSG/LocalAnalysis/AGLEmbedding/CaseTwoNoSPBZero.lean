module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoSPResidues
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPoszAux
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfigAt

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1ComponentConfig.b0_of_shape (hcfg : D1ComponentConfig p P M H R Rbar) {z : G}
    (hzp : orderOf z = p) (hzR : z ∈ R) (hRz : R ≤ Subgroup.centralizer ({z} : Set G))
    (hCM : ¬ Subgroup.centralizer ({z} : Set G) ≤ M) (hnSP : ¬ D1CzSP p z)
    (hshape : D1CzShape p P M R z) :
    D1CzB0 p R z ∧ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≠ ⊥ ∧ D1CzEven p z :=
  hcfg.toU.b0_of_shape hzp hzR hRz hCM hshape fun m _ T _ _ h => by
    have hQ'4 : 4 ≤ Open.pRank p ((P : Subgroup G).map (MulAut.conj m).toMonoidHom) := by
      have := betaFour_all_sylows_rank_ge_four hcfg.loc.beta (m • P)
      rwa [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at this
    have h1 := pRank_mono p hcfg.red.prime
      (Subgroup.map_subtype_le (T : Subgroup (Subgroup.centralizer ({z} : Set G))))
    have h2 : ¬ 4 ≤ Open.pRank p (Subgroup.centralizer ({z} : Set G)) := hnSP
    rw [h] at h1
    omega

theorem D1CaseTwoData.allOutEV (hS : D1CaseTwoShape) (hd : D1CaseTwoData p P M H R Rbar)
    (hnosp : D1CaseTwoNoSP p M H R)
    (hout : ∀ z : H, D1CaseTwoCand p M H R z → D1CzOutside p (z : G)) :
    D1CaseTwoAllOutEV p M H R := by
  intro z hz
  obtain ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩ := hz
  have hnSP := hnosp L hL hLX z hzR hzp hRz hzL
  have hshape := hS G p P M H R Rbar hd z ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩ hnSP
    (hout z ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩)
  obtain ⟨hB0, hne, hev⟩ := D1ComponentConfig.b0_of_shape hd.cfg hzp hzR hRz
    (hd.cfg.centralizer_not_le hLX z.2 hzp hzL) hnSP hshape
  exact ⟨hout z ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩, hB0, hne, hev⟩

theorem d1CaseTwoPosZeroNoSP_of (hS : D1CaseTwoShape) (hEV : D1CaseTwoPosZeroEV)
    (hIn : D1CaseTwoPosZeroIn) : D1CaseTwoPosZeroNoSP := by
  intro G _ _ p P M H R Rbar hd hnosp hU h0
  by_cases h : ∃ z : H, D1CaseTwoCand p M H R z ∧ ¬ D1CzOutside p (z : G)
  · exact hIn G p P M H R Rbar hd hnosp h hU h0
  · push Not at h
    exact hEV G p P M H R Rbar hd hnosp (D1CaseTwoData.allOutEV hS hd hnosp h) hU h0

theorem d1CaseTwoNTwoAResNoSP_of (hS : D1CaseTwoShape) (hEV : D1CaseTwoNTwoAResEV)
    (hIn : D1CaseTwoNTwoAResIn) : D1CaseTwoNTwoAResNoSP := by
  intro G _ _ p P M H R Rbar hd hnosp hU L₁ L₂ h1 h2 h3 h4 h5 h6
  by_cases h : ∃ z : H, D1CaseTwoCand p M H R z ∧ ¬ D1CzOutside p (z : G)
  · exact hIn G p P M H R Rbar hd hnosp h hU L₁ L₂ h1 h2 h3 h4 h5 h6
  · push Not at h
    exact hEV G p P M H R Rbar hd hnosp (D1CaseTwoData.allOutEV hS hd hnosp h) hU L₁ L₂ h1 h2
      h3 h4 h5 h6

theorem d1CaseTwoZZThreeNoSP_of (hS : D1CaseTwoShape) (hEV : D1CaseTwoZZThreeEV)
    (hIn : D1CaseTwoZZThreeIn) : D1CaseTwoZZThreeNoSP := by
  intro G _ _ P M H R Rbar hd hnosp hU L₁ h1 h2 h3 h4 h5 z h6 h7 h8 h9
  by_cases h : ∃ z : H, D1CaseTwoCand 3 M H R z ∧ ¬ D1CzOutside 3 (z : G)
  · exact hIn G P M H R Rbar hd hnosp h hU L₁ h1 h2 h3 h4 h5 z h6 h7 h8 h9
  · push Not at h
    exact hEV G P M H R Rbar hd hnosp (D1CaseTwoData.allOutEV hS hd hnosp h) hU L₁ h1 h2 h3 h4
      h5 z h6 h7 h8 h9

end CFSG.AGLEmbedding
