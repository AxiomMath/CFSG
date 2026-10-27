module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.EqGamma

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem gamma_of_hyps (h27 : Segev27) (hU : U35Facts) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hCls : Vert GzClassFacts a z) (hF3 : Vert Fusion3Facts a z)
    (hPar : Vert ParityFacts a z) (hT4 : Vert TableIVFacts a z) (hPerp : Vert PerpFacts a z)
    (hT5 : Vert TableVFacts a z) (h4B : Vert FourBFacts a z) (h6A : Vert SixAFacts a z)
    (hT7 : Vert TableVIIFacts a z) (hLines : Vert LinesFacts a z) (hOdd : Vert OddInvFacts a z)
    (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z) (hCube : Vert CubeFacts a z)
    (hOrb : Vert GzOrbitFacts a z) (hNo : Vert GzNoFacts a z) : GammaFacts a z := by
  have H : GammaHyps a z := ⟨h27, hU, h, hF1, hF2, hF3, hCube, hOrb, hCls, hNo, hPar, hT4,
    hPerp, hT5, h4B, h6A, hT7, hLines, hOdd⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, gamma_connected H, ?_⟩
  · intro x y t hx _ _ ht hy
    exact gamma_inv_one (H.at hx)
      (by simpa only [gamma_orb2A_eq hx, gamma_orb2B_eq hx, gamma_orb4A_eq hx,
        gamma_orb4B_eq hx, gamma_orb5A_eq hx] using hy)
      (by simpa only [gamma_orb2A_eq hx] using ht)
  · intro x y t b hx _ _ ht hy hb htb
    exact gamma_inv_two_i (H.at hx)
      (by simpa only [gamma_orb3A_eq hx, gamma_orb6A_eq hx] using hy)
      (by simpa only [gamma_orb2A_eq hx] using hb) (by simpa only [gamma_orb2A_eq hx] using ht)
      (by simpa only [gamma_orb2A_eq hx, gamma_orb2B_eq hx, gamma_orb3A_eq hx,
        gamma_orb4B_eq hx, gamma_orb6A_eq hx] using htb)
  · intro x y t b hx _ _ ht _ hb htb
    exact gamma_inv_two_ii (H.at hx) (by simpa only [gamma_orb2A_eq hx] using hb.1)
      (hx.symm.trans ht.1) (by simpa only [gamma_orb4A_eq hx] using htb)
  · intro x y t hx _ _ ht hy
    obtain ⟨y₁, hy₁, hty₁⟩ := gamma_five_E (H.at hx)
      (by simpa only [gamma_orb5E_eq hx] using hy) (by simpa only [gamma_orb2A_eq hx] using ht)
    exact ⟨y₁, by simpa only [gamma_orb2A_eq hx, gamma_orb2B_eq hx, gamma_orb4A_eq hx,
      gamma_orb4B_eq hx, gamma_orb6A_eq hx] using hy₁,
      by simpa only [gamma_orb2A_eq hx] using hty₁⟩
  · intro x y t hx _ hyx ht
    have hmem := gamma_mem_gamma (H.at hx) (by simpa only [gamma_gammaSet_eq hx] using hyx)
      (by simpa only [gamma_orb2A_eq hx] using ht)
    simpa only [gamma_gammaSet_eq hx] using hmem
  · intro x y hx hy
    simpa only [gamma_gammaSet_eq hx] using gamma_eq_gamma (H.at hx) (hx.symm.trans hy)

end CFSG.EvenSporadicStandard.HNRecog.Section3
