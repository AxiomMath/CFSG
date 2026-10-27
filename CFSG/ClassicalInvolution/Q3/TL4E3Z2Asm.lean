module

public import CFSG.ClassicalInvolution.Q3.TL4E3C269Defs
public import CFSG.ClassicalInvolution.Q3.TL4E3OneOrbitC
public import CFSG.ClassicalInvolution.Q3.TL4SecIdFam
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Odd

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

section Plus


theorem tightE3Z2F_of_leaves'' {n : ℕ} (h4 : Thm4RBelow 3 n)
    (hD : TightBelowRPlus 3 n → TightS26DichR 3 n)
    (h264 : TightBelowRPlus 3 n → TightC26_4RG n)
    (hsec : TightE3Z2Sec163 n) (h269 : TightE3C269S n) (hfin : TightE3Z2Fin n) :
    TightE3Z2F n := by
  intro Y _ _ R S t J u hF htu ht Sb hex hedge hμ
  by_contra hnE2
  have hLC : TightLambdaCommR 3 n :=
    tightLambdaCommR_three_of_plus hF.plus hF.large.below h4 secIdE4OddCent_proved
  have h163 := hsec Y R S t J u hF htu ht Sb hex hedge hμ hnE2
  have hOJ := hF.omegaNbr_subset_orbOf htu ht h163
  obtain ⟨g, Sd, S', R', T, W, hgJ, hu, hs⟩ := hF.exists_std8
  have hcore : tightCore (conjSub g R) = J := by rw [← conjSub_tightCore, hgJ]
  have hα : TightSepAlpha (conjSub g R) u := hu ▸ hF.alpha.conj g
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hmu : MuIsoE4 (CoreAssembly.conjClass (tightCore (conjSub g R))) W ∨
      MuIsoS4 (CoreAssembly.conjClass (tightCore (conjSub g R))) W := by
    refine hs.muIso_E4_or_S4_of_uniq ?_
    rw [hfam]
    exact hF.partnerUniq_of_oneOrbit hOJ hF.t_mem_centralizer hF.t_mem_secH hμ (hfam ▸ hs.hW.1)
  rcases hmu with hE4 | hS4
  · rcases h264 hF.plus Y (conjSub g R) Sd u (tightCore R) S' R' T W t hs
        (hs.sup_omegaNbrGen_ne_top_of_alpha hα) hE4 with h1 | h2
    · exact h269 hLC Y R S t J u hF htu ht Sb hex hedge hμ hnE2 h163 _ Sd S' R' T W hcore hs hE4
        h1
    · exact hnE2 (hfin Y R S t J u hF htu ht Sb hex _ Sd S' R' T W hcore hs h2)
  · exact hs.not_muIsoS4_of_alpha (hD hF.plus) hα hS4

end Plus

end CFSG.ClassicalInvolution.Q3.TL4
