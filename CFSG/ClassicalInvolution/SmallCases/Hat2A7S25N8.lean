module

public import Mathlib
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25N7
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25FW4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S.N

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ClassicalInvolution.Hat2A7M.Asc77.T7F2 (Hyp25T)
open scoped MatrixGroups

section Bridge




theorem w3Five_proved : W3Five := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF' hdiv
  obtain ⟨t', h⟩ := Hat2A7M.Asc77.T7T.exists_hyp25T hyp.toMirror
  have haN : a ∈ Subgroup.normalizer (K' : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (fix_of_isFAut h haS hF').2.2.2
  obtain ⟨zc, hzc⟩ := h.hs.stand.classical K' h.hK'
  obtain ⟨π, zE, cov, -⟩ := Hat2A7.exists_cover_of_witness hzc.witness
  have hε : Hat2A7.epsG cov a = -1 :=
    Hat2A7S.epsG_eq_neg_one_of_isFAut cov h.hR'syl h.hz' haN ha2 hF'
  exact ⟨Hat2A7S.W3_five haN cov ha2 hε hdiv, fun x hxK hxb hx2 =>
    Hat2A7S.W3_five_mem haN cov ha2 hε hdiv hxK hxb hx2⟩

theorem w3Three_proved : W3Three := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF' hndiv
  obtain ⟨t', h⟩ := Hat2A7M.Asc77.T7T.exists_hyp25T hyp.toMirror
  have haN : a ∈ Subgroup.normalizer (K' : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (fix_of_isFAut h haS hF').2.2.2
  obtain ⟨zc, hzc⟩ := h.hs.stand.classical K' h.hK'
  obtain ⟨π, zE, cov, -⟩ := Hat2A7.exists_cover_of_witness hzc.witness
  have hε : Hat2A7.epsG cov a = -1 :=
    Hat2A7S.epsG_eq_neg_one_of_isFAut cov h.hR'syl h.hz' haN ha2 hF'
  exact Hat2A7S.W3_three haN cov ha2 hε hndiv


theorem a7NoFFz_of_c25_11 (h11 : A7C25_11) : A7NoFFz :=
  a7NoFFz_of_w3 h11 w3Five_proved w3Three_proved

end Bridge

end CFSG.ClassicalInvolution.Hat2A7S.N
