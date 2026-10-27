module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7SylowCert
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7SylowChecks
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7CentYZ
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcJ
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Classes

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction

theorem oddDerivE7YFrame_facts :
    (∀ σ ∈ oddDerivE7YFrame, IsRoot .E7 σ ∧ 0 < height σ) ∧ oddDerivE7YFrame.Nodup ∧
      oddDerivE7YFrame.Pairwise fun σ σ' => iform σ σ' = 0 := by
  have h : (∀ σ ∈ oddDerivE7YFrame, List.ofFn σ ∈ Tag.artifactRoots .E7 ∧ 0 < height σ) ∧
      oddDerivE7YFrame.Nodup ∧ oddDerivE7YFrame.Pairwise fun σ σ' => iform σ σ' = 0 := by
    decide +kernel
  exact ⟨fun σ hσ => ⟨isRoot_iff_mem_artifactRoots.2 (h.1 σ hσ).1, (h.1 σ hσ).2⟩, h.2⟩

theorem e7FrameY_facts : e7FrameY ≠ [] ∧ e7FrameY.Nodup ∧
    (∀ σ ∈ e7FrameY, IsRoot .E7 σ ∧ 0 < height σ) ∧
      e7FrameY.Pairwise fun σ σ' => iform σ σ' = 0 := by
  obtain ⟨h1, h2, h3⟩ := e7Frames_facts e7FrameY (by simp)
  exact ⟨h1, h2, fun σ hσ => ⟨(isRoot_of_mem_e7Frames σ (by simp_all)).1,
    (isRoot_of_mem_e7Frames σ (by simp_all)).2.2⟩, h3⟩

variable {K : Type} [Field K]

section Certs


theorem sylowData_e7ASY [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    Exc.SylowData (e7FramePt K oddDerivE7YFrame) (e7FrameLine K oddDerivE7YFrame) :=
  sylowData_of_e7SylowCheck h4 oddDerivE7YFrame_facts.1 oddDerivE7YFrame_facts.2.1
    oddDerivE7YFrame_facts.2.2 e7SylowCheck_y

theorem e7FrameElt_conj_e7WordY_syl [CharP K 2] (d : K) :
    e7WeylRep K ((coxeterSystem .E7).wordProd e7WordY) * e7FrameElt K oddDerivE7YFrame d *
        (e7WeylRep K ((coxeterSystem .E7).wordProd e7WordY))⁻¹ = e7FrameElt K e7FrameY d := by
  rw [e7FrameElt_conj_word e7WordY fun σ hσ => (oddDerivE7YFrame_facts.1 σ hσ).1, e7WordY_map]

theorem sylowData_e7FrameY [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    Exc.SylowData (e7FramePt K e7FrameY) (e7FrameLine K e7FrameY) := by
  have h := (sylowData_e7ASY (K := K) h4).conj
    (e7WeylRep K ((coxeterSystem .E7).wordProd e7WordY))
  rwa [← e7FrameElt_one, e7FrameElt_conj_e7WordY_syl, e7FrameElt_one,
    map_conj_e7FrameLine_of e7FrameElt_conj_e7WordY_syl] at h

theorem centreData_e7FrameY [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    Exc.CentreData (e7FramePt K e7FrameY) (e7FrameLine K e7FrameY) := by
  obtain ⟨hne, hnd, hF, ho⟩ := e7FrameY_facts
  exact centreData_e7FrameLine hne hnd hF ho commute_e7FrameLine_Y
    (sylowData_e7FrameY h4)

theorem regular_e7FrameY [Finite K] [CharP K 2] :
    ∃ u, Exc.Regular (e7FrameLine K e7FrameY) u := by
  obtain ⟨hne, hnd, hF, ho⟩ := e7FrameY_facts
  exact regular_e7FrameLine hne hnd hF ho commute_e7FrameLine_Y

end Certs

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
