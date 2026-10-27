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

theorem oddDerivE7ZFrame_facts :
    (∀ σ ∈ oddDerivE7ZFrame, IsRoot .E7 σ ∧ 0 < height σ) ∧ oddDerivE7ZFrame.Nodup ∧
      oddDerivE7ZFrame.Pairwise fun σ σ' => iform σ σ' = 0 := by
  have h : (∀ σ ∈ oddDerivE7ZFrame, List.ofFn σ ∈ Tag.artifactRoots .E7 ∧ 0 < height σ) ∧
      oddDerivE7ZFrame.Nodup ∧ oddDerivE7ZFrame.Pairwise fun σ σ' => iform σ σ' = 0 := by
    decide +kernel
  exact ⟨fun σ hσ => ⟨isRoot_iff_mem_artifactRoots.2 (h.1 σ hσ).1, (h.1 σ hσ).2⟩, h.2⟩

theorem e7FrameZ_facts : e7FrameZ ≠ [] ∧ e7FrameZ.Nodup ∧
    (∀ σ ∈ e7FrameZ, IsRoot .E7 σ ∧ 0 < height σ) ∧
      e7FrameZ.Pairwise fun σ σ' => iform σ σ' = 0 := by
  obtain ⟨h1, h2, h3⟩ := e7Frames_facts e7FrameZ (by simp)
  exact ⟨h1, h2, fun σ hσ => ⟨(isRoot_of_mem_e7Frames σ (by simp_all)).1,
    (isRoot_of_mem_e7Frames σ (by simp_all)).2.2⟩, h3⟩

variable {K : Type} [Field K]

section Certs


theorem sylowData_e7ASZ [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    Exc.SylowData (e7FramePt K oddDerivE7ZFrame) (e7FrameLine K oddDerivE7ZFrame) :=
  sylowData_of_e7SylowCheck h4 oddDerivE7ZFrame_facts.1 oddDerivE7ZFrame_facts.2.1
    oddDerivE7ZFrame_facts.2.2 e7SylowCheck_z

theorem e7FrameElt_conj_e7WordZ_syl [CharP K 2] (d : K) :
    e7WeylRep K ((coxeterSystem .E7).wordProd e7WordZ) * e7FrameElt K oddDerivE7ZFrame d *
        (e7WeylRep K ((coxeterSystem .E7).wordProd e7WordZ))⁻¹ = e7FrameElt K e7FrameZ d := by
  rw [e7FrameElt_conj_word e7WordZ fun σ hσ => (oddDerivE7ZFrame_facts.1 σ hσ).1, e7WordZ_map]

theorem sylowData_e7FrameZ [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    Exc.SylowData (e7FramePt K e7FrameZ) (e7FrameLine K e7FrameZ) := by
  have h := (sylowData_e7ASZ (K := K) h4).conj
    (e7WeylRep K ((coxeterSystem .E7).wordProd e7WordZ))
  rwa [← e7FrameElt_one, e7FrameElt_conj_e7WordZ_syl, e7FrameElt_one,
    map_conj_e7FrameLine_of e7FrameElt_conj_e7WordZ_syl] at h

theorem centreData_e7FrameZ [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    Exc.CentreData (e7FramePt K e7FrameZ) (e7FrameLine K e7FrameZ) := by
  obtain ⟨hne, hnd, hF, ho⟩ := e7FrameZ_facts
  exact centreData_e7FrameLine hne hnd hF ho commute_e7FrameLine_Z
    (sylowData_e7FrameZ h4)

theorem regular_e7FrameZ [Finite K] [CharP K 2] :
    ∃ u, Exc.Regular (e7FrameLine K e7FrameZ) u := by
  obtain ⟨hne, hnd, hF, ho⟩ := e7FrameZ_facts
  exact regular_e7FrameLine hne hnd hF ho commute_e7FrameLine_Z

end Certs

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
