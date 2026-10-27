module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7SylowCert
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7SylowChecks
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7CentV
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcJ
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Classes

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction


variable {K : Type} [Field K]

theorem e7FrameV_facts : e7FrameV ≠ [] ∧ e7FrameV.Nodup ∧
    (∀ σ ∈ e7FrameV, IsRoot .E7 σ ∧ 0 < height σ) ∧
      e7FrameV.Pairwise fun σ σ' => iform σ σ' = 0 := by
  obtain ⟨h1, h2, h3⟩ := e7Frames_facts e7FrameV (by simp)
  exact ⟨h1, h2, fun σ hσ => ⟨(isRoot_of_mem_e7Frames σ (by simp_all)).1,
    (isRoot_of_mem_e7Frames σ (by simp_all)).2.2⟩, h3⟩

section Certs


theorem sylowData_e7_vAS [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    Exc.SylowData (e7FramePt K oddDerivE7VFrame) (e7FrameLine K oddDerivE7VFrame) :=
  sylowData_of_e7SylowCheck h4
    (fun σ hσ => E7Pilot.pos_of_mem_vPsi (by rw [E7Pilot.vPsi, E7Pilot.vFrame]; simp_all))
    (by decide +kernel) oddDerivE7VFrame_orth e7SylowCheck_v

theorem sylowData_e7FrameV [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    Exc.SylowData (e7FramePt K e7FrameV) (e7FrameLine K e7FrameV) := by
  have h := Exc.SylowData.conj (sylowData_e7_vAS (K := K) h4)
    (e7WeylRep K ((coxeterSystem .E7).wordProd e7WordV))
  rwa [← e7FrameElt_one, e7FrameElt_conj_wordV, e7FrameElt_one,
    map_conj_e7FrameLine_of e7FrameElt_conj_wordV] at h

theorem centreData_e7FrameV [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    Exc.CentreData (e7FramePt K e7FrameV) (e7FrameLine K e7FrameV) := by
  obtain ⟨hne, hnd, hF, ho⟩ := e7FrameV_facts
  exact centreData_e7FrameLine hne hnd hF ho commute_e7FrameLine_V (sylowData_e7FrameV h4)

theorem regular_e7FrameV [Finite K] [CharP K 2] :
    ∃ u, Exc.Regular (e7FrameLine K e7FrameV) u := by
  obtain ⟨hne, hnd, hF, ho⟩ := e7FrameV_facts
  exact regular_e7FrameLine hne hnd hF ho commute_e7FrameLine_V

end Certs

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
