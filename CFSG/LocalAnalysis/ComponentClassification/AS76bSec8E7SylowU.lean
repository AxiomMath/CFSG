module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7SylowCert
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7SylowChecks
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7CentU
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcJ
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Classes

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction


variable {K : Type} [Field K]

theorem e7FrameU_facts : e7FrameU ≠ [] ∧ e7FrameU.Nodup ∧
    (∀ σ ∈ e7FrameU, IsRoot .E7 σ ∧ 0 < height σ) ∧
      e7FrameU.Pairwise fun σ σ' => iform σ σ' = 0 := by
  obtain ⟨h1, h2, h3⟩ := e7Frames_facts e7FrameU (by simp)
  exact ⟨h1, h2, fun σ hσ => ⟨(isRoot_of_mem_e7Frames σ (by simp_all)).1,
    (isRoot_of_mem_e7Frames σ (by simp_all)).2.2⟩, h3⟩

section Certs


theorem sylowData_e7_uAS [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    Exc.SylowData (e7FramePt K oddDerivE7UFrame) (e7FrameLine K oddDerivE7UFrame) :=
  sylowData_of_e7SylowCheck h4
    (fun σ hσ => E7Pilot.pos_of_mem_uPsi (by rw [E7Pilot.uPsi, E7Pilot.uFrame]; simp_all))
    (by decide +kernel) oddDerivE7UFrame_orth e7SylowCheck_u

theorem sylowData_e7FrameU [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    Exc.SylowData (e7FramePt K e7FrameU) (e7FrameLine K e7FrameU) := by
  have h := Exc.SylowData.conj (sylowData_e7_uAS (K := K) h4)
    (e7WeylRep K ((coxeterSystem .E7).wordProd e7WordU))
  rwa [← e7FrameElt_one, e7FrameElt_conj_wordU, e7FrameElt_one,
    map_conj_e7FrameLine_of e7FrameElt_conj_wordU] at h

theorem centreData_e7FrameU [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    Exc.CentreData (e7FramePt K e7FrameU) (e7FrameLine K e7FrameU) := by
  obtain ⟨hne, hnd, hF, ho⟩ := e7FrameU_facts
  exact centreData_e7FrameLine hne hnd hF ho commute_e7FrameLine_U (sylowData_e7FrameU h4)

theorem regular_e7FrameU [Finite K] [CharP K 2] :
    ∃ u, Exc.Regular (e7FrameLine K e7FrameU) u := by
  obtain ⟨hne, hnd, hF, ho⟩ := e7FrameU_facts
  exact regular_e7FrameLine hne hnd hF ho commute_e7FrameLine_U

end Certs

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
