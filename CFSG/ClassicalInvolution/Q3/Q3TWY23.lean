module

public import CFSG.ClassicalInvolution.Q3.Q3EPQuot
public import CFSG.ClassicalInvolution.RouteD.GapsFrFive
public import CFSG.ClassicalInvolution.Q3.Q3WADict
public import CFSG.ClassicalInvolution.Q3.Q3WMain

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Generic (Commutes)

set_option linter.unusedSectionVars false

local notation "𝔽₃" => GaloisField 3 1


section Twin

variable {V : Type} [AddCommGroup V] [Module 𝔽₃ V] [FiniteDimensional 𝔽₃ V]
  {Q : QuadraticForm 𝔽₃ V}

theorem chain_twin_five3 (hfr : Module.finrank 𝔽₃ V = 11) {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot3 (spinAction Q) 𝓕 (fundSet Q) (scalars 𝔽₃ V))
    {R0 R1 Rtw RM : Subgroup (spinGroup Q)} (hR0 : R0 ∈ 𝓕) (hR1 : R1 ∈ 𝓕) (hRtw : Rtw ∈ 𝓕)
    (hRM : RM ∈ 𝓕) (hadj1 : ModelAdj (Subgroup.center _) R0 R1)
    (hadj2 : ModelAdj (Subgroup.center _) R0 Rtw) (hc12 : Commutes R1 Rtw)
    (hM0 : Commutes RM R0) (hM1 : Commutes RM R1) (hM2 : Commutes RM Rtw) :
    ∀ i j, IsFundamental Q (R1.map (spinAction Q)) i →
      IsFundamental Q (Rtw.map (spinAction Q)) j → i = j := by
  classical
  have hodd : Odd (Nat.card 𝔽₃) := odd_gf3
  have hdim : 9 ≤ Module.finrank 𝔽₃ V := by omega
  obtain ⟨i0, hi0⟩ := cq.map_mem _ hR0
  obtain ⟨i1, hi1⟩ := cq.map_mem _ hR1
  obtain ⟨i2, hi2⟩ := cq.map_mem _ hRtw
  obtain ⟨iM, hiM⟩ := cq.map_mem _ hRM
  intro i j hi hj
  have e1 : i1 = i := IsFundamental.involution_unique hodd hi1 hi
  have e2 : i2 = j := IsFundamental.involution_unique hodd hi2 hj
  rw [← e1, ← e2]
  by_contra hne
  have hadj1V := cq.modelAdj hR0 hR1 hadj1
  have hadj2V := cq.modelAdj hR0 hRtw hadj2
  have c12 : Commutes (R1.map (spinAction Q)) (Rtw.map (spinAction Q)) :=
    (cq.commutes_iff hR1).mpr hc12
  have cM0 : Commutes (RM.map (spinAction Q)) (R0.map (spinAction Q)) :=
    (cq.commutes_iff hRM).mpr hM0
  have cM1 : Commutes (R1.map (spinAction Q)) (RM.map (spinAction Q)) :=
    (cq.commutes_iff hR1).mpr (commutes_symm hM1)
  have cM2 : Commutes (Rtw.map (spinAction Q)) (RM.map (spinAction Q)) :=
    (cq.commutes_iff hRtw).mpr (commutes_symm hM2)
  have o12 : ∀ x ∈ negSpace i1, ∀ y ∈ negSpace i2, polar Q x y = 0 := by
    rcases orth_or_twin hodd hi1 hi2 c12 with h | h
    · exact h
    · exact absurd h.symm hne
  have oM : ∀ {L : Subgroup (V ≃ₗ[𝔽₃] V)} {il : V ≃ₗ[𝔽₃] V}, IsFundamental Q L il →
      ModelAdj (scalars 𝔽₃ V) (R0.map (spinAction Q)) L →
      Commutes L (RM.map (spinAction Q)) →
      ∀ x ∈ negSpace il, ∀ y ∈ negSpace iM, polar Q x y = 0 := by
    intro L il hl hadj hcomm
    rcases orth_or_twin hodd hl hiM hcomm with h | h
    · exact h
    · exfalso
      obtain ⟨-, -, C⟩ := adj_data hodd hdim hi0 hl hadj
      apply C
      rw [← h]
      exact Subgroup.mem_centralizer_iff.mpr fun g hg => (cM0 iM hiM.mem g hg).symm
  exact not_three_orth_fours (Q := Q) (U₁ := negSpace i1) (U₂ := negSpace i2)
    (U₃ := negSpace iM) (by omega) (finrank_negSpace hodd hi1) (finrank_negSpace hodd hi2)
    (finrank_negSpace hodd hiM) (polarNondegOn_negSpace hodd hi1)
    (polarNondegOn_negSpace hodd hiM) o12 (oM hi1 hadj1V cM1) (oM hi2 hadj2V cM2)

end Twin

end CFSG.ClassicalInvolution.Q3.Q3TWY
