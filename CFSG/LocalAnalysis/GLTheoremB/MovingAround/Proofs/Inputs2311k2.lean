module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311k

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311k

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph CFSG.HardMathSupport.Lang.D4Three
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c

@[expose] def D4GraphG2Plane
    (d : TauCeti.ValidLieTypeIndex) (p : ℕ) (E : Subgroup (MulAut (Cat d))) : Prop :=
  p = 3 ∧ d.1.characteristic ≠ 2 ∧ ∃ q : TauCeti.PrimePower, d.1 = .D 4 q ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.card ∧
      ∃ e : Cat d ≃* ↥(adjointGroup Tag.D4 K), d4Graph K 1 ∈ E.map (MulAut.congr e).toMonoidHom ∧
        ∃ x : ↥(adjointGroup Tag.D4 K), x ≠ 1 ∧ MulAut.conj x ∈ E.map (MulAut.congr e).toMonoidHom

@[expose] def D4PlanesRest :
    Prop :=
  UniSeitzPlanes fun d p E => Inputs2311g.OddCpfRest4 d p E ∧ ¬ InnerPlane d p E ∧
    ¬ D4GraphG2Plane d p E

section Assembly

set_option linter.unusedSectionVars false


theorem uniSeitzPlanes_oddCpfRest4_triality_inner :
    UniSeitzPlanes fun d p E => Inputs2311g.OddCpfRest4 d p E ∧ InnerPlane d p E ∧ IsTrialityIndex d.1 := by
  intro d p hp hp2 hpd hex E hE hc ⟨⟨hR, hcase⟩, hin, ⟨q, hq⟩⟩
  rcases hcase with hb | ⟨-, hexc, hsub⟩ | htri
  · exact absurd hin hb.1
  · have hnR : ¬ NormalizesRSubgroup d E := fun hN => hR.2.2 ⟨hin, hexc, hN⟩
    rcases hsub with ⟨h5, hcls⟩ | ⟨hp3, ht | htw⟩
    · rcases hcls with ⟨q', hq', -⟩ | ⟨q', hq', -⟩ | ⟨q', hq', -⟩ | ⟨q', hq', -⟩ | ⟨q', hq', h36⟩
      · rw [hq] at hq'
        cases hq'
      · rw [hq] at hq'
        cases hq'
      · rw [hq] at hq'
        cases hq'
      · rw [hq] at hq'
        cases hq'
      · exact uniSeitzPlanes_triality_inner_phi36 d p hp hp2 hpd hex E hE hc ⟨hin, h5, q', hq', h36⟩
    · exact uniSeitzPlanes_triality_inner_three d p hp hp2 hpd hex E hE hc
        ⟨hin, hp3, hR.1.1, hnR, ht⟩
    · obtain ⟨q', hq', -⟩ := htw
      rw [hq] at hq'
      cases hq'
  · exact absurd hin htri.1

theorem uniSeitzPlanes_twoRest4_triality :
    UniSeitzPlanes fun d p E => d.1.characteristic = 2 ∧ 5 ≤ p ∧ CentralPrimeFree p d.1 ∧
      InnerPlane d p E ∧ ¬ NormalizesRSubgroup d E ∧ ∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q ∧
        (p ∣ q.card ^ 2 + q.card + 1 ∨ p ∣ q.card ^ 2 - q.card + 1) :=
  UniSeitzPlanes.mono (fun _ _ _ h => ⟨h.2.2.2.1, h.2.1, h.2.2.2.2.2⟩) uniSeitzPlanes_triality_inner_phi36

theorem uniSeitzPlanes_oddCpfRest4_graphG2 :
    UniSeitzPlanes fun d p E => Inputs2311g.OddCpfRest4 d p E ∧ D4GraphG2Plane d p E :=
  UniSeitzPlanes.mono (fun _ _ _ h => h.2) uniSeitzPlanes_dFour_graphG2Type

theorem uniSeitzPlanes_oddCpfRest4_d4Families_of_rest (h : D4PlanesRest) :
    UniSeitzPlanes fun d p E => Inputs2311g.OddCpfRest4 d p E ∧ (¬ InnerPlane d p E ∨ IsTrialityIndex d.1) := by
  intro d p hp hp2 hpd hex E hE hc ⟨hR, hcase⟩
  by_cases hin : InnerPlane d p E
  · rcases hcase with hout | htri
    · exact absurd hin hout
    · exact uniSeitzPlanes_oddCpfRest4_triality_inner d p hp hp2 hpd hex E hE hc ⟨hR, hin, htri⟩
  · by_cases hg : D4GraphG2Plane d p E
    · exact uniSeitzPlanes_oddCpfRest4_graphG2 d p hp hp2 hpd hex E hE hc ⟨hR, hg⟩
    · exact h d p hp hp2 hpd hex E hE hc ⟨hR, hin, hg⟩

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311k
