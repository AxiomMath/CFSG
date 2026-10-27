module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Dispatch
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FamiliesSmall
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FamiliesTw

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 TauCeti

@[expose] def TrialityOuterCubesThree : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid),
    KFactSeitzOuterCubeRankTwoAtPrime ⟨.trialityD4 q, hv⟩ 3

theorem kFactSeitzOuterCubeRankTwoAt_of_pair {d : ValidLieTypeIndex}
    (h : ∀ (p : ℕ) [Fact p.Prime], ExcOuterPair d p) : KFactSeitzOuterCubeRankTwoAt d :=
  kFactSeitzOuterCubeRankTwoAt_of_atPrime fun p _ =>
    kFactSeitzOuterCubeRankTwoAtPrime_of_fieldAutData (h p)

section Families


theorem kFactSeitzOuterCubeRankTwoAt_G2 (hLow : ExcInnerLowPlanes) {q : PrimePower}
    (hv : (LieTypeIndex.G2 q).Valid) : KFactSeitzOuterCubeRankTwoAt ⟨.G2 q, hv⟩ :=
  kFactSeitzOuterCubeRankTwoAt_of_pair fun p _ => excOuterPair_G2 hLow hv p

theorem kFactSeitzOuterCubeRankTwoAt_F4 (hLow : ExcInnerLowPlanes) {q : PrimePower}
    (hv : (LieTypeIndex.F4 q).Valid) : KFactSeitzOuterCubeRankTwoAt ⟨.F4 q, hv⟩ :=
  kFactSeitzOuterCubeRankTwoAt_of_pair fun p _ => excOuterPair_F4 hLow hv p

theorem kFactSeitzOuterCubeRankTwoAt_E6 (hLow : ExcInnerLowPlanes) {q : PrimePower}
    (hv : (LieTypeIndex.E6 q).Valid) : KFactSeitzOuterCubeRankTwoAt ⟨.E6 q, hv⟩ :=
  kFactSeitzOuterCubeRankTwoAt_of_pair fun p _ => excOuterPair_E6 hLow hv p

theorem kFactSeitzOuterCubeRankTwoAt_E7 (hLow : ExcInnerLowPlanes) {q : PrimePower}
    (hv : (LieTypeIndex.E7 q).Valid) : KFactSeitzOuterCubeRankTwoAt ⟨.E7 q, hv⟩ :=
  kFactSeitzOuterCubeRankTwoAt_of_pair fun p _ => excOuterPair_E7 hLow hv p

theorem kFactSeitzOuterCubeRankTwoAt_E8 (hLow : ExcInnerLowPlanes) {q : PrimePower}
    (hv : (LieTypeIndex.E8 q).Valid) : KFactSeitzOuterCubeRankTwoAt ⟨.E8 q, hv⟩ :=
  kFactSeitzOuterCubeRankTwoAt_of_pair fun p _ => excOuterPair_E8 hLow hv p

theorem kFactSeitzOuterCubeRankTwoAt_twistedE6 (hLow : ExcInnerLowPlanes) {q : PrimePower}
    (hv : (LieTypeIndex.twistedE6 q).Valid) :
    KFactSeitzOuterCubeRankTwoAt ⟨.twistedE6 q, hv⟩ :=
  kFactSeitzOuterCubeRankTwoAt_of_pair fun p _ => excOuterPair_twE6 hLow hv p

theorem kFactSeitzOuterCubeRankTwoAt_reeF4 (hLow : ExcInnerLowPlanes) {m : ℕ}
    (hv : (LieTypeIndex.reeF4 m).Valid) : KFactSeitzOuterCubeRankTwoAt ⟨.reeF4 m, hv⟩ :=
  kFactSeitzOuterCubeRankTwoAt_of_pair fun p _ => excOuterPair_reeF4 hLow hv p

theorem kFactSeitzOuterCubeRankTwoAt_trialityD4 (hLow : ExcInnerLowPlanes)
    (hTri : TrialityOuterCubesThree) {q : PrimePower}
    (hv : (LieTypeIndex.trialityD4 q).Valid) : KFactSeitzOuterCubeRankTwoAt ⟨.trialityD4 q, hv⟩ :=
  kFactSeitzOuterCubeRankTwoAt_of_atPrime fun p _ => by
    by_cases hp3 : p = 3
    · subst hp3
      exact hTri q hv
    · exact kFactSeitzOuterCubeRankTwoAtPrime_of_fieldAutData
        (excOuterPair_trialityD4_five hLow hv p hp3)

theorem kFactSeitzOuterCubeRankTwoExcRest_of_inputs (hLow : ExcInnerLowPlanes)
    (hTri : TrialityOuterCubesThree) : KFactSeitzOuterCubeRankTwoExcRest := by
  intro d hnc hs hr ht
  obtain ⟨d, hv⟩ := d
  rcases (not_isClassicalIndex_iff d).mp hnc with
    ((hd | hd | hd | hd | hd) | (hd | hd)) | (hd | hd | hd | hd)
  · obtain ⟨q, rfl⟩ := hd
    exact kFactSeitzOuterCubeRankTwoAt_G2 hLow hv
  · obtain ⟨q, rfl⟩ := hd
    exact kFactSeitzOuterCubeRankTwoAt_F4 hLow hv
  · obtain ⟨q, rfl⟩ := hd
    exact kFactSeitzOuterCubeRankTwoAt_E6 hLow hv
  · obtain ⟨q, rfl⟩ := hd
    exact kFactSeitzOuterCubeRankTwoAt_E7 hLow hv
  · obtain ⟨q, rfl⟩ := hd
    exact kFactSeitzOuterCubeRankTwoAt_E8 hLow hv
  · obtain ⟨q, rfl⟩ := hd
    exact kFactSeitzOuterCubeRankTwoAt_trialityD4 hLow hTri hv
  · obtain ⟨q, rfl⟩ := hd
    exact kFactSeitzOuterCubeRankTwoAt_twistedE6 hLow hv
  · obtain ⟨m, rfl⟩ := hd
    exact (hs m rfl).elim
  · obtain ⟨m, rfl⟩ := hd
    exact (hr m rfl).elim
  · obtain ⟨m, rfl⟩ := hd
    exact kFactSeitzOuterCubeRankTwoAt_reeF4 hLow hv
  · subst hd
    exact (ht rfl).elim

end Families

section FromAnisotropic


theorem kFactSeitzOuterCubeRankTwoExcRest_of_anisotropic (hAni : SeitzExcAnisotropic)
    (hTri : TrialityOuterCubesThree) : KFactSeitzOuterCubeRankTwoExcRest :=
  kFactSeitzOuterCubeRankTwoExcRest_of_inputs (excInnerLowPlanes_of_anisotropic hAni) hTri

end FromAnisotropic

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
