module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.Assembly
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALayer

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding TauCeti
open CFSG.RankThree.PartTwo.Sec4.E27 (Seitz27 seitz27_trialityD4_final_layer)

theorem hyperGen_of_seitz27 {Y : Type} [Group Y] {K : Subgroup Y} [K.Normal]
    (hC : Subgroup.centralizer (K : Set Y) = ⊥) {E : Subgroup Y} (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) (hK : Seitz27 K) : HyperGen 3 K E := by
  have hc : Nat.card (actionImage K E) = 27 :=
    calc Nat.card (actionImage K E) = Nat.card E :=
          Subgroup.card_map_of_injective (conjNormal_injective hC)
      _ = 27 := by rw [hEc]; norm_num
  exact hyperGen_of_seitzHyperGamma 3 K E
    (hK (actionImage K E) (hE.map (MulAut.conjNormal : Y →* MulAut K)) hc)

@[expose] def TrialityOuterCubesThreeOdd : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid), q.p ≠ 2 →
    KFactSeitzOuterCubeRankTwoAtPrime ⟨.trialityD4 q, hv⟩ 3

section Even


theorem trialityOuterCubesThree_even (q : PrimePower)
    (hv : (LieTypeIndex.trialityD4 q).Valid) (hq : q.p = 2) :
    KFactSeitzOuterCubeRankTwoAtPrime ⟨.trialityD4 q, hv⟩ 3 := by
  intro _ Y _ _ K hKn hC he _ hl _ E hE hEc
  obtain ⟨e⟩ := he
  have : K.Normal := hKn
  by_cases h1 : q.exponent = 1
  ·
    exfalso
    refine hl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, q, hq, h1, ?_⟩)))))
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  · have h2 : 2 ≤ q.exponent := by
      have := q.exponent_pos
      omega
    exact hyperGen_of_seitz27 hC hE hEc (seitz27_trialityD4_final_layer q hv hq h2 K ⟨e⟩)

theorem trialityOuterCubesThree_of_odd (hOdd : TrialityOuterCubesThreeOdd) :
    TrialityOuterCubesThree := fun q hv => by
  by_cases hq : q.p = 2
  · exact trialityOuterCubesThree_even q hv hq
  · exact hOdd q hv hq

section FromAnisotropic


theorem kFactSeitzOuterCubeRankTwoExcRest_of_anisotropic_odd (hAni : SeitzExcAnisotropic)
    (hOdd : TrialityOuterCubesThreeOdd) : KFactSeitzOuterCubeRankTwoExcRest :=
  kFactSeitzOuterCubeRankTwoExcRest_of_anisotropic hAni (trialityOuterCubesThree_of_odd hOdd)

end FromAnisotropic

end Even

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
