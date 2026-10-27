module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCFinal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172B

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.GroupTheory.WeirSylow CFSG.LieType.Universal.Spin
  CFSG.RankThree.Classical2

open CFSG.Adapters.RankTwoModelTransports (glCongr statedProjCongr glCongr_statedScalars) in
noncomputable def statedProjOmegaPlusEquivOrthDerived (n : ℕ) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    StatedProj (StatedOmega (StatedQuadPlus n K)) ≃* ↥(orthDerived (quadPlus n (ZMod 2))) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  let σ : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hK').symm
  have hZ2 : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  let e1 : StatedProj (StatedOmega (StatedQuadPlus n K)) ≃*
      StatedProj (StatedOmega (StatedQuadPlus n (ZMod 2))) :=
    statedProjCongr (glCongr σ)
      (CFSG.ClassicalInvolution.Upgrade.map_statedOmega σ
        (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp σ))
      (glCongr_statedScalars σ)
  let e2 := (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.omStatedProjEquivOfCardTwo hZ2
    (StatedOmega (StatedQuadPlus n (ZMod 2)))).symm
  let e3 := CFSG.ComponentClassification.RankTwoClassical.statedOmegaEquivCommutator
    (quadPlus n (ZMod 2)) (coe_quadPlus n (ZMod 2))
  exact (e1.trans e2).trans e3

theorem exists_omegaPlusTwo_model {n : ℕ} (hn : 4 ≤ n) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V) (_ : FiniteDimensional (ZMod 2) V)
      (Q : QuadraticForm (ZMod 2) V), (QuadraticMap.polarBilin Q).Nondegenerate ∧
        Module.finrank (ZMod 2) V = 2 * n ∧ CFSG.GroupTheory.WeirSylow.IsPlusType Q ∧
        ∀ (X : Type) [Group X], catalogIs X (isOmPA n 2) →
          Nonempty (X ≃* ↥(CFSG.RankThree.Classical2.orthDerived Q)) := by
  refine ⟨Fin n ⊕ Fin n → ZMod 2, inferInstance, inferInstance, inferInstance,
    quadPlus n (ZMod 2), nondegenerate_polarBilin_quadPlus n (ZMod 2), finrank_quadPlus_space n,
    isPlusType_quadPlus (ZMod 2) n, ?_⟩
  intro X _ ⟨i, hi, ⟨e⟩⟩
  rcases hi with hi | ⟨h3, -⟩
  · cases i with
    | lie j =>
      obtain ⟨x, hv⟩ := j
      cases x
      case D r q =>
        obtain ⟨rfl, hq⟩ := hi
        obtain ⟨hp2, hf1⟩ :=
          CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.primePower_card_two' hq
        have hMod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hp2 e
        obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨φ⟩⟩ := hMod
        have hK2 : Nat.card K = 2 := by
          rw [hKcard, hp2, hf1]
          norm_num
        exact ⟨φ.trans (statedProjOmegaPlusEquivOrthDerived r hK2)⟩
      all_goals exact hi.elim
    | _ => exact hi.elim
  · omega

end CFSG.LocalAnalysis.GLTheoremA.S172B

end
