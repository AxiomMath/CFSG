module

public import CFSG.ClassicalInvolution.Q3.Q3MFOSAut

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFO

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Balance
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.ClassicalInvolution.Generic

section Transport

variable {A B : Type} [Group A] [Group B]

theorem fixedOddFree_of_mulEquiv (e : A ≃* B) (h : FixedOddFree B) : FixedOddFree A := by
  intro ρ hρ
  have hρ' : MulAut.congr e ρ * MulAut.congr e ρ = 1 := by
    rw [← map_mul, hρ, map_one]
  have h1 := oddCoreIn_fixed_congr_eq_bot' e.symm (MulAut.congr e ρ) (h _ hρ')
  have h2 : MulAut.congr e.symm (MulAut.congr e ρ) = ρ := by
    ext x
    simp [MulAut.congr_apply]
  rwa [h2] at h1

end Transport


theorem fixedOddFree_pOmegaOdd {n : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n 3 1) :
    FixedOddFree ((CompData.model .POmegaOdd n).G ⧸
      Subgroup.center (CompData.model .POmegaOdd n).G) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hn : 3 ≤ n := hadm.2.2.1
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hF : Nat.card (GaloisField 3 1) = 3 := by simpa using GaloisField.card 3 1 one_ne_zero
  have h2 : (2 : GaloisField 3 1) ≠ 0 := (three_eq_zero_two_ne_zero_of_card_eq_three hF).2
  have hM : modelUniv .POmegaOdd n 3 1 hp = ⟨spinGroup (Spin.quadOdd n (GaloisField 3 1)),
      Spin.oddDatum n (GaloisField 3 1)⟩ := by
    simp only [modelUniv, lieUniversal]
  obtain ⟨eK⟩ : Nonempty ((modelUniv .POmegaOdd n 3 1 hp).K ≃*
      ↥(spinGroup (Spin.quadOdd n (GaloisField 3 1)))) := by
    rw [hM]
    exact ⟨MulEquiv.refl _⟩
  let e : (modelUniv .POmegaOdd n 3 1 hp).K ⧸ Subgroup.center (modelUniv .POmegaOdd n 3 1 hp).K ≃*
      StatedProj (StatedOmega (StatedQuadOdd n (GaloisField 3 1))) :=
    (QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)).trans
      (spinQuotientCenterEquivQuadOdd (K := GaloisField 3 1) (n := n) h2 hn)
  have hmodel : StatedClassicalModel ((modelUniv .POmegaOdd n 3 1 hp).K ⧸
      Subgroup.center (modelUniv .POmegaOdd n 3 1 hp).K) .POmegaOdd n 3 1 :=
    ⟨hadm, GaloisField 3 1, inferInstance, inferInstance, by rw [hF, pow_one], ⟨e⟩⟩
  obtain ⟨-, hQ, hT3, hE, -, -⟩ := coordinate_model_witness_odd hmodel (GaloisField 3 1)
    (by rw [hF, pow_one]) e
  have hdim : 3 ≤ 2 * n + 1 := by omega
  have himg : matrixProjectiveImage (coordinateQuadOdd n (GaloisField 3 1)) = ⊤ := by
    rw [← ((orthogonal_geometry_model_stabilizer_preserving_image _ .POmegaOdd (.inl rfl) n 3 1
      hmodel) (GaloisField 3 1) (by rw [hF, pow_one]) e).1]
    exact ((orthogonal_geometry_tail_model_point_family_invariant _ .POmegaOdd (.inl rfl) n 3 1
      hmodel) (GaloisField 3 1) (by rw [hF, pow_one])).2
  obtain ⟨T3, hT3r, hT3Q⟩ := hT3
  have hperf : Group.IsPerfect ↥(elementaryGroup (coordinateQuadOdd n (GaloisField 3 1))) :=
    Group.isPerfect_def.mpr (commutator_elementaryGroup_eq_top' hQ (T := T3) hT3r.ge hT3Q)
  let η : ((modelUniv .POmegaOdd n 3 1 hp).K ⧸ Subgroup.center (modelUniv .POmegaOdd n 3 1 hp).K) ≃*
      (↥(elementaryGroup (coordinateQuadOdd n (GaloisField 3 1))) ⧸
        Subgroup.center ↥(elementaryGroup (coordinateQuadOdd n (GaloisField 3 1)))) :=
    (coordinateOddWitnessEquiv (GaloisField 3 1) e).trans
      (centralEquiv (coordinateQuadOdd n (GaloisField 3 1)) hF hQ hdim hE)
  have hKq : CFSG.Open.IsQuasisimple (modelUniv .POmegaOdd n 3 1 hp).K :=
    (ModelFacts.modelClauseZero .POmegaOdd n 3 1 hp trivial hadm).1
  have hsimpleT : IsSimpleGroup ((modelUniv .POmegaOdd n 3 1 hp).K ⧸
      Subgroup.center (modelUniv .POmegaOdd n 3 1 hp).K) := hKq.2
  have := hsimpleT
  have hsimple : IsSimpleGroup (↥(elementaryGroup (coordinateQuadOdd n (GaloisField 3 1))) ⧸
      Subgroup.center ↥(elementaryGroup (coordinateQuadOdd n (GaloisField 3 1)))) :=
    η.symm.isSimpleGroup
  exact fixedOddFree_of_mulEquiv η (fixedOddFree_central_odd (coordinateQuadOdd n (GaloisField 3 1))
    hF hQ hdim ⟨n, rfl⟩ hE himg hperf hsimple)

end CFSG.ClassicalInvolution.Q3.Q3MFO
