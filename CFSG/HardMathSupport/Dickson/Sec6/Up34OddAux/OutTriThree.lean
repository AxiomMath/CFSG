module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutTri
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutTriAux.ThreeD4

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.ComponentClassification.CatLeaf
  CFSG.RankThree.PartOne.Sec66T
open CFSG.LieType.Chevalley (graphFixedRootGroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Dickson.Sec6.I923

set_option linter.unusedSectionVars false

section TriD4Three


theorem noL34OuterAt3_triD4 : NoL34OuterAtThree FamTriD4 := by
  intro P _ _ t n f hadm ht hF hm ψ hψ3 hninn
  obtain rfl := hF
  have hexc : ChevalleyExceptionalModel P .trialityD4 3 f := by
    rcases hm with ⟨hcl, -⟩ | ⟨-, -, hexc⟩ | ⟨-, hree, -⟩ | ⟨-, h, -⟩
    · exact absurd hcl (by decide)
    · exact hexc
    · exact absurd hree (by decide)
    · exact absurd h (by decide)
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := OutTri.exists_graphFixed_of_exceptionalModel hexc
  obtain ⟨-, hf, -⟩ := hadm
  haveI := TriD4Aux.finite_graphFixedRootGroup_D4 σ
  refine noL34Layer_congr e ?_
  have hφ3 : (MulAut.congr e ψ) ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hφ : MulAut.congr e ψ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
    rintro ⟨c, hc⟩
    apply hninn
    refine ⟨e.symm c, (MulAut.congr e).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
    exact hc
  haveI : CharP K 3 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_three (by omega) (by rw [hK, ← pow_mul, mul_comm] : Nat.card K = 3 ^ (3 * f))
  exact OutTri.noL34Layer_three_D4_outer_three hf hK σ hσ _ hφ3 hφ

theorem noL34OuterAt3_d4_of_order (hO : LieOrderFormulasInput) : NoL34OuterAtThree FamD4 := by
  intro P _ _ t n f hadm ht hF hm ψ hψ3 hninn
  obtain ⟨rfl, rfl⟩ := hF
  have hC : StatedClassicalModel P .POmegaPlus 4 3 f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hC
  obtain ⟨e'⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup K
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  let E : P ≃* adjointGroup Tag.D4 K := e.trans e'
  haveI := D4Aux.finite_adjointD4 K
  refine noL34Layer_congr E ?_
  have hα3 : MulAut.congr E ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hα : MulAut.congr E ψ ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.D4 K) := by
    rintro ⟨c, hc⟩
    apply hninn
    refine ⟨E.symm c, (MulAut.congr E).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
    exact hc
  exact OutTri.noL34Layer_adjointD4_outer_three hO hf K hK _ hα3 hα

end TriD4Three

section D4Three


theorem noL34OuterAt3_d4 : NoL34OuterAtThree FamD4 :=
  noL34OuterAt3_d4_of_order CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput

end D4Three

end CFSG.HardMathSupport.Dickson.Sec6
