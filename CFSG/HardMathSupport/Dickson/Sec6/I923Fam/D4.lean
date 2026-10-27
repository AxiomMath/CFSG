module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.D4Aux.Normal
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.ComponentClassification.CatLeaf
  CFSG.RankThree.PartOne.Sec66T

set_option linter.unusedSectionVars false

section Final


theorem noL2OuterAt_d4 (hO : LieOrderFormulasInput) (hA2 : TriD4Aux.TriD4A2NoL2)
    (hC3 : TriD4Aux.TriD4C3NoL2) : NoL2OuterAt FamD4 := by
  intro P _ _ t n p f hadm ht hF hm ψ hψ3 hninn
  obtain ⟨rfl, rfl⟩ := hF
  have hC : StatedClassicalModel P .POmegaPlus 4 p f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hC
  obtain ⟨e'⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup K
  haveI : Fact p.Prime := ⟨hp⟩
  let E : P ≃* adjointGroup Tag.D4 K := e.trans e'
  haveI := D4Aux.finite_adjointD4 K
  refine OrthAux.noL2Layer_of_congr E ?_
  have hα3 : MulAut.congr E ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hα : MulAut.congr E ψ ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.D4 K) := by
    rintro ⟨c, hc⟩
    apply hninn
    refine ⟨E.symm c, (MulAut.congr E).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
    exact hc
  exact D4Aux.noL2Layer_adjointD4_outer hO hA2 hC3 hf K hK _ hα3 hα

end Final

section Residual


theorem y923_d4_of_residuals (hA2 : TriD4Aux.TriD4A2NoL2) (hC3 : TriD4Aux.TriD4C3NoL2) :
    Y923_D4 :=
  y923_lieRestAt_of_noL2Outer
    (noL2OuterAt_d4 CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hA2 hC3)

end Residual

end CFSG.HardMathSupport.Dickson.Sec6.I923
