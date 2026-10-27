module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.ExcCommon
public import CFSG.HardMathSupport.Lang.E6Descent.OuterDescentE
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Lang.E6Descent

section


theorem noL2OuterAt_e8 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    NoL2OuterAt FamE8 := by
  intro P _ _ t n p f hadm ht hF hm ψ hψ3 hψ
  obtain rfl := hF
  haveI : Fact p.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .E8 (p ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∉ inner ↥(adjointGroup Tag.E8 F) := fun hin =>
    hψ ((congr_mem_inner_iff_of_equiv θ ψ).mp hin)
  have hdet : ¬ 3 ∣ Tag.E8.cartan.det.natAbs := by
    rw [det_cartan_E8]
    decide
  obtain ⟨d, T, r, j, δ, hfd, hTo, hTc, hrj, hδ⟩ :=
    exists_conj_entrywise_of_outer_E Tag.E8 (Or.inr (Or.inr rfl)) hf F hFcard Nat.prime_three
      (by norm_num) hdet _ hβ3 hβinn
  refine noL2Layer_congr θ (noL2Layer_of_conj_pow hrj hδ ?_)
  have hd : 1 ≤ d := by omega
  haveI : Finite ↥(fixSubfield T) := Subtype.finite
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E8 ↥(fixSubfield T)) .E8 p d :=
    ⟨⟨hadm.1, hd, rfl⟩, untwisted_adjointGroup hTc⟩
  obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_e8_simplicity _ p d hM
  have hZ : Subgroup.center ↥(adjointGroup Tag.E8 ↥(fixSubfield T)) = ⊥ :=
    center_adjointGroup_eq_bot
  exact noL2Layer_entrywise_of_model hO ht (by decide) T (Or.inr (Or.inl ⟨rfl, by decide, hM⟩))
    hsimp (exists_noncomm_of_center_bot hZ) hZ

theorem y923_e8_holds :
    Y923_E8 :=
  y923_lieRestAt_of_noL2Outer
    (noL2OuterAt_e8 CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput)

end

end CFSG.HardMathSupport.Dickson.Sec6.I923
