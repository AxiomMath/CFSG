module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexModelParameter
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Models
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairLinear
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairSuzuki
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84TorusModels

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII

universe u

theorem simpleBender_borel_exact_parameter_at_exponent
    {G : Type u} [Group G] [Finite G] (f : ℕ) (hf : 2 ≤ f)
    (hmodel : IsSimpleBenderGroupAtExponent f G) :
    ∃ i : ℕ, i ∈ ({1, 2, 3} : Set ℕ) ∧
      ∀ B : Subgroup G, IsBorelSubgroup B →
        B.index = (2 ^ f) ^ i + 1 ∧
          Nat.card {x : G // x ∈ B ∧ IsInvolution x} = 2 ^ f - 1 := by
  rcases hmodel with ⟨⟨e⟩⟩ | ⟨⟨m, hfm, ⟨e⟩⟩⟩ |
    ⟨⟨K, hfield, hfinite, J, hJ, hKcard, hfixed, ⟨e⟩⟩⟩
  · let K := BinaryGaloisField f
    let F := Matrix.ProjGenLinGroup (Fin 2) K
    let : Finite F := Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
    obtain ⟨ePGL⟩ := psl_charTwo_equiv_pgl f (by omega)
    refine ⟨1, by simp, ?_⟩
    intro B hB
    exact borel_index_and_whole_involution_card_map_mulEquiv (e.trans ePGL) (2 ^ f) 1
      (fun C hC => linear_borel_index_and_whole_involution_parameter f hf C hC) B hB
  · have hm : 1 ≤ m := by omega
    refine ⟨2, by simp, ?_⟩
    intro B hB
    rw [hfm]
    exact borel_index_and_whole_involution_card_map_mulEquiv e (2 ^ (2 * m + 1)) 2
      (fun C hC => suzuki_borel_index_and_whole_involution_parameter m hm C hC) B hB
  · let := hfield
    let := hfinite
    let : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
      Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_injective
      (fun x : ProjectiveSpecialUnitaryMatrixGroup J =>
        (x : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
    refine ⟨3, by simp, ?_⟩
    intro B hB
    exact borel_index_and_whole_involution_card_map_mulEquiv e (2 ^ f) 3
      (fun C hC => unitary_borel_index_and_whole_involution_parameter
        J f hf hKcard hfixed hJ C hC) B hB

theorem simpleBender_borel_exact_whole_parameter
    {G : Type u} [Group G] [Finite G] (hmodel : IsSimpleBenderGroup G) :
    ∃ f i : ℕ, 2 ≤ f ∧ i ∈ ({1, 2, 3} : Set ℕ) ∧
      ∀ B : Subgroup G, IsBorelSubgroup B →
        B.index = (2 ^ f) ^ i + 1 ∧
          Nat.card {x : G // x ∈ B ∧ IsInvolution x} = 2 ^ f - 1 := by
  obtain ⟨f, hf, hmodel⟩ := hmodel.exists_exponent
  obtain ⟨i, hi, hB⟩ := simpleBender_borel_exact_parameter_at_exponent f hf hmodel
  exact ⟨f, i, hf, hi, hB⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
