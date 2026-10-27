module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5OmegaInv
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatDefs

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat

open CFSG Subgroup CFSG.Open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation
open CFSG.ComponentClassification.SolMax.FiveCat.C5Omega

namespace C5Omega

theorem false_of_orth_data {S : Type} [Group S] [Finite S] [IsSimpleGroup S] {K : Type}
    [Field K] [Finite K] {d f n : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 5 ^ f)
    (hdim : d = 2 * n + 1 ∧ 3 ≤ n ∨ d = 2 * n ∧ 4 ≤ n) (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate) (hrep : SemilinearRepresentation Q)
    (ψ : S ≃* matrixProjectiveDerived Q) (σ : MulAut S) (P : Subgroup S)
    (hP : ProperFixedComponent σ P)
    (eP : Nonempty (↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin 5)))
    (huniq : ∀ P' : Subgroup S, ProperFixedComponent σ P' → P' = P) : False := by
  have hσ1 : σ ≠ 1 := hP.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => hP.1 y
  have hα2 : MulAut.congr ψ σ * MulAut.congr ψ σ = 1 := by rw [← map_mul, hσσ, map_one]
  have hα1 : MulAut.congr ψ σ ≠ 1 := fun h =>
    hσ1 ((MulAut.congr ψ).injective (h.trans (map_one _).symm))
  have hqs : IsQuasisimple (P.subgroupOf (fixedSubgroup σ)) :=
    CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv 2
      (Sporadic.HeldB.fixedSubgroupCongr ψ σ)
      ((CatalogueBOrthogonalInvolutionFixedComponents.fixed_pComponent_quasisimple_of_representation
        5 f Nat.prime_five (by norm_num) hf hK (by omega) Q hQ hrep _ hα2 hα1) 2 Nat.prime_two)
      _ hP.2.2.1
  obtain ⟨hcomp, ⟨eZ⟩⟩ := hP.fusionZStar_equiv_of_quasisimple hqs
  have hA5 : Nonempty (↥(P.subgroupOf (fixedSubgroup σ)) ⧸
      center ↥(P.subgroupOf (fixedSubgroup σ)) ≃* alternatingGroup (Fin 5)) :=
    ⟨eZ.symm.trans eP.some⟩
  have hu : ∀ L' : Subgroup ↥(fixedSubgroup σ), IsComponent L' →
      L' = P.subgroupOf (fixedSubgroup σ) := by
    intro L' hL'
    have hLL : (L'.map (fixedSubgroup σ).subtype).subgroupOf (fixedSubgroup σ) = L' :=
      comap_map_eq_self_of_injective (subtype_injective _) L'
    have hP' : ProperFixedComponent σ (L'.map (fixedSubgroup σ).subtype) := by
      refine ⟨hP.1, map_subtype_le L', ?_, fun htop => hσ1 ?_⟩
      · rw [hLL]
        exact CatLeafProof.isPComponent_two_of_isComponent hL'
      · have hF : fixedSubgroup σ = ⊤ := top_le_iff.mp (htop ▸ map_subtype_le L')
        ext x
        have hx : x ∈ fixedSubgroup σ := hF ▸ mem_top x
        exact hx
    rw [← hLL, huniq _ hP']
  obtain ⟨L', hL', hne⟩ := NotOnlyA5.of_mulEquiv (Sporadic.HeldB.fixedSubgroupCongr ψ σ)
    (notOnlyA5_involution hf hK hdim Q hQ hrep _ hα2 hα1) _ hcomp hA5
  exact hne (hu L' hL')

end C5Omega

theorem fivePump_char5_POmegaOdd : FivePumpCharFiveClause .POmegaOdd := by
  intro S _ _ hs _hna ⟨n, f, hm⟩ σ P hP _hZ eP huniq
  exfalso
  have hadm : StatedLieAdmissible .POmegaOdd n 5 f := hm.admissible
  have hC : StatedClassicalModel S .POmegaOdd n 5 f := hm.statedClassicalModel (by decide)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hC
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaOdd (Or.inl rfl) hC K hK
    e
  obtain ⟨-, hQ, -⟩ := coordinate_model_witness_odd hC K hK e
  exact C5Omega.false_of_orth_data hadm.2.1 hK (Or.inl ⟨rfl, hadm.2.2.1⟩) (coordinateQuadOdd n K)
    hQ hrep (coordinateOddWitnessEquiv K e) σ P hP eP huniq

theorem fivePump_char5_POmegaPlus : FivePumpCharFiveClause .POmegaPlus := by
  intro S _ _ hs _hna ⟨n, f, hm⟩ σ P hP _hZ eP huniq
  exfalso
  have hadm : StatedLieAdmissible .POmegaPlus n 5 f := hm.admissible
  have hC : StatedClassicalModel S .POmegaPlus n 5 f := hm.statedClassicalModel (by decide)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hC
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaPlus
    (Or.inr (Or.inl rfl)) hC K hK e
  obtain ⟨-, hQ, -⟩ := coordinate_model_witness_plus hC K hK e
  exact C5Omega.false_of_orth_data hadm.2.1 hK (Or.inr ⟨rfl, hadm.2.2⟩) (coordinateQuadPlus n K)
    hQ hrep (coordinatePlusWitnessEquiv K e) σ P hP eP huniq

theorem fivePump_char5_POmegaMinus : FivePumpCharFiveClause .POmegaMinus := by
  intro S _ _ hs _hna ⟨n, f, hm⟩ σ P hP _hZ eP huniq
  exfalso
  have hadm : StatedLieAdmissible .POmegaMinus n 5 f := hm.admissible
  have hn : 1 ≤ n := by have := hadm.2.2; omega
  have hC : StatedClassicalModel S .POmegaMinus n 5 f := hm.statedClassicalModel (by decide)
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id hC
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaMinus
    (Or.inr (Or.inr rfl)) hC hn K hK b c hirr e
  obtain ⟨-, hQ, -⟩ := coordinate_model_witness_minus hC K hK b c hirr e
  exact C5Omega.false_of_orth_data hadm.2.1 hK (Or.inr ⟨rfl, hadm.2.2⟩)
    (coordinateQuadMinus n K hn b c) hQ hrep (coordinateMinusWitnessEquiv K hn b c e) σ P hP eP
    huniq

end CFSG.ComponentClassification.SolMax.FiveCat
