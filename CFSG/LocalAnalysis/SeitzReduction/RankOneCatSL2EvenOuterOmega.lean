module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterOmega
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2EvenOuterFixed

public noncomputable section

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv fixedInnerEquiv)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.SeitzReduction.LinearPilot (OmegaPComponents omegaPComponents_of_mulEquiv
  omega_field_pComponents)

@[expose] def OmegaOuterFixedRank (X : Type) [Group X] (g : ℕ) (R : ℕ → Prop) : Prop :=
  SpFixedRankOrNoPComponent X g R ∨ OmegaPComponents X

theorem omegaOuterFixedRank_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {g : ℕ}
    {R : ℕ → Prop} (h : OmegaOuterFixedRank Y g R) : OmegaOuterFixedRank X g R := by
  rcases h with h | h
  · exact Or.inl (spFixedRankOrNoPComponent_of_mulEquiv e h)
  · exact Or.inr (omegaPComponents_of_mulEquiv e h)

variable {K : Type} [Field K] [Finite K] {f n : ℕ}

theorem omega_outer_fixed_rank (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hconj : ∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 →
      ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage Q)
    (α : MulAut (matrixProjectiveDerived Q)) (hα : orderOf α = 2)
    (hout : α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q)) :
    OmegaOuterFixedRank (fixedSubgroup α) f (fun r => r = n - 1) := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have := finite_mulAut_matrixProjectiveDerived Q
  have hαα : α * α = 1 := by
    have h2 := pow_orderOf_eq_one α
    rw [hα] at h2
    rw [← pow_two]
    exact h2
  obtain ⟨β, hβ⟩ := hconj α hαα
  have hc : MulAut.congr β⁻¹ α = β⁻¹ * α * β := MulEquiv.ext fun _ => rfl
  have hγ2 : orderOf (β⁻¹ * α * β) = 2 := by
    rw [← hc]
    exact (orderOf_injective (MulAut.congr β⁻¹).toMonoidHom (MulAut.congr β⁻¹).injective
      α).trans hα
  have hγo : β⁻¹ * α * β ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
    rw [← hc, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hout
  refine omegaOuterFixedRank_of_mulEquiv ((fixedSubgroupCongrEquiv β⁻¹ α).trans
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc))) ?_
  obtain ⟨S, hS, hSγ⟩ := exists_unit_rep hβ
  by_cases hσ : S.val.right = 1
  · obtain ⟨-, -, -, -, F, hF, hker, -, -⟩ :=
      evenOrthogonalRealization_of_regular hf hK (by omega) Q hQ hT hE
    have hmem : (⟨matrixProjectiveConjugationHom Q S, ⟨S, rfl⟩⟩ : matrixProjectiveImage Q) ∈
        F.ker := by
      rw [MonoidHom.mem_ker, hF, hσ]
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    obtain ⟨s, hs⟩ := hmem
    have hs' : matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) =
        β⁻¹ * α * β := hs.trans hSγ
    have hs2 : orderOf (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) = 2 := by
      rw [hs']
      exact hγ2
    have hso : matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) ∉
        OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
      rw [hs']
      exact hγo
    refine omegaOuterFixedRank_of_mulEquiv
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hs'.symm)) ?_
    rcases F4Pilot.omega_linear_fixed hf hK hn hQ hT hE s hs2 hso with hΦ | hch
    · exact Or.inl (Or.inl ⟨K, inferInstance, inferInstance, n - 1, hK, by omega, rfl, hΦ⟩)
    · exact Or.inl (Or.inr (CatLeafProof.not_isPComponent_of_isCharacteristicP hch))
  · exact Or.inr (omega_field_pComponents hf hK hn hQ hT hE hβ hγ2 hγo hS hSγ hσ)

omit [Finite K] in
theorem omega_family_fixed_rank {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    {J : Type} [Group J] {e : ℕ} (hadm : StatedLieAdmissible t n 2 e) (hm : LieModel J t n 2 e)
    (α : MulAut J) (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    OmegaOuterFixedRank (fixedSubgroup α) e (fun r => r = n - 1) := by
  have hC : StatedClassicalModel J t n 2 e := EvenOrthSelector.statedModel_of_lieModel
    (by rcases ht with rfl | rfl <;> decide) hm
  have hf : 1 ≤ e := hadm.2.1
  have hn : 4 ≤ n := by rcases ht with rfl | rfl <;> exact hadm.2.2
  obtain ⟨K, _, _, Q, hK, hQ, hT, hE, hconj, ⟨eJ⟩⟩ :=
    EvenOrthSelector.exists_coordinate_witness ht hC
  have hβ : orderOf (MulAut.congr eJ α) = 2 :=
    (orderOf_injective (MulAut.congr eJ).toMonoidHom (MulAut.congr eJ).injective α).trans hα
  have hβo : MulAut.congr eJ α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  exact omegaOuterFixedRank_of_mulEquiv (fixedSubgroupCongrEquiv eJ α)
    (omega_outer_fixed_rank hf hK hn hQ hT hE hconj _ hβ hβo)

end CFSG.SeitzReduction.RankOne
