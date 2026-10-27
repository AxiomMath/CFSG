module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOutCyc
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.OmegaF2.Irred
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartOne.CTP.StdMatrix
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om

open Matrix Subgroup CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter CFSG.LieType.SeitzGeneration
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadMinus StatedLieAdmissible
  StatedLieTag StatedClassicalModel)
open CFSG.RankThree.PartOne.KCOrthogonalAut (matrixProjectiveImage_eq_top_minus)
open scoped commutatorElement

theorem om_aut_facts {n ℓ f : ℕ} (hn : 4 ≤ n) (hn1 : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Subgroup.center (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) = ⊥ ∧
    OutCycAt 3 (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) ∧
    (∀ a ∈ innAutDerived (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)),
      a ^ 3 = 1 → a ∈ (MulAut.conj : matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c) →*
        MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c))).range) := by
  classical
  have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus n K b c)))
      .POmegaMinus n ℓ f := ⟨⟨hℓ, hf, hn⟩, K, inferInstance, inferInstance, hK, b, c, hirr,
    ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadMinus n K hn1 b c) f :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ f hM hn1 K hK b c hirr (MulEquiv.refl _)
  have htop := matrixProjectiveImage_eq_top_minus K n hn b c hirr
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus hM K hK b c hirr (MulEquiv.refl _)
  have hcen := center_matrix_eq_bot (by omega : 0 < 2 * n) hnd hT
  obtain ⟨ψ, -, hψker, hψcyc⟩ := hg.2.1
  obtain ⟨hInnD, k0, hk0⟩ := hg.2.2.1
  have hD3 : ∀ β ∈ (linearConjugationHom (coordinateQuadMinus n K hn1 b c)).range, β ^ 3 = 1 →
      β ∈ (MulAut.conj : matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c) →*
        MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c))).range := by
    intro β hβD hβ3
    have : (inner (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c))).Normal :=
      inner_normal _
    obtain ⟨g, hgβ⟩ :=
      CFSG.RankThree.PartOne.KCOrthogonalNoninner.mem_of_pow_eq_one_of_relIndex_eq_two_pow hk0
        Nat.prime_three (by norm_num) hβD hβ3
    exact ⟨g, hgβ⟩
  have hderD : innAutDerived (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) ≤
      (linearConjugationHom (coordinateQuadMinus n K hn1 b c)).range := by
    refine sup_le hInnD ?_
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    let x' : ↥(matrixProjectiveImage (coordinateQuadMinus n K hn1 b c)) :=
      ⟨x, htop ▸ Subgroup.mem_top x⟩
    let y' : ↥(matrixProjectiveImage (coordinateQuadMinus n K hn1 b c)) :=
      ⟨y, htop ▸ Subgroup.mem_top y⟩
    have hcomm : Commute (ψ x') (ψ y') := by
      haveI := hψcyc
      have := IsMulCommutative.is_comm.comm (⟨ψ x', x', rfl⟩ : ψ.range) ⟨ψ y', y', rfl⟩
      exact congrArg Subtype.val this
    have h1 : ψ ⁅x', y'⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 hcomm.eq
    have h2 : ⁅x', y'⁆ ∈ ψ.ker := h1
    rw [hψker] at h2
    exact Subgroup.mem_subgroupOf.1 h2
  refine ⟨hcen, ?_, ?_⟩
  · haveI := hψcyc
    refine outCycAt_of_cyclic Nat.prime_three
      (matrixProjectiveImage (coordinateQuadMinus n K hn1 b c))
      (fun α _ => htop ▸ Subgroup.mem_top α) (ψ.rangeRestrict) ?_
    intro x hx hx3
    have h1 : ψ x = 1 := by
      have := congrArg Subtype.val hx
      simpa using this
    have h2 : x ∈ ψ.ker := h1
    rw [hψker] at h2
    exact inner_le_innAutDerived _ (hD3 _ (Subgroup.mem_subgroupOf.1 h2) hx3)
  · intro a ha ha3
    exact hD3 a (hderD ha) ha3

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om

end
