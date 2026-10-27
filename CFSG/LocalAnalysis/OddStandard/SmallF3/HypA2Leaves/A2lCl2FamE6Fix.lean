module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamCore
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6C4Fixed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6C4Edge
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6C4Comm
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6C4Gen
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddExc
public import CFSG.ClassicalInvolution.WeakCT.Symplectic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6F4Fixed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6F4Frame
public import CFSG.LieType.Chevalley.GraphFixedSimplePairs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenExc
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddGFE
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeFixedPoints
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairChevalley
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.LieType.Chevalley.E7SupportedBruhat

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Timmesfeld CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Chevalley.E6SignedGraph
open CFSG.ClassicalInvolution.WeakCT (blk spBlock edgeDown doubleBondDiagram_cartanC
  weylElement_sp_one)
open scoped MatrixGroups Matrix
open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (range_le_of_tv)
open scoped MatrixGroups
open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LieType.Ree (ReeTag)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

section


variable {K : Type} [Field K]

theorem cl24_oddLieCentralQuotient_rootGenerated
    [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    {Rel : ℕ → Prop} (hRel : ∀ f', f' = f → Rel f' := by cl24_rel) :
    Cl24Q p Rel ↥(rootGenerated K) := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  exact ⟨.PSp, 4, f, hRel f rfl, ⟨hp, hf, by norm_num, fun h => by simp at h⟩,
    (rootGenerated_recognition hp hp2 hK).2⟩

end

section


variable {K : Type} [Field K] [Finite K]

theorem cl24_oddLieCentralQuotient_graphFixedRootGroup_E6_id
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    {Rel : ℕ → Prop} (hRel : ∀ f', f' = f → Rel f' := by cl24_rel) :
    Cl24Q p Rel ↥(graphFixedRootGroup TwistTag.E6 K (RingHom.id K)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  exact ⟨.F4, 0, f, hRel f rfl, ⟨hp, hf, rfl⟩, (graphFixedRootGroup_E6_id_recognition hp2 hK).2⟩

end

section


theorem cl24_oddLieCentralQuotient_graphFixedRootGroup_E6
    {M : Type} [Field M] [Finite M] {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hM : Nat.card M = (p ^ e) ^ 2) (σ : M ≃+* M) (hσ : ∀ c, σ c = c ^ (p ^ e))
    {Rel : ℕ → Prop} (hRel : ∀ f', f' = e → Rel f' := by cl24_rel) :
    Cl24Q p Rel (graphFixedRootGroup TwistTag.E6 M σ.toRingHom) := by
  have hperf := (finite_fixed_root_group_perfect TwistTag.E6 hp he M hM σ.toRingHom hσ).2.2.1
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 M σ
  obtain ⟨e'⟩ := LieType.Chevalley.nonempty_derivedCentralQuotient_equiv hperf hZ
  have hadm : StatedLieAdmissible .twistedE6 0 p e := ⟨hp, he, rfl⟩
  exact ⟨.twistedE6, 0, e, hRel e rfl, hadm, Or.inr (Or.inl ⟨rfl, by decide, hadm, M, inferInstance,
    inferInstance, hM, σ.toRingHom, hσ,
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e'.symm⟩⟩)⟩

end

end CFSG.OddStandard.SmallF3.HypA2Leaves
