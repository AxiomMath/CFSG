module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamE6Fix
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6GraphRational
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6C4Fixed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6F4Fixed
public import CFSG.LocalAnalysis.SteinbergCEOddResidualE6GraphCore
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6Graph
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6GraphMain
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7TwistMain
public import CFSG.LocalAnalysis.SteinbergCEOddResidualE6Graph
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6Inner
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Export
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Pairs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentCore
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentDisplayed
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentTags
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification
open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.SteinbergCE
  CFSG.LocalAnalysis.SteinbergCE.E6GraphCoset
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.SteinbergCE
  CFSG.LocalAnalysis.SteinbergCE.E6GraphCoset CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatLeaf
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootDiag)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LieType.Ree (ReeTag)

section


theorem cl24_oddLieCentralQuotient_rationalRootGroup
    {k : Type} [Field k] (σ : k ≃+* k) [Finite (fixSubfield σ)] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card (fixSubfield σ) = p ^ f)
    {AK : ModGL TwistTag.E6.tag (fixSubfield σ)}
    (hAK : AK = diagramMap TwistTag.E6 _ ∨
      AK = rootDiagUnit TwistTag.E6.tag (E6SignedGraph.signTuple _) * diagramMap TwistTag.E6 _)
    {Rel : ℕ → Prop} (hRel : ∀ f', f' = f → Rel f' := by cl24_rel) :
    Cl24Q p Rel ↥(rationalRootGroup σ AK) := by
  let inner : Subgroup (ModGL TwistTag.E6.tag (fixSubfield σ)) :=
    (posUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
      graphCentralizer TwistTag.E6.tag (fixSubfield σ) AK) ⊔
    (negUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
      graphCentralizer TwistTag.E6.tag (fixSubfield σ) AK)
  let e : ↥(rationalRootGroup σ AK) ≃* ↥inner := (inner.equivMapOfInjective _
    (baseChangeGL_injective (τ := TwistTag.E6.tag) (fixSubfield σ).subtype)).symm
  refine cl24_of_mulEquiv e ?_
  rcases hAK with rfl | rfl
  · have hinner : (posUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
        graphCentralizer TwistTag.E6.tag (fixSubfield σ) (diagramMap TwistTag.E6 _)) ⊔
          (negUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
            graphCentralizer TwistTag.E6.tag (fixSubfield σ) (diagramMap TwistTag.E6 _)) =
        graphFixedRootGroup TwistTag.E6 (fixSubfield σ) (RingHom.id _) := by
      rw [graphFixedRootGroup, graphFixedPosUnipotent, graphFixedNegUnipotent,
        twistedFixedGroup_id_eq]
    exact cl24_of_mulEquiv (MulEquiv.subgroupCongr hinner)
      (cl24_oddLieCentralQuotient_graphFixedRootGroup_E6_id hp hp2 hK)
  · exact cl24_oddLieCentralQuotient_rootGenerated hp hp2 hK

theorem cl24_oddLieCentralQuotient_of_isComponent_graphCosetFixed
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {e : ℕ} (he : 1 ≤ e) (k : Type) [Field k]
    [IsAlgClosed k] [CharP k p] (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k)
    (ε : ℕ) (hε : ε = 0 ∨ ε = 1) {x : ModGL TwistTag.E6.tag k} (hx : x ∈ graphRational k p e ε)
    (hx2 : (x * diagramMap TwistTag.E6 k) ^ 2 = 1) {L : Subgroup (graphCosetFixed k p e ε x)}
    (hL : IsComponent L)
    {Rel : ℕ → Prop} (hRel : ∀ f', f' = e → Rel f' := by cl24_rel) :
    Cl24Q p Rel L := by
  obtain ⟨hfin, -⟩ := E6_rational_graph_coset_fixed_components p hp he k halg ε hε
  have : Finite (graphRational k p e ε) := hfin
  have hXR : graphCosetFixed k p e ε x ≤ graphRational k p e ε :=
    inf_le_left.trans (Subgroup.commutator_le_self _)
  have : Finite (graphCosetFixed k p e ε x) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hXR)
  set L₂ := L.map (graphCosetFixed k p e ε x).subtype with hL₂
  have hLX : L₂ ≤ graphCosetFixed k p e ε x := Subgroup.map_subtype_le L
  have hsub : L₂.subgroupOf (graphCosetFixed k p e ε x) = L :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) L
  have hL₂c : Assembly.IsComponentOf L₂ (graphCosetFixed k p e ε x) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLX).2
      (by rw [hsub]; exact hL)
  obtain ⟨AK, c, hAK, hc⟩ := exists_conj_eq_rationalRootGroup p hp he k halg ε hε hx hx2
    Nat.prime_two hLX (ExcSelector.isPComponent_two_subgroupOf hL₂c)
  have : Finite (fixSubfield (iterateFrobeniusEquiv k p e)) :=
    ExcSelector.finite_fixSubfield_frobenius p he
  let e₁ : L ≃* L₂ := L.equivMapOfInjective _ (Subgroup.subtype_injective _)
  let e₂ : L₂ ≃* L₂.map (MulAut.conj c).toMonoidHom :=
    L₂.equivMapOfInjective _ (MulAut.conj c).injective
  exact cl24_of_mulEquiv ((e₁.trans e₂).trans (MulEquiv.subgroupCongr hc))
    (cl24_oddLieCentralQuotient_rationalRootGroup _ (Fact.out : p.Prime) hp
      (card_fixSubfield_iterateFrobeniusEquiv he) hAK)

@[expose] def Cl24E6Graph : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    ∀ (α : MulAut (adjointGroup TwistTag.E6.tag K)) (g : adjointGroup TwistTag.E6.tag K)
      (a : Fin TwistTag.E6.tag.rank → Kˣ),
      (∀ h : adjointGroup TwistTag.E6.tag K, (α h : ModGL TwistTag.E6.tag K) =
        (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a *
          diagramMap TwistTag.E6 K * (h : ModGL TwistTag.E6.tag K) *
            (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
              (g : ModGL TwistTag.E6.tag K)⁻¹) → orderOf α = 2 →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → Cl24Q p (fun f' => f' = f) L

theorem cl24_oddE6GraphInput_holds
    : Cl24E6Graph := by
  intro K _ _ p f hp hp2 hK α g a hαg hα L hL
  have hf := (one_le_and_three_le_of_card hp hp2 hK).1
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hk := isAlgebraic_zmod_of_isAlgClosure p K (AlgebraicClosure K)
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα2 : α ^ 2 = 1 := by
    rw [← hα]
    exact pow_orderOf_eq_one α
  obtain ⟨x, hxR, hx2, ⟨Φ⟩⟩ := exists_mulEquiv_E6_graph_coset_fixed hK hKodd hαg hα2
  exact cl24_of_mulEquiv (L.equivMapOfInjective Φ.toMonoidHom Φ.injective)
    (cl24_oddLieCentralQuotient_of_isComponent_graphCosetFixed p hp2 hf _ hk 0 (Or.inl rfl) hxR hx2
      (LocalCores.isComponent_map_mulEquiv Φ hL))

end

end CFSG.OddStandard.SmallF3.HypA2Leaves
