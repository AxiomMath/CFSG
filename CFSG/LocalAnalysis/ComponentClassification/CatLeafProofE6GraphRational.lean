module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6C4Fixed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6F4Fixed
public import CFSG.LocalAnalysis.SteinbergCEOddResidualE6GraphCore
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6Graph

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.SteinbergCE
  CFSG.LocalAnalysis.SteinbergCE.E6GraphCoset
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

theorem card_fixSubfield_iterateFrobeniusEquiv {k : Type} [Field k] [IsAlgClosed k] {p : ℕ}
    [Fact p.Prime] [CharP k p] {f : ℕ} (hf : 1 ≤ f) :
    Nat.card (fixSubfield (iterateFrobeniusEquiv k p f)) = p ^ f := by
  have e : fixSubfield (iterateFrobeniusEquiv k p f) = frobeniusFixedField k p f := by
    ext c
    rw [mem_frobeniusFixedField]
    change iterateFrobeniusEquiv k p f c = c ↔ _
    rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  rw [e, card_frobeniusFixedField (by omega)]

theorem oddLieCentralQuotient_rationalRootGroup
    {k : Type} [Field k] (σ : k ≃+* k) [Finite (fixSubfield σ)] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card (fixSubfield σ) = p ^ f)
    {AK : ModGL TwistTag.E6.tag (fixSubfield σ)}
    (hAK : AK = diagramMap TwistTag.E6 _ ∨
      AK = rootDiagUnit TwistTag.E6.tag (E6SignedGraph.signTuple _) * diagramMap TwistTag.E6 _) :
    OddLieCentralQuotient p ↥(rationalRootGroup σ AK) := by
  let inner : Subgroup (ModGL TwistTag.E6.tag (fixSubfield σ)) :=
    (posUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
      graphCentralizer TwistTag.E6.tag (fixSubfield σ) AK) ⊔
    (negUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
      graphCentralizer TwistTag.E6.tag (fixSubfield σ) AK)
  let e : ↥(rationalRootGroup σ AK) ≃* ↥inner := (inner.equivMapOfInjective _
    (baseChangeGL_injective (τ := TwistTag.E6.tag) (fixSubfield σ).subtype)).symm
  refine oddLieCentralQuotient_of_mulEquiv e ?_
  rcases hAK with rfl | rfl
  · have hinner : (posUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
        graphCentralizer TwistTag.E6.tag (fixSubfield σ) (diagramMap TwistTag.E6 _)) ⊔
          (negUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
            graphCentralizer TwistTag.E6.tag (fixSubfield σ) (diagramMap TwistTag.E6 _)) =
        graphFixedRootGroup TwistTag.E6 (fixSubfield σ) (RingHom.id _) := by
      rw [graphFixedRootGroup, graphFixedPosUnipotent, graphFixedNegUnipotent,
        twistedFixedGroup_id_eq]
    exact oddLieCentralQuotient_of_mulEquiv (MulEquiv.subgroupCongr hinner)
      (oddLieCentralQuotient_graphFixedRootGroup_E6_id hp hp2 hK)
  · exact oddLieCentralQuotient_rootGenerated hp hp2 hK

theorem oddLieCentralQuotient_of_isComponent_graphCosetFixed
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {e : ℕ} (he : 1 ≤ e) (k : Type) [Field k]
    [IsAlgClosed k] [CharP k p] (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k)
    (ε : ℕ) (hε : ε = 0 ∨ ε = 1) {x : ModGL TwistTag.E6.tag k} (hx : x ∈ graphRational k p e ε)
    (hx2 : (x * diagramMap TwistTag.E6 k) ^ 2 = 1) {L : Subgroup (graphCosetFixed k p e ε x)}
    (hL : IsComponent L) : OddLieCentralQuotient p L := by
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
  exact oddLieCentralQuotient_of_mulEquiv ((e₁.trans e₂).trans (MulEquiv.subgroupCongr hc))
    (oddLieCentralQuotient_rationalRootGroup _ (Fact.out : p.Prime) hp
      (card_fixSubfield_iterateFrobeniusEquiv he) hAK)

end CFSG.ComponentClassification.CatLeafProof
