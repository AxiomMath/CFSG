module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Witness
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6TwistedOuter

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.SteinbergCE
  CFSG.LocalAnalysis.SteinbergCE.E6GraphCoset CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootDiag)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def A6Free (G : Type) [Group G] : Prop :=
  ∀ L : Subgroup G, IsComponent L → IsEmpty (L ⧸ center L ≃* alternatingGroup (Fin 6))

theorem a6Free_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) (h : A6Free H) :
    A6Free G := by
  intro L hL
  refine ⟨fun eA => ?_⟩
  let eL : L ≃* L.map e.toMonoidHom := L.equivMapOfInjective _ e.injective
  exact (h _ (LocalCores.isComponent_map_mulEquiv e hL)).false
    ((QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)).symm.trans eA)

theorem a6_false_of_a6Free {S : Type} [Group S] [Finite S] {σ : MulAut S}
    {D : Subgroup ↥(fixedSubgroup σ)} (hD : A6Hyp σ D) (hform : A6Free ↥(fixedSubgroup σ)) :
    False := by
  obtain ⟨hDc, ⟨eA⟩⟩ := hD.component
  exact (hform D hDc).false eA

theorem isEmpty_a6_of_lieModel_hO (hO : LieOrderFormulasInput) {B H : Type} [Group B] [Group H]
    (e : B ≃* H) {τ' : StatedLieTag} {n' p f : ℕ} (hadm : StatedLieAdmissible τ' n' p f)
    (hp2 : p ≠ 2) (hlie : Blueprint.LieModel (H ⧸ center H) τ' n' p f)
    (hne : ¬ (τ' = .PSL ∧ n' = 2)) :
    IsEmpty (B ⧸ center B ≃* alternatingGroup (Fin 6)) := by
  refine ⟨fun eA => hne ?_⟩
  have hlieB : Blueprint.LieModel (B ⧸ center B) τ' n' p f :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).symm hlie
  obtain ⟨h1, h2, -⟩ := a6sq_lieModel_a6 hO ⟨eA⟩ hadm hp2 hlieB
  exact ⟨h1, h2⟩


theorem isEmpty_a6_rationalRootGroup_hO (hO : LieOrderFormulasInput) {k : Type} [Field k]
    (σ : k ≃+* k) [Finite (fixSubfield σ)] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card (fixSubfield σ) = p ^ f) {AK : ModGL TwistTag.E6.tag (fixSubfield σ)}
    (hAK : AK = diagramMap TwistTag.E6 _ ∨
      AK = rootDiagUnit TwistTag.E6.tag (E6SignedGraph.signTuple _) * diagramMap TwistTag.E6 _) :
    IsEmpty (↥(rationalRootGroup σ AK) ⧸ Subgroup.center ↥(rationalRootGroup σ AK) ≃*
      alternatingGroup (Fin 6)) := by
  let inner : Subgroup (ModGL TwistTag.E6.tag (fixSubfield σ)) :=
    (posUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
      graphCentralizer TwistTag.E6.tag (fixSubfield σ) AK) ⊔
    (negUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
      graphCentralizer TwistTag.E6.tag (fixSubfield σ) AK)
  let e : ↥(rationalRootGroup σ AK) ≃* ↥inner := (inner.equivMapOfInjective _
    (baseChangeGL_injective (τ := TwistTag.E6.tag) (fixSubfield σ).subtype)).symm
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  rcases hAK with rfl | rfl
  · have hinner : (posUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
        graphCentralizer TwistTag.E6.tag (fixSubfield σ) (diagramMap TwistTag.E6 _)) ⊔
          (negUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
            graphCentralizer TwistTag.E6.tag (fixSubfield σ) (diagramMap TwistTag.E6 _)) =
        graphFixedRootGroup TwistTag.E6 (fixSubfield σ) (RingHom.id _) := by
      rw [graphFixedRootGroup, graphFixedPosUnipotent, graphFixedNegUnipotent,
        twistedFixedGroup_id_eq]
    exact isEmpty_a6_of_lieModel_hO hO (τ' := .F4) (n' := 0)
      (e.trans (MulEquiv.subgroupCongr hinner)) ⟨hp, hf, rfl⟩ hp2
      (graphFixedRootGroup_E6_id_recognition hp2 hK).2 (by decide)
  · exact isEmpty_a6_of_lieModel_hO hO (τ' := .PSp) (n' := 4) e
      ⟨hp, hf, by norm_num, fun h => by simp at h⟩ hp2
      (rootGenerated_recognition hp hp2 hK).2 (by decide)

theorem a6Free_graphCosetFixed (hO : LieOrderFormulasInput)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {e : ℕ} (he : 1 ≤ e) (k : Type) [Field k]
    [IsAlgClosed k] [CharP k p] (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k)
    (ε : ℕ) (hε : ε = 0 ∨ ε = 1) {x : ModGL TwistTag.E6.tag k} (hx : x ∈ graphRational k p e ε)
    (hx2 : (x * diagramMap TwistTag.E6 k) ^ 2 = 1) :
    A6Free (graphCosetFixed k p e ε x) := by
  intro L hL
  refine ⟨fun eA => ?_⟩
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
  refine (isEmpty_a6_rationalRootGroup_hO hO _ (Fact.out : p.Prime) hp
    (card_fixSubfield_iterateFrobeniusEquiv he) hAK).false ?_
  let E := (e₁.trans e₂).trans (MulEquiv.subgroupCongr hc)
  exact (QuotientGroup.congr _ _ E (Subgroup.map_center_eq E)).symm.trans eA

theorem a6_twistedE6_outer_false (hO : LieOrderFormulasInput) {J : Type} [Group J] [Finite J]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .twistedE6 0 p f)
    (hm : Blueprint.LieModel J .twistedE6 0 p f) {α : MulAut J} (hα : orderOf α = 2)
    (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) {D : Subgroup ↥(fixedSubgroup α)}
    (hD : A6Hyp α D) : False := by
  have hf : 1 ≤ f := hadm.2.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, σ, hF, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card TwistTag.E6 hp hf
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  have hF2 : Nat.card F = (p ^ f) ^ 2 := hF
  have : CharP F p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    (show 1 ≤ f * 2 by omega) (by rw [hF2, ← pow_mul])
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have halg := isAlgebraic_zmod_of_isAlgClosure p F (AlgebraicClosure F)
  have hα' : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hα'2 : MulAut.congr e α ^ 2 = 1 := by
    rw [← hα']
    exact pow_orderOf_eq_one _
  have hα'o : MulAut.congr e α ∉ twistedE6Inn F σ := by
    rintro ⟨c, hc⟩
    refine hαo ⟨e.symm c, (MulAut.congr e).injective ?_⟩
    rw [mulAut_congr_conj_twistedE6, MulEquiv.apply_symm_apply]
    exact hc
  obtain ⟨x, hxR, hx2, ⟨Φ⟩⟩ :=
    exists_mulEquiv_twisted_E6_outer_fixed hp2 hf F hF2 σ hσ _ hα'2 hα'o
  let Ψ := (fixedSubgroupCongrEquiv e α).trans Φ
  exact a6_false_of_a6Free hD
    (a6Free_of_mulEquiv Ψ (a6Free_graphCosetFixed hO p hp2 hf _ halg 1 (Or.inr rfl) hxR hx2))

end CFSG.ComponentClassification.CatFC
