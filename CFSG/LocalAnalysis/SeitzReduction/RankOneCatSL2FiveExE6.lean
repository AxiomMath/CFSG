module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveEx
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6GraphMain
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6TwistedOuter
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveExTwoPartE

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.SteinbergCE
  CFSG.LocalAnalysis.SteinbergCE.E6GraphCoset
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def F4OrC4CentralQuotient (p f : ℕ) (L : Type) [Group L] : Prop :=
  LieModel (L ⧸ center L) .F4 0 p f ∨ LieModel (L ⧸ center L) .PSp 4 p f

theorem F4OrC4CentralQuotient.of_mulEquiv {p f : ℕ} {L L' : Type} [Group L] [Group L']
    (e : L ≃* L') (h : F4OrC4CentralQuotient p f L') : F4OrC4CentralQuotient p f L :=
  h.imp (FiveList.lieModel_centerQuotient_of_mulEquiv e.symm)
    (FiveList.lieModel_centerQuotient_of_mulEquiv e.symm)

section Graph

namespace FiveEx

theorem f4OrC4_rationalRootGroup
    {k : Type} [Field k] (σ : k ≃+* k) [Finite (fixSubfield σ)] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card (fixSubfield σ) = p ^ f)
    {AK : ModGL TwistTag.E6.tag (fixSubfield σ)}
    (hAK : AK = diagramMap TwistTag.E6 _ ∨
      AK = rootDiagUnit TwistTag.E6.tag (E6SignedGraph.signTuple _) * diagramMap TwistTag.E6 _) :
    F4OrC4CentralQuotient p f ↥(rationalRootGroup σ AK) := by
  have : Fact p.Prime := ⟨hp⟩
  let inner : Subgroup (ModGL TwistTag.E6.tag (fixSubfield σ)) :=
    (posUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
      graphCentralizer TwistTag.E6.tag (fixSubfield σ) AK) ⊔
    (negUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
      graphCentralizer TwistTag.E6.tag (fixSubfield σ) AK)
  let e : ↥(rationalRootGroup σ AK) ≃* ↥inner := (inner.equivMapOfInjective _
    (baseChangeGL_injective (τ := TwistTag.E6.tag) (fixSubfield σ).subtype)).symm
  refine F4OrC4CentralQuotient.of_mulEquiv e ?_
  rcases hAK with rfl | rfl
  · have hinner : (posUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
        graphCentralizer TwistTag.E6.tag (fixSubfield σ) (diagramMap TwistTag.E6 _)) ⊔
          (negUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
            graphCentralizer TwistTag.E6.tag (fixSubfield σ) (diagramMap TwistTag.E6 _)) =
        graphFixedRootGroup TwistTag.E6 (fixSubfield σ) (RingHom.id _) := by
      rw [graphFixedRootGroup, graphFixedPosUnipotent, graphFixedNegUnipotent,
        twistedFixedGroup_id_eq]
    exact Or.inl (FiveList.lieModel_centerQuotient_of_mulEquiv (MulEquiv.subgroupCongr hinner).symm
      (ComponentClassification.CatLeafProof.graphFixedRootGroup_E6_id_recognition hp2 hK).2)
  · exact Or.inr (ComponentClassification.CatLeafProof.rootGenerated_recognition hp hp2 hK).2

theorem f4OrC4_of_isComponent_graphCosetFixed
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {e : ℕ} (he : 1 ≤ e) (k : Type) [Field k]
    [IsAlgClosed k] [CharP k p] (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k)
    (ε : ℕ) (hε : ε = 0 ∨ ε = 1) {x : ModGL TwistTag.E6.tag k} (hx : x ∈ graphRational k p e ε)
    (hx2 : (x * diagramMap TwistTag.E6 k) ^ 2 = 1) {L : Subgroup (graphCosetFixed k p e ε x)}
    (hL : IsComponent L) : F4OrC4CentralQuotient p e L := by
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
    Nat.prime_two hLX (ComponentClassification.ExcSelector.isPComponent_two_subgroupOf hL₂c)
  have : Finite (fixSubfield (iterateFrobeniusEquiv k p e)) :=
    ComponentClassification.ExcSelector.finite_fixSubfield_frobenius p he
  let e₁ : L ≃* L₂ := L.equivMapOfInjective _ (Subgroup.subtype_injective _)
  let e₂ : L₂ ≃* L₂.map (MulAut.conj c).toMonoidHom :=
    L₂.equivMapOfInjective _ (MulAut.conj c).injective
  exact F4OrC4CentralQuotient.of_mulEquiv ((e₁.trans e₂).trans (MulEquiv.subgroupCongr hc))
    (f4OrC4_rationalRootGroup _ (Fact.out : p.Prime) hp
      (ComponentClassification.CatLeafProof.card_fixSubfield_iterateFrobeniusEquiv he) hAK)

theorem f4OrC4_of_isComponent_E6_graph
    (K : Type) [Field K] [Finite K] (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (α : MulAut (adjointGroup TwistTag.E6.tag K))
    (g : adjointGroup TwistTag.E6.tag K) (a : Fin TwistTag.E6.tag.rank → Kˣ)
    (hαg : ∀ h : adjointGroup TwistTag.E6.tag K, (α h : ModGL TwistTag.E6.tag K) =
      (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a *
        diagramMap TwistTag.E6 K * (h : ModGL TwistTag.E6.tag K) *
          (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
            (g : ModGL TwistTag.E6.tag K)⁻¹) (hα : orderOf α = 2)
    (L : Subgroup (fixedSubgroup α)) (hL : IsComponent L) : F4OrC4CentralQuotient p f L := by
  have hf := (ComponentClassification.CatLeafProof.one_le_and_three_le_of_card hp hp2 hK).1
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
  obtain ⟨x, hxR, hx2, ⟨Φ⟩⟩ :=
    ComponentClassification.CatLeafProof.exists_mulEquiv_E6_graph_coset_fixed hK hKodd hαg hα2
  exact F4OrC4CentralQuotient.of_mulEquiv (L.equivMapOfInjective Φ.toMonoidHom Φ.injective)
    (f4OrC4_of_isComponent_graphCosetFixed p hp2 hf _ hk 0 (Or.inl rfl) hxR hx2
      (LocalCores.isComponent_map_mulEquiv Φ hL))

theorem not_lieModel_PSL_two_two_of_f4OrC4 {L : Type} [Group L] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (h : F4OrC4CentralQuotient p f L) :
    ¬ LieModel (L ⧸ center L) .PSL 2 2 2 := by
  intro hA
  rcases h with h | h
  · have hadm : StatedLieAdmissible .F4 0 p f := ⟨hp, hf, rfl⟩
    obtain ⟨ht, -⟩ := eq_five_of_lieModel_PSL_two_two hA hp2 hadm h
    exact absurd ht (by decide)
  · have hadm : StatedLieAdmissible .PSp 4 p f := ⟨hp, hf, by norm_num, fun h => by simp at h⟩
    obtain ⟨ht, -⟩ := eq_five_of_lieModel_PSL_two_two hA hp2 hadm h
    exact absurd ht (by decide)

theorem f4OrC4_of_isComponent_twistedE6_outer {J : Type} [Group J] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .twistedE6 0 p f)
    (hm : LieModel J .twistedE6 0 p f) (α : MulAut J) (hα : orderOf α = 2)
    (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) (L : Subgroup (fixedSubgroup α))
    (hL : IsComponent L) : F4OrC4CentralQuotient p f L := by
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
    rw [ComponentClassification.CatLeafProof.mulAut_congr_conj_twistedE6,
      MulEquiv.apply_symm_apply]
    exact hc
  obtain ⟨x, hxR, hx2, ⟨Φ⟩⟩ :=
    ComponentClassification.CatLeafProof.exists_mulEquiv_twisted_E6_outer_fixed hp2 hf F hF2 σ
      hσ _ hα'2 hα'o
  let Ψ := (ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv e α).trans Φ
  exact F4OrC4CentralQuotient.of_mulEquiv (L.equivMapOfInjective Ψ.toMonoidHom Ψ.injective)
    (f4OrC4_of_isComponent_graphCosetFixed p hp2 hf _ halg 1 (Or.inr rfl) hxR hx2
      (LocalCores.isComponent_map_mulEquiv Ψ hL))

end FiveEx

theorem false_of_catSL2Hyp_E6 {J : Type} [Group J] [Finite J] {m f : ℕ}
    (hJm : LieModel J .E6 m 5 f) {τ : MulAut J} (hτ : CatSL2Hyp J τ 2) : False := by
  obtain rfl := FiveEx.eq_zero_of_lieModel_exc (by decide) hJm
  have hA := fiveA5Group_of_catSL2Hyp hτ
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6
    ((GH74.chevalleyExceptionalModel_of_lieModel (by decide) hJm).2 :
      UntwistedChevalleyModel J .E6 (5 ^ f))
  let e' : J ≃* adjointGroup TwistTag.E6.tag F := e
  have : Finite (adjointGroup TwistTag.E6.tag F) := Finite.of_equiv J e'.toEquiv
  let β : MulAut (adjointGroup TwistTag.E6.tag F) := MulAut.congr e' τ
  have hβ : orderOf β = 2 :=
    (orderOf_injective (MulAut.congr e').toMonoidHom (MulAut.congr e').injective τ).trans hτ.1
  have hAβ : FiveA5Group (fixedSubgroup β) := hA.congr e'
  rcases two_pow_six_dvd_card_fixed_E6_or_graph (by norm_num) (by norm_num) hF β hβ with
    h | ⟨g, a, hga⟩
  · exact hAβ.not_dvd ((pow_dvd_pow 2 (by norm_num : 5 ≤ 6)).trans h)
  · obtain ⟨⟨D, hD, hDm⟩, -⟩ := hAβ
    have hD' := FiveEx.f4OrC4_of_isComponent_E6_graph F 5 f (by norm_num) (by norm_num) hF β g
      a hga hβ D hD
    exact FiveEx.not_lieModel_PSL_two_two_of_f4OrC4 (by norm_num) (by norm_num)
      (FiveEx.one_le_of_card hF) hD' hDm

theorem oddFiveSL2BoundFamilyInput_E6 : OddFiveSL2BoundFamilyInput .E6 :=
  fun _ _ _ _ _ _ _ _ hJm _ hτ => (false_of_catSL2Hyp_E6 hJm hτ).elim

theorem false_of_catSL2Hyp_twistedE6 (hinner : ∀ f, TwistedE6InnerTwoPartInput 5 f 5)
    {J : Type} [Group J] [Finite J] {m f : ℕ} (hJm : LieModel J .twistedE6 m 5 f)
    {τ : MulAut J} (hτ : CatSL2Hyp J τ 2) : False := by
  obtain rfl := FiveEx.eq_zero_of_lieModel_exc (by decide) hJm
  have hA := fiveA5Group_of_catSL2Hyp hτ
  by_cases hi : τ ∈ (MulAut.conj : J →* MulAut J).range
  · exact hA.not_dvd (hinner f J hJm τ hτ.1 hi)
  · obtain ⟨⟨D, hD, hDm⟩, -⟩ := hA
    have hadm := SeitzReduction.CrossChar.statedLieAdmissible_of_lieModel hJm
    exact FiveEx.not_lieModel_PSL_two_two_of_f4OrC4 (by norm_num) (by norm_num) hadm.2.1
      (FiveEx.f4OrC4_of_isComponent_twistedE6_outer (by norm_num) (by norm_num) hadm hJm τ hτ.1
        hi D hD) hDm

theorem oddFiveSL2BoundFamilyInput_twistedE6_of_inner
    (hinner : ∀ f, TwistedE6InnerTwoPartInput 5 f 5) : OddFiveSL2BoundFamilyInput .twistedE6 :=
  fun _ _ _ _ _ _ _ _ hJm _ hτ => (false_of_catSL2Hyp_twistedE6 hinner hJm hτ).elim

end Graph

end CFSG.SeitzReduction.RankOne
