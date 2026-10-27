module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6GraphRational
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6GraphMain
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcDiv
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.LieType.Chevalley.OddE7AllInvolutionComponents

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.SteinbergCE
  CFSG.LocalAnalysis.SteinbergCE.E6GraphCoset CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatLeafProof CFSG.LieType.Chevalley.E6SignedGraph
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.EvenSmallLie.CatalogOrders

section Orders

variable {K : Type} [Field K] [Finite K]

theorem gomi_pow_dvd_graphFixed_F4
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    (p ^ f) ^ 5 ∣ Nat.card ↥(graphFixedRootGroup TwistTag.E6 K (RingHom.id K)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hm⟩ := graphFixedRootGroup_E6_id_recognition hp2 hK
  have hexc := CFSG.Blueprint.LieModel.chevalleyExceptionalModel hm (by decide)
  have hcard := card_eq_lieOrd_of_exceptional hexc
  have hpow : (p ^ f) ^ 24 ∣ lieOrd .F4 0 (p ^ f) :=
    pow_lieExp_dvd (t := .F4) (n := 0) (by decide) (p ^ f)
  rw [← hcard] at hpow
  exact (pow_dvd_pow _ (by norm_num : 5 ≤ 24)).trans
    (hpow.trans (Subgroup.card_quotient_dvd_card _))

theorem gomi_pow_dvd_rootGenerated
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    (p ^ f) ^ 5 ∣ Nat.card ↥(rootGenerated K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hm⟩ := rootGenerated_recognition hp hp2 hK
  have hcl := CFSG.Blueprint.LieModel.statedClassicalModel hm (by decide)
  have hcard := card_eq_lieOrd_of_classical hcl
  have hpow : (p ^ f) ^ 16 ∣ lieOrd .PSp 4 (p ^ f) :=
    pow_lieExp_dvd (t := .PSp) (n := 4) (by decide) (p ^ f)
  rw [← hcard] at hpow
  exact (pow_dvd_pow _ (by norm_num : 5 ≤ 16)).trans
    (hpow.trans (Subgroup.card_quotient_dvd_card _))

end Orders

theorem gomi_pow_dvd_rationalRootGroup
    {k : Type} [Field k] (σ : k ≃+* k) [Finite (fixSubfield σ)] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card (fixSubfield σ) = p ^ f)
    {AK : ModGL TwistTag.E6.tag (fixSubfield σ)}
    (hAK : AK = diagramMap TwistTag.E6 _ ∨
      AK = rootDiagUnit TwistTag.E6.tag (E6SignedGraph.signTuple _) * diagramMap TwistTag.E6 _) :
    (p ^ f) ^ 5 ∣ Nat.card ↥(rationalRootGroup σ AK) := by
  let inner : Subgroup (ModGL TwistTag.E6.tag (fixSubfield σ)) :=
    (posUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
      graphCentralizer TwistTag.E6.tag (fixSubfield σ) AK) ⊔
    (negUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
      graphCentralizer TwistTag.E6.tag (fixSubfield σ) AK)
  let e : ↥(rationalRootGroup σ AK) ≃* ↥inner := (inner.equivMapOfInjective _
    (baseChangeGL_injective (τ := TwistTag.E6.tag) (fixSubfield σ).subtype)).symm
  rw [Nat.card_congr e.toEquiv]
  rcases hAK with rfl | rfl
  · have hinner : (posUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
        graphCentralizer TwistTag.E6.tag (fixSubfield σ) (diagramMap TwistTag.E6 _)) ⊔
          (negUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
            graphCentralizer TwistTag.E6.tag (fixSubfield σ) (diagramMap TwistTag.E6 _)) =
        graphFixedRootGroup TwistTag.E6 (fixSubfield σ) (RingHom.id _) := by
      rw [graphFixedRootGroup, graphFixedPosUnipotent, graphFixedNegUnipotent,
        twistedFixedGroup_id_eq]
    rw [Nat.card_congr (MulEquiv.subgroupCongr hinner).toEquiv]
    exact gomi_pow_dvd_graphFixed_F4 hp hp2 hK
  · exact gomi_pow_dvd_rootGenerated hp hp2 hK

theorem gomi_pow_dvd_of_isComponent_graphCosetFixed
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {e : ℕ} (he : 1 ≤ e) (k : Type) [Field k]
    [IsAlgClosed k] [CharP k p] (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k)
    (ε : ℕ) (hε : ε = 0 ∨ ε = 1) {x : ModGL TwistTag.E6.tag k} (hx : x ∈ graphRational k p e ε)
    (hx2 : (x * diagramMap TwistTag.E6 k) ^ 2 = 1) {L : Subgroup (graphCosetFixed k p e ε x)}
    (hL : CFSG.IsComponent L) : (p ^ e) ^ 5 ∣ Nat.card L := by
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
    Nat.prime_two hLX (CFSG.ComponentClassification.ExcSelector.isPComponent_two_subgroupOf hL₂c)
  have : Finite (fixSubfield (iterateFrobeniusEquiv k p e)) :=
    CFSG.ComponentClassification.ExcSelector.finite_fixSubfield_frobenius p he
  let e₁ : L ≃* L₂ := L.equivMapOfInjective _ (Subgroup.subtype_injective _)
  let e₂ : L₂ ≃* L₂.map (MulAut.conj c).toMonoidHom :=
    L₂.equivMapOfInjective _ (MulAut.conj c).injective
  rw [Nat.card_congr ((e₁.trans e₂).trans (MulEquiv.subgroupCongr hc)).toEquiv]
  exact gomi_pow_dvd_rationalRootGroup _ (Fact.out : p.Prime) hp
    (card_fixSubfield_iterateFrobeniusEquiv he) hAK

theorem gomi_E6_graph_false
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {α : MulAut (adjointGroup TwistTag.E6.tag K)}
    {g : adjointGroup TwistTag.E6.tag K} {a : Fin TwistTag.E6.tag.rank → Kˣ}
    (hαg : ∀ h : adjointGroup TwistTag.E6.tag K, (α h : ModGL TwistTag.E6.tag K) =
      (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 K *
        h * (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
          (g : ModGL TwistTag.E6.tag K)⁻¹)
    (hα : α ^ 2 = 1)
    (L : Subgroup ↥(α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup TwistTag.E6.tag K))))
    (hL : CFSG.IsComponent L) (hdvd : Nat.card L ∣ 51840) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hKodd : Odd (Nat.card K) := by rw [hK]; exact hodd
  have hf : 1 ≤ f := (one_le_and_three_le_of_card hp hp2 hK).1
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hk := isAlgebraic_zmod_of_isAlgClosure p K (AlgebraicClosure K)
  obtain ⟨x, hxR, hx2, ⟨Φ⟩⟩ := exists_mulEquiv_E6_graph_coset_fixed hK hKodd hαg hα
  have hΦL := CFSG.LocalCores.isComponent_map_mulEquiv Φ hL
  have h5 := gomi_pow_dvd_of_isComponent_graphCosetFixed p hp2 hf (AlgebraicClosure K) hk 0
    (Or.inl rfl) hxR hx2 hΦL
  have hc : Nat.card ↥(Subgroup.map Φ.toMonoidHom L) = Nat.card ↥L :=
    Subgroup.card_map_of_injective (f := Φ.toMonoidHom) (K := L) Φ.injective
  rw [hc] at h5
  exact gomi_not_pow_five_dvd hodd (Nat.one_lt_pow (by omega) hp.one_lt) (h5.trans hdvd)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
