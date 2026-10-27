module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotUniqueFieldTorus
public import CFSG.Adapters.TauCetiExceptional.ReeBasis
public import CFSG.HardMathSupport.Lang.E6Descent.FixedE6
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.OutRank
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2 CFSG.RankThree.PartOne.CTP
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti

section Fixed


theorem twE6_fixedSubgroup_equiv_subfield {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hp : p.Prime) (hp3 : 3 < p) {η : K ≃+* K}
    (hη : orderOf η = p) :
    Nonempty (↥(fixedSubgroup (fieldActor (t := TwistTag.E6) σ η)) ≃*
      ↥(graphFixedRootGroup TwistTag.E6 (fixSubfield η) (fixSubfieldRestrict σ η).toRingHom)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    rw [hσ, hσ, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hηp : η ^ p = 1 := by rw [← hη]; exact pow_orderOf_eq_one η
  have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  have hXJ : entrywiseFixedGroup TwistTag.E6.tag η = fixedFieldImage TwistTag.E6.tag η :=
    CFSG.HardMathSupport.Lang.E6Descent.entrywiseFixedGroup_eq_fixedFieldImage_E6_of_pow η hηp hcop
  have hC : twistedFixedGroup TwistTag.E6 K σ.toRingHom =
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    CFSG.SeitzReduction.TwistedE6Pilot.twistedFixedGroup_eq_graphFixedRootGroup_twistedE6 hσσ
  have hσ₀σ₀ : ∀ c : fixSubfield η, (fixSubfieldRestrict σ η).toRingHom
      ((fixSubfieldRestrict σ η).toRingHom c) = c := fun c => Subtype.ext (hσσ c)
  have hC₀ : twistedFixedGroup TwistTag.E6 (fixSubfield η) (fixSubfieldRestrict σ η).toRingHom =
      graphFixedRootGroup TwistTag.E6 (fixSubfield η) (fixSubfieldRestrict σ η).toRingHom :=
    CFSG.SeitzReduction.TwistedE6Pilot.twistedFixedGroup_eq_graphFixedRootGroup_twistedE6 hσ₀σ₀
  have hL := map_baseChangeGL_twistedFixedGroup_eq (t := TwistTag.E6) (σ := σ) (δ := η)
    (σk := (fixSubfieldRestrict σ η).toRingHom) (coe_fixSubfieldRestrict σ η)
  have hmap : (fixedSubgroup (fieldActor (t := TwistTag.E6) σ η)).map
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype =
      (graphFixedRootGroup TwistTag.E6 (fixSubfield η) (fixSubfieldRestrict σ η).toRingHom).map
        (baseChangeGL (fixSubfield η).subtype) := by
    rw [← hC₀, hL]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyΓ : (y : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
        graphFixedRootGroup_le _ _ _ y.2
      have hyF : Units.map (entrywiseHom η.toRingHom) (y : ModGL TwistTag.E6.tag K) = y :=
        congrArg Subtype.val hy
      have hyX : (y : ModGL TwistTag.E6.tag K) ∈ entrywiseFixedGroup TwistTag.E6.tag η :=
        ⟨hyΓ.1, hyF⟩
      exact ⟨hXJ ▸ hyX, hyΓ, hyX⟩
    · rintro ⟨-, hΓ, hX⟩
      exact ⟨⟨x, hC ▸ hΓ⟩, Subtype.ext (mem_entrywiseFixedGroup.1 hX).2, rfl⟩
  exact ⟨(Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).trans
    ((MulEquiv.subgroupCongr hmap).trans
      (Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective (τ := TwistTag.E6.tag) _)).symm)⟩

end Fixed

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
