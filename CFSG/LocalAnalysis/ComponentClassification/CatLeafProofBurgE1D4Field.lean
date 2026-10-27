module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1D4FieldFix
public import CFSG.LieType.Chevalley.EvenTrialityCanonicalFieldCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1D4Galois
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1D4Shape
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1Field

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {K : Type} [Field K] [Finite K]

theorem burgOddCoreFor_fieldActor_triality
    {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 1 ≤ a) (hK : Nat.card K = (p ^ a) ^ 6)
    (σ δ : K ≃+* K) (hσ : ∀ c, σ c = c ^ ((p ^ a) ^ 2)) (hδ : ∀ c, δ c = c ^ ((p ^ a) ^ 3)) :
    BurgOddCoreFor (fieldActor (t := TwistTag.D4) σ δ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hK6 : Nat.card K = p ^ (6 * a) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK6
  have : CharP (fixSubfield δ) p := Subfield.charP _ p
  have hK₀2 : ringChar (fixSubfield δ) ≠ 2 := by
    rw [ringChar.eq (fixSubfield δ) p]
    exact hp2
  have hmap := map_fixedSubgroup_fieldActor_eq hp ha hK σ δ hσ hδ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (ModGL TwistTag.D4.tag (fixSubfield δ)) := finite_modGL
  obtain ⟨hsimp, hnab, -⟩ := odd_diagram_field_fixed_p_components TwistTag.D4 (fixSubfield δ) hK₀2
    (fixSubfieldRestrict σ δ)
  let e₁ : fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) ≃*
      (graphFixedRootGroup TwistTag.D4 (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom).map
        (baseChangeGL (fixSubfield δ).subtype) :=
    ((fixedSubgroup _).equivMapOfInjective (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  let e₂ := (graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
    (fixSubfieldRestrict σ δ).toRingHom).equivMapOfInjective
      (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield δ).subtype)
      (baseChangeGL_injective (fixSubfield δ).subtype)
  refine ⟨?_, fun β hβ hcomm hfix => ?_⟩
  · have h0 := pPrimeCore_eq_bot_of_isSimpleGroup (Q := graphFixedRootGroup TwistTag.D4
      (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom) hnab
    have h1 := pPrimeCore_map_iso 2 (e₁.trans e₂.symm).symm
    rw [h0, Subgroup.map_bot] at h1
    exact h1.symm
  obtain ⟨-, huniq, -⟩ := odd_triality_exact_automorphism_normal_form hp hp2 (f := 2 * a)
    (by omega) K (by rw [hK]; ring) σ (fun c => by rw [hσ]; ring_nf)
  obtain ⟨⟨g, ε⟩, hgε, -⟩ := huniq β
  dsimp only at hgε
  have hσ3 : ∀ c, σ (σ (σ c)) = c := fun c => by
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul, show (p ^ a) ^ 2 * ((p ^ a) ^ 2 * (p ^ a) ^ 2) =
      (p ^ a) ^ 6 by ring, ← hK, pow_natCard_eq_self]
  have hδε : δ * ε = ε * δ := RingEquiv.ext fun c => by
    change δ (ε c) = ε (δ c)
    rw [hδ, hδ, map_pow]
  have hconj : ∀ (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) h,
      φ * MulAut.conj h * φ⁻¹ = MulAut.conj (φ h) := fun φ h => by
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
  have hgδ : fieldActor σ δ g = g := by
    have h1 : fieldActor σ δ * β * (fieldActor σ δ)⁻¹ = β := by
      rw [hcomm, mul_inv_cancel_right]
    rw [hgε] at h1
    have hεδ : fieldActor (t := TwistTag.D4) σ δ * fieldActor σ ε * (fieldActor σ δ)⁻¹ =
        fieldActor σ ε := by
      rw [← fieldActor_mul, hδε, fieldActor_mul, mul_inv_cancel_right]
    have h2 : fieldActor σ δ * (MulAut.conj g * fieldActor σ ε) * (fieldActor σ δ)⁻¹ =
        MulAut.conj (fieldActor σ δ g) * fieldActor σ ε := by
      calc fieldActor σ δ * (MulAut.conj g * fieldActor σ ε) * (fieldActor σ δ)⁻¹ =
          (fieldActor σ δ * MulAut.conj g * (fieldActor σ δ)⁻¹) *
            (fieldActor σ δ * fieldActor σ ε * (fieldActor σ δ)⁻¹) := by group
        _ = _ := by rw [hconj, hεδ]
    rw [h2] at h1
    exact (conj_mul_fieldActor_injective_D4 σ hσ3 h1).1
  have hgM : g ∈ fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) := hgδ
  have hgJ : ((g : ModGL TwistTag.D4.tag K)) ∈ (graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom).map (baseChangeGL (fixSubfield δ).subtype) :=
    hmap ▸ ⟨g, hgM, rfl⟩
  obtain ⟨g', hg', hgg'⟩ := hgJ
  set ε' := fixSubfieldRestrict ε δ with hε'
  have hβ' : MulAut.conj (⟨g', hg'⟩ : graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom) * fieldActor (fixSubfieldRestrict σ δ) ε' =
      MulAut.conj 1 * fieldActor (fixSubfieldRestrict σ δ) 1 := by
    rw [map_one, one_mul, fieldActor_one]
    refine MulEquiv.ext fun x' => Subtype.ext ?_
    have hx'C : baseChangeGL (fixSubfield δ).subtype (x' : ModGL TwistTag.D4.tag (fixSubfield δ)) ∈
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
      have h1 : baseChangeGL (fixSubfield δ).subtype (x' : ModGL TwistTag.D4.tag (fixSubfield δ)) ∈
          ((fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)).map
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype) :=
        hmap ▸ ⟨x', x'.2, rfl⟩
      obtain ⟨x, -, hx⟩ := h1
      rw [← hx]
      exact x.2
    have hxM : (⟨_, hx'C⟩ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∈
        fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) := by
      have h1 : baseChangeGL (fixSubfield δ).subtype (x' : ModGL TwistTag.D4.tag (fixSubfield δ)) ∈
          ((fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)).map
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype) :=
        hmap ▸ ⟨x', x'.2, rfl⟩
      obtain ⟨x, hxM, hx⟩ := h1
      rwa [show (⟨_, hx'C⟩ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = x from
        Subtype.ext hx.symm]
    have h1 := hfix _ hxM
    rw [hgε, MulAut.mul_apply, MulAut.conj_apply] at h1
    have h2 := congrArg (fun u : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
      (u : ModGL TwistTag.D4.tag K)) h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_fieldActor] at h2
    rw [← hgg', entrywise_baseChangeGL_fixSubfieldRestrict, ← map_inv, ← map_mul,
      ← map_mul] at h2
    have h3 := baseChangeGL_injective _ h2
    change (g' * Units.map (entrywiseHom ε'.toRingHom) (x' : ModGL TwistTag.D4.tag
      (fixSubfield δ)) * g'⁻¹ : ModGL TwistTag.D4.tag (fixSubfield δ)) = x'
    exact h3
  have hσ₀3 : ∀ c, fixSubfieldRestrict σ δ (fixSubfieldRestrict σ δ
      (fixSubfieldRestrict σ δ c)) = c := fun c => Subtype.ext (by
    simp only [coe_fixSubfieldRestrict]
    exact hσ3 c)
  obtain ⟨hg'1, hε'1⟩ := conj_mul_fieldActor_injective_D4 (fixSubfieldRestrict σ δ) hσ₀3 hβ'
  have hg1 : g = 1 := by
    refine Subtype.ext ?_
    rw [← hgg', show g' = 1 from congrArg Subtype.val hg'1, map_one]
    rfl
  have hεK₀ : ∀ c, δ c = c → ε c = c := fun c hc => by
    have h1 := congrArg (fun φ : fixSubfield δ ≃+* fixSubfield δ => (φ ⟨c, hc⟩ : K)) hε'1
    simpa [hε'] using h1
  have hK₀c : Nat.card (RingHom.eqLocusField δ.toRingHom (RingHom.id K)) = (p ^ a) ^ 3 := by
    have h := card_fixSubfield_of_sq_pow hp (e := 3 * a) (by omega)
      (by rw [hK]; ring) δ (fun c => by rw [hδ]; ring_nf)
    rw [show RingHom.eqLocusField δ.toRingHom (RingHom.id K) = fixSubfield δ from rfl, h]
    ring
  have hε2 := sq_eq_one_of_fixes_eqLocus (m := (p ^ a) ^ 3) (by rw [hK]; ring) δ hK₀c ε hεK₀
  have hβ2 : β ^ 2 = 1 := by
    rw [hgε, hg1, map_one, one_mul, sq, ← fieldActor_mul, ← sq, hε2, fieldActor_one]
  exact eq_one_of_sq_eq_one_of_odd hβ hβ2

end CFSG.ComponentClassification.CatLeafProof
