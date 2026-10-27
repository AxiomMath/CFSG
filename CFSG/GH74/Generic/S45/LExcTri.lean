module

public import CFSG.GH74.Generic.S45.LExcBase
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorComponents
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenInner
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenOrders
public import CFSG.LocalAnalysis.ComponentClassification.SteinbergBNEvenInnerInvolutionOddCore
public import CFSG.RankThree.Chevalley.SteinbergBTTrialityCanonicalField

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {K : Type} [Field K] [Finite K]

theorem even_triality_noSmallQ8 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hβ2 : β ^ 2 = 1)
    (hβ1 : β ≠ 1) {L : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hL : Assembly.IsComponentOf L (fixedSubgroup β))
    : ¬ SmallQ8 L := by
  have hK' : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK'
  have hσ3 : σ ^ TwistTag.D4.order = 1 := pow_eq_one_of_apply_eq_pow σ hK hσ
  by_cases hin : β ∈ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
  · obtain ⟨c, rfl⟩ := hin
    have hc1 : c ≠ 1 := fun h => hβ1 (by rw [h, map_one])
    have hZ := exceptional_fixed_center_trivial TwistTag.D4 K σ
    have hc2 : c ^ 2 = 1 := by
      apply mulAut_conj_injective_of_center_eq_bot hZ
      rw [map_pow, hβ2, map_one]
    exact absurd hL
      (not_isComponentOf_fixedSubgroup_conj (RootWeightDatum.fixed TwistTag.D4 σ hσ3) hc1 hc2 L)
  obtain ⟨⟨e, he⟩, δ, hδ, -, ψ, hψ, -⟩ :=
    even_triality_outer_involutions_canonical_field hf K hK σ hσ β hβ2 hin
  have he1 : 1 ≤ e := by omega
  have hK6 : Nat.card K = 2 ^ (3 * e * 2) := by rw [hK', he]; ring_nf
  have hσ' : ∀ c, σ c = c ^ 2 ^ (e * 2) := fun c => by rw [hσ, he]; ring_nf
  have hδ' : ∀ c, δ c = c ^ 2 ^ (3 * e) := fun c => by
    rw [hδ, show 3 * f / 2 = 3 * e by omega]
  obtain ⟨-, -, hk, hres, -, hJC, hfixJ, hsimple, hnab, -⟩ :=
    CFSG.RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel
      Nat.prime_two he1 (le_refl 2) (by norm_num : Nat.Coprime 2 3) K hK6 σ hσ' δ hδ'
  refine not_smallQ8_of_conj hψ (fun L' hL' => ?_) hL
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  set J := trialityFieldImage σ δ
  have hF : fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) = J.subgroupOf C := by
    change _ = (J).comap C.subtype
    rw [← hfixJ, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    rfl
  rw [hF] at hL'
  have eJ : J.subgroupOf C ≃* J := Subgroup.subgroupOfEquivOfLe hJC
  have : IsSimpleGroup (J.subgroupOf C) := (MulEquiv.isSimpleGroup_congr eJ).2 hsimple
  refine not_smallQ8_of_not_smallType ?_
  rw [eq_of_isComponentOf_of_isSimpleGroup hL', smallType_congr eJ]
  have hk' : Nat.card (fixSubfield δ) = (2 ^ e) ^ 3 := by rw [hk, ← pow_mul, mul_comm]
  have hσ₀ : ∀ c : fixSubfield δ, (fixSubfieldRestrict σ δ).toRingHom c = c ^ ((2 ^ e) ^ 2) :=
    fun c => Subtype.ext (by
      change (fixSubfieldRestrict σ δ c : K) = ((c ^ ((2 ^ e) ^ 2) : fixSubfield δ) : K)
      rw [hres c, hσ', SubmonoidClass.coe_pow, ← pow_mul, mul_comm])
  have e₁ : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom) ≃* ↥J :=
    (graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom).equivMapOfInjective _ (baseChangeGL_injective _)
  have hcardJ : Nat.card J = ordTrialityD4 (2 ^ e) := by
    rw [← Nat.card_congr e₁.toEquiv, (triality_both_orientations_exact_finite_order 2 e
      Nat.prime_two he1 (fixSubfield δ) hk' 2 (Or.inr rfl) _ hσ₀).1, ordTrialityD4]
    ring
  have hnab' : ∃ a b : J, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hnab h
  exact not_smallType_of_card_ordTrialityD4 (center_eq_bot_of_isSimpleGroup' hnab') he1 hcardJ


end CFSG.ComponentClassification.ExcSelector
