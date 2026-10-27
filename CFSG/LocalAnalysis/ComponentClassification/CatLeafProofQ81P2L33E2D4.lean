module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E2Tools
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E2Open
public import CFSG.LocalAnalysis.ComponentClassification.SteinbergBNEvenInnerInvolutionOddCore
public import CFSG.RankThree.Chevalley.SteinbergBTTrialityCanonicalField

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.E2

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem triality_not_isPGroup
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (hopen : ∀ c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, orderOf c = 2 →
      ¬ IsPGroup 2 ↥(centralizer ({c} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))))
    (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hβ : orderOf β = 2) :
    ¬ IsPGroup 2 (↥(fixedPoints β) ⧸ pPrimeCore 2 ↥(fixedPoints β)) := by
  have hK' : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK'
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  have hσ3 : σ ^ TwistTag.D4.order = 1 := pow_eq_one_of_apply_eq_pow σ hK hσ
  have hβ2 : β ^ 2 = 1 := by rw [← hβ, pow_orderOf_eq_one]
  by_cases hin : β ∈ OuterAutomorphisms.inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
  · obtain ⟨c, rfl⟩ := hin
    have hZ := exceptional_fixed_center_trivial TwistTag.D4 K σ
    have hc : orderOf c = 2 := by
      rw [← orderOf_injective _ (mulAut_conj_injective_of_center_eq_bot hZ) c]
      exact hβ
    exact inner_not_isPGroup (MulEquiv.refl _)
      (fun c hc2 hc1 => isCharacteristicP_centralizer (RootWeightDatum.fixed TwistTag.D4 σ hσ3)
        hc2 hc1) hopen c hc
  obtain ⟨⟨e, he⟩, δ, hδ, -, ψ, hψ, -⟩ :=
    even_triality_outer_involutions_canonical_field hf K hK σ hσ β hβ2 hin
  have he1 : 1 ≤ e := by omega
  have hK6 : Nat.card K = 2 ^ (3 * e * 2) := by rw [hK', he]; ring_nf
  have hσ' : ∀ c, σ c = c ^ 2 ^ (e * 2) := fun c => by rw [hσ, he]; ring_nf
  have hδ' : ∀ c, δ c = c ^ 2 ^ (3 * e) := fun c => by
    rw [hδ, show 3 * f / 2 = 3 * e by omega]
  obtain ⟨-, -, hk, hres, -, hJC, hfixJ, hsimple, -, -⟩ :=
    CFSG.RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel
      Nat.prime_two he1 (le_refl 2) (by norm_num : Nat.Coprime 2 3) K hK6 σ hσ' δ hδ'
  refine not_isPGroup_of_conj hψ ?_
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  set J := trialityFieldImage σ δ
  have hF : fixedPoints (fieldActor (t := TwistTag.D4) σ δ) = J.subgroupOf C := by
    change _ = (J).comap C.subtype
    rw [← hfixJ, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    rfl
  have eJ : J.subgroupOf C ≃* J := Subgroup.subgroupOfEquivOfLe hJC
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
  have h4 : 4 ∣ Nat.card J := by
    rw [hcardJ, ordTrialityD4]
    have h4' : 4 ∣ (2 ^ e) ^ 12 := by
      rw [← pow_mul]
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ∣ 2 ^ (e * 12) := pow_dvd_pow 2 (by omega)
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right h4' _) _) _
  rw [hF]
  exact Ree.not_isPGroup_of_perfect_equiv le_rfl eJ
    (commutator_eq_top_of_simple_of_four_dvd hsimple h4) ((by norm_num : (2 : ℕ) ∣ 4).trans h4)

theorem triality_model_not_isPGroup
    {Y : Type} [Group Y] [Finite Y] {f : ℕ}
    (hopen : InvolutionCentralizerNotTwoGroup .trialityD4)
    (hY : ChevalleyExceptionalModel Y .trialityD4 2 f) (hs : IsSimpleGroup Y)
    (a : MulAut Y) (ha : orderOf a = 2) :
    ¬ IsPGroup 2 (↥(fixedPoints a) ⧸ pPrimeCore 2 ↥(fixedPoints a)) := by
  have hopenY := hopen Y f hY hs
  obtain ⟨⟨-, hf, -⟩, hm⟩ := hY
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf hm
  refine Ree.not_isPGroup_of_mulEquiv e (triality_not_isPGroup hf hK σ hσ ?_) a ha
  intro c hc hP
  exact hopenY (e.symm c) (by rw [MulEquiv.orderOf_eq]; exact hc)
    (hP.of_equiv (centralizerEquiv e.symm c))

end CFSG.ComponentClassification.HarrisLit.L33.E2
