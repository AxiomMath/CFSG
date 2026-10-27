module

public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.EvenTrialityCanonicalFieldCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenTriality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenGraphField

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.UnbalancedCatalog (EvenCatalog.oddCore_eq_bot_of_mulEquiv
  EvenCatalog.oddCore_eq_bot_of_normal_of_centralizer EvenCatalog.centralizerConjEquivMap
  EvenCatalog.inner_le_map_conj even_triality_root_group_odd_core)

theorem oddCore_inf_centralizer_fieldActor_triality
    {e : ℕ} (he : 1 ≤ e) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (6 * e)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ (2 * e))
    (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ 2 ^ (3 * e))
    (H : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hIH : inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≤ H) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {fieldActor σ δ}) = ⊥ := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    Finite.of_injective (fun β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =>
      (β : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) fun _ _ h => MulEquiv.ext (congrFun h)
  obtain ⟨-, hk, -, hord, hJC, -, ⟨ι, -⟩, -, hNδ, hNnorm, hcent⟩ :=
    even_triality_canonical_field_full_centralizer he K hK σ hσ δ hδ
  obtain ⟨-, hδ2, -⟩ := triality_field_facts he hK hσ hδ
  set N := trialityFieldInner σ δ with hN
  have hNcore : CFSG.oddCore N = ⊥ := by
    have : CharP (fixSubfield δ) 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (by omega : 1 ≤ 3 * e) hk
    have : Finite (fixSubfield δ) := Subtype.finite
    have hJcore := even_triality_root_group_odd_core (fixSubfield δ) (ringChar.eq _ 2)
      (fixSubfieldRestrict σ δ) hord
    have e₁ : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
        (fixSubfieldRestrict σ δ).toRingHom) ≃* ↥(trialityFieldImage σ δ) :=
      (graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
        (fixSubfieldRestrict σ δ).toRingHom).equivMapOfInjective _ (baseChangeGL_injective _)
    exact EvenCatalog.oddCore_eq_bot_of_mulEquiv
      ((e₁.trans (Subgroup.subgroupOfEquivOfLe hJC).symm).trans ι) hJcore
  have hδ0 : fieldActor (t := TwistTag.D4) σ δ * fieldActor σ δ = 1 := by
    rw [← fieldActor_mul, ← pow_two, hδ2, fieldActor_one]
  refine EvenCatalog.oddCore_eq_bot_of_normal_of_centralizer (R := N) ?_ ?_ hNcore ?_
  · intro n hn
    refine Subgroup.mem_inf.2 ⟨hIH ?_, hNδ hn⟩
    obtain ⟨j, -, rfl⟩ := hn
    exact ⟨j, rfl⟩
  · intro c hc n hn
    have h := hNnorm.conj_mem ⟨n, hNδ hn⟩ (Subgroup.mem_subgroupOf.2 hn)
      ⟨c, (Subgroup.mem_inf.1 hc).2⟩
    exact Subgroup.mem_subgroupOf.1 h
  · intro c hc hcN
    have hc' : c ∈ Subgroup.centralizer {fieldActor σ δ} ⊓
        Subgroup.centralizer (N : Set (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hc).2,
        Subgroup.mem_centralizer_iff.2 fun n hn => (hcN n hn).symm⟩
    rw [hcent] at hc'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc'
    refine ⟨1, ?_⟩
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, Nat.cast_ofNat, zpow_two, hδ0,
      one_zpow]

theorem even_triality_outer_involution_full_centralizer_odd_core
    {f : ℕ} (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (H : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom))) (hIH : inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≤ H)
    {α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hαI : α ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hα : orderOf α = 2) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥ := by
  have hα2 : α ^ 2 = 1 := by
    rw [← hα]
    exact pow_orderOf_eq_one α
  obtain ⟨hev, δ, hδ, -, ψ, hψ, -⟩ :=
    even_triality_outer_involutions_canonical_field hf K hK σ hσ α hα2 hαI
  obtain ⟨e, he⟩ := hev
  have hK' : Nat.card K = 2 ^ (6 * e) := by rw [hK, ← pow_mul, he]; ring_nf
  have hσ' : ∀ c, σ c = c ^ 2 ^ (2 * e) := fun c => by rw [hσ, he, two_mul]
  have hδ' : ∀ c, δ c = c ^ 2 ^ (3 * e) := fun c => by
    rw [hδ, show 3 * f / 2 = 3 * e by omega]
  have hα' : α = ψ⁻¹ * fieldActor σ δ * ψ⁻¹⁻¹ := by
    rw [← hψ]
    group
  rw [hα']
  exact EvenCatalog.oddCore_eq_bot_of_mulEquiv
    (EvenCatalog.centralizerConjEquivMap H ψ⁻¹ (fieldActor σ δ)).symm
    (oddCore_inf_centralizer_fieldActor_triality (by omega) K hK' σ hσ' δ hδ' _
      (EvenCatalog.inner_le_map_conj hIH ψ⁻¹))

end CFSG.LieType.Chevalley
