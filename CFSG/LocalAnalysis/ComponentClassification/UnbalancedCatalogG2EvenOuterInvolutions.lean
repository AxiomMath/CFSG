module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenG2
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiTwoAAutomorphisms

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem oddCore_inf_centralizer_of_map_conj {G : Type*} [Group G] {H : Subgroup G} {ψ α : G}
    (h : CFSG.oddCore ↥(H.map (MulAut.conj ψ).toMonoidHom ⊓
      Subgroup.centralizer {ψ * α * ψ⁻¹}) = ⊥) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥ := by
  have hmap : (H ⊓ Subgroup.centralizer {α}).map (MulAut.conj ψ).toMonoidHom =
      H.map (MulAut.conj ψ).toMonoidHom ⊓ Subgroup.centralizer {ψ * α * ψ⁻¹} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hzH, hzC⟩ := Subgroup.mem_inf.mp hz
      have hzC' := Subgroup.mem_centralizer_singleton_iff.mp hzC
      refine Subgroup.mem_inf.mpr ⟨⟨z, hzH, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc ψ * z * ψ⁻¹ * (ψ * α * ψ⁻¹) = ψ * (z * α) * ψ⁻¹ := by group
        _ = ψ * (α * z) * ψ⁻¹ := by rw [hzC']
        _ = ψ * α * ψ⁻¹ * (ψ * z * ψ⁻¹) := by group
    · intro hy
      obtain ⟨⟨z, hzH, rfl⟩, hyC⟩ := Subgroup.mem_inf.mp hy
      have hyC' := Subgroup.mem_centralizer_singleton_iff.mp hyC
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyC'
      refine ⟨z, Subgroup.mem_inf.mpr ⟨hzH, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, rfl⟩
      calc z * α = ψ⁻¹ * (ψ * z * ψ⁻¹ * (ψ * α * ψ⁻¹)) * ψ := by group
        _ = ψ⁻¹ * (ψ * α * ψ⁻¹ * (ψ * z * ψ⁻¹)) * ψ := by rw [hyC']
        _ = α * z := by group
  exact EvenCatalog.oddCore_eq_bot_of_mulEquiv
    (((H ⊓ Subgroup.centralizer {α}).equivMapOfInjective _ (MulAut.conj ψ).injective).trans
      (MulEquiv.subgroupCongr hmap)).symm h

theorem oddCore_inf_centralizer_entrywiseAdjointAut {e : ℕ} (he : 1 ≤ e) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ (2 * e)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ e)
    (H : Subgroup (MulAut (adjointGroup .G2 K))) (hIH : inner (adjointGroup .G2 K) ≤ H) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {entrywiseAdjointAut .G2 σ}) = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Finite (adjointGroup .G2 K) := generated_group_finite .G2 K
  have : Finite (MulAut (adjointGroup .G2 K)) :=
    Finite.of_injective (fun β : MulAut (adjointGroup .G2 K) => (β : adjointGroup .G2 K →
      adjointGroup .G2 K)) fun _ _ h => MulEquiv.ext (congrFun h)
  obtain ⟨-, hk, hJC, -, ⟨ι, -⟩, -, hNδ, hNnorm, hcent⟩ :=
    even_G2_canonical_field_full_centralizer he K hK σ hσ
  have hσ' : ∀ c, σ c = c ^ 2 ^ (2 * e / 2) := fun c => by
    rw [hσ, show 2 * e / 2 = e by omega]
  obtain ⟨hσσ, -, -⟩ := SpChain.mem_zpowers_of_forall_fixed (by omega) ⟨e, two_mul e⟩ hK hσ'
  set N := ((fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K)).map MulAut.conj with hN
  have hNcore : CFSG.oddCore N = ⊥ := by
    have : CharP (fixSubfield σ) 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        he hk
    have : Finite (fixSubfield σ) := Subtype.finite
    have hJcore := even_G2_odd_core_including_field_two (fixSubfield σ) (ringChar.eq _ 2)
    have e₁ : ↥(adjointGroup .G2 (fixSubfield σ)) ≃* ↥(fixedFieldImage .G2 σ) :=
      (adjointGroup .G2 (fixSubfield σ)).equivMapOfInjective _ (baseChangeGL_injective _)
    exact EvenCatalog.oddCore_eq_bot_of_mulEquiv
      ((e₁.trans (Subgroup.subgroupOfEquivOfLe hJC).symm).trans ι) hJcore
  have hδ2 : entrywiseAdjointAut .G2 σ * entrywiseAdjointAut .G2 σ = 1 := by
    rw [← entrywiseAdjointAut_mul, hσσ, entrywiseAdjointAut_one]
  refine SpChain.oddCore_eq_bot_of_centralizer (N := N) ?_ ?_ ?_ ?_
  · intro n hn
    refine Subgroup.mem_inf.2 ⟨hIH ?_, hNδ hn⟩
    obtain ⟨j, -, rfl⟩ := hn
    exact ⟨j, rfl⟩
  · intro c hc n hn
    have h := hNnorm.conj_mem ⟨n, hNδ hn⟩ (Subgroup.mem_subgroupOf.2 hn)
      ⟨c, (Subgroup.mem_inf.1 hc).2⟩
    exact Subgroup.mem_subgroupOf.1 h
  · intro X hXN hXn hodd
    exact SpChain.eq_bot_of_oddCore_eq_bot hNcore hXN hXn hodd
  · intro c hc hcN
    have hc' : c ∈ Subgroup.centralizer {entrywiseAdjointAut .G2 σ} ⊓
        Subgroup.centralizer (N : Set (MulAut (adjointGroup .G2 K))) :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hc).2,
        Subgroup.mem_centralizer_iff.2 fun n hn => (hcN n hn).symm⟩
    rw [hcent] at hc'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc'
    refine ⟨1, ?_⟩
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, Nat.cast_ofNat, zpow_two, hδ2,
      one_zpow]

theorem even_G2_outer_involution_full_centralizer_odd_core {f : ℕ} (hf : 2 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = 2 ^ f) (H : Subgroup (MulAut (adjointGroup .G2 K)))
    (hIH : inner (adjointGroup .G2 K) ≤ H) {α : MulAut (adjointGroup .G2 K)}
    (hαI : α ∉ inner (adjointGroup .G2 K)) (hα : orderOf α = 2) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥ := by
  rcases even_G2_involution_inner_or_canonical_field hf K hK α hα with h | ⟨hev, hδ⟩
  · exact absurd h hαI
  obtain ⟨e, he⟩ := hev
  obtain ⟨φ₀, hφ₀, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega) hK
  have hσ : ∀ c, (φ₀ ^ e) c = c ^ 2 ^ e :=
    CFSG.LocalAnalysis.ComponentInitial.ringAut_pow_apply_of_sq hφ₀ e
  obtain ⟨β, ψ, hβ, hψ, -⟩ := hδ (φ₀ ^ e).toRingHom fun c => by
    rw [show f / 2 = e by omega]
    exact hσ c
  have hβδ : β = entrywiseAdjointAut .G2 (φ₀ ^ e) :=
    MulEquiv.ext fun u => Subtype.ext (by rw [hβ u, coe_entrywiseAdjointAut])
  refine oddCore_inf_centralizer_of_map_conj (ψ := ψ) ?_
  have hIH' : inner (adjointGroup .G2 K) ≤ H.map (MulAut.conj ψ).toMonoidHom := by
    rintro _ ⟨g, rfl⟩
    refine ⟨MulAut.conj (ψ⁻¹ g), hIH ⟨_, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [mulAut_mul_conj_mul_inv, MulAut.apply_inv_self]
  rw [hψ, hβδ]
  exact oddCore_inf_centralizer_entrywiseAdjointAut (by omega) K
    (by rw [hK, show f = 2 * e by omega]) (φ₀ ^ e) hσ _ hIH'

end CFSG.ComponentClassification.UnbalancedCatalog
