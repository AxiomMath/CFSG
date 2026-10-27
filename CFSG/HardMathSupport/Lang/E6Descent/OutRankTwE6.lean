module

public import CFSG.HardMathSupport.Lang.E6Descent.OutRankE6

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Main


theorem exists_inner_mem_of_plane_twE6 {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hp : p.Prime) (hp3 : 3 < p)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) [hE : IsElementaryAbelian p E]
    (hEc : Nat.card E = p ^ 2) :
    ∃ g : twistedE6RootGroup K σ, g ≠ 1 ∧ MulAut.conj g ∈ E := by
  classical
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite (twistedE6RootGroup K σ) := Subtype.finite
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, hcube, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  obtain ⟨-, hcyc⟩ := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hℓ K hK'
  have : Finite (RingAut K) := Finite.of_injective (fun σ : RingAut K => (σ : K → K))
    DFunLike.coe_injective
  have hH : Nat.card {h : RingAut K // h ^ p = 1} ≤ p := by
    have := Fintype.ofFinite (RingAut K)
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le hp.pos
  have : Finite {h : RingAut K // h ^ p = 1} := Finite.of_injective Subtype.val Subtype.val_injective
  obtain ⟨a, b, hab, hΘ⟩ := exists_ne_map_eq_of_plane hp Θ hH E
    (fun x hx => elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) x hx) hEc
  have hxE : (a : MulAut (twistedE6RootGroup K σ))⁻¹ * (b : MulAut (twistedE6RootGroup K σ)) ∈ E :=
    E.mul_mem (E.inv_mem a.2) b.2
  have hxker : (a : MulAut (twistedE6RootGroup K σ))⁻¹ * (b : MulAut (twistedE6RootGroup K σ)) ∈
      Θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hΘ, inv_mul_cancel]
  have hxp := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) _ hxE
  have hxinn : (a : MulAut (twistedE6RootGroup K σ))⁻¹ * (b : MulAut (twistedE6RootGroup K σ)) ∈
      twistedE6Inn K σ := by
    have hmem := hxker
    rw [hker] at hmem
    set H := twistedE6Inn K σ ⊔ twistedE6Diag K σ
    set x : MulAut (twistedE6RootGroup K σ) :=
      (a : MulAut (twistedE6RootGroup K σ))⁻¹ * (b : MulAut (twistedE6RootGroup K σ))
    set c := QuotientGroup.mk' ((twistedE6Inn K σ).subgroupOf H) (⟨x, hmem⟩ : H) with hc
    have hxp' : (⟨x, hmem⟩ : H) ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hxp)
    have hcp : c ^ p = 1 := by rw [hc, ← map_pow, hxp', map_one]
    have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
    have hc1 : c = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 (hcop.gcd_eq_one ▸
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcp) (orderOf_dvd_of_pow_eq_one (hcube c))))
    have h2 := (QuotientGroup.eq_one_iff (N := (twistedE6Inn K σ).subgroupOf H) _).1 hc1
    rwa [Subgroup.mem_subgroupOf] at h2
  obtain ⟨g, hg⟩ := hxinn
  refine ⟨g, ?_, ?_⟩
  · rintro rfl
    rw [map_one] at hg
    apply hab
    have h1 : (a : MulAut (twistedE6RootGroup K σ)) = b := by
      have := congrArg (fun z => (a : MulAut (twistedE6RootGroup K σ)) * z) hg
      simpa using this
    exact Subtype.ext h1
  · rw [hg]
    exact hxE

end Main

end CFSG.HardMathSupport.Lang.E6Descent
