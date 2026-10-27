module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsSplit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt

variable {K : Type*} [Field K] {A : Type*} [CommGroup A] {p : ℕ}
variable {V : Type*} [AddCommGroup V] [Module K V] {σ : K →+* K}
variable (β : V →ₗ[K] V →ₛₗ[σ] K) (ρ : Representation K A V) [Finite A]
variable (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hpK : (p : K) ≠ 0) (hρ : IsIsomRep β ρ)
variable {𝒮 : Set (V →+ V)}

include hp hA hpK hρ

theorem eq_one_of_supported_of_fixed (hmax : IsMaxElem β ρ p 𝒮) (H : Hyperplane A p)
    (g : V ≃ₗ[K] V) (hg : ∀ x y, β (g x) (g y) = β x y) (hgp : ∀ v, (g ^ p) v = v)
    (hgA : ∀ a v, g (ρ a v) = ρ a (g v)) (hg𝒮 : ∀ s ∈ 𝒮, ∀ v, g (s v) = s (g v))
    (hgW : ∀ i : Option (Hyperplane A p), i ≠ some H → ∀ v ∈ weightFamily (p := p) ρ i, g v = v)
    {v₀ : V} (hv₀ : v₀ ∈ weightSpace ρ H.1) (hv₀0 : v₀ ≠ 0) (hfix : g v₀ = v₀) : g = 1 := by
  classical
  haveI : Fintype (Hyperplane A p) := Fintype.ofFinite _
  obtain ⟨a, ha, -⟩ := eq_rho_of_supported β ρ hp hA hpK hρ hmax H g hg hgp hgA hg𝒮 hgW
  have haH : a ∈ H.1 := by
    by_contra h
    exact hv₀0 (eq_zero_of_mem_weightSpace_of_fixed ρ hp hA hpK h hv₀ ((ha v₀).trans hfix))
  refine LinearEquiv.ext fun v => ?_
  show g v = v
  conv_lhs => rw [← sum_eps_apply ρ hp hA hpK v, map_sum]
  conv_rhs => rw [← sum_eps_apply ρ hp hA hpK v]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = some H
  · subst hi
    rw [← ha]
    exact apply_eq_of_mem_weightSpace ρ haH ⟨v, rfl⟩
  · exact hgW i hi _ ⟨v, rfl⟩

omit hρ in
theorem exists_smul_of_finrank_eq_one [FiniteDimensional K V] {H : Hyperplane A p}
    (hH : Module.finrank K (weightSpace ρ H.1) = 1) {x : A} (hx : x ∉ H.1) :
    ∃ c : K, c ^ p = 1 ∧ c ≠ 1 ∧ ∀ v ∈ weightSpace ρ H.1, ρ x v = c • v := by
  obtain ⟨v₀, hv₀, hspan⟩ := finrank_eq_one_iff'.mp hH
  have hv₀0 : (v₀ : V) ≠ 0 := fun h => hv₀ (Subtype.ext h)
  obtain ⟨c, hc⟩ := hspan ⟨ρ x v₀, apply_mem_weightSpace ρ H.1 x v₀.2⟩
  have hc' : ρ x v₀ = c • (v₀ : V) := (congrArg Subtype.val hc).symm
  have hall : ∀ v ∈ weightSpace ρ H.1, ρ x v = c • v := by
    intro v hv
    obtain ⟨d, hd⟩ := hspan ⟨v, hv⟩
    have hd' : v = d • (v₀ : V) := (congrArg Subtype.val hd).symm
    rw [hd', map_smul, hc', smul_comm]
  have hpow : ∀ n : ℕ, ρ (x ^ n) v₀ = c ^ n • (v₀ : V) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, map_mul, Module.End.mul_apply, hc', map_smul, ih, smul_smul, ← pow_succ']
  refine ⟨c, ?_, ?_, hall⟩
  · have h := hpow p
    rw [hA x, map_one, Module.End.one_apply] at h
    have h' : (c ^ p - 1) • (v₀ : V) = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right hv₀0)
  · rintro rfl
    rw [one_smul] at hc'
    exact hv₀0 (eq_zero_of_mem_weightSpace_of_fixed ρ hp hA hpK hx v₀.2 hc')

theorem mul_map_eq_one_of_finrank_eq_one [FiniteDimensional K V] (hβ : β.SeparatingLeft)
    {H : Hyperplane A p} (hH : weightSpace ρ H.1 ≠ ⊥) {x : A} {c : K}
    (hc : ∀ v ∈ weightSpace ρ H.1, ρ x v = c • v) : c * σ c = 1 := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH
  have hex : ∃ w ∈ weightSpace ρ H.1, β v w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv0 (weightFamily_nondeg β ρ hρ hp hA hpK hβ (some H) hv hcon)
  obtain ⟨w, hw, hvw⟩ := hex
  have h := hρ x v w
  rw [hc v hv, hc w hw] at h
  simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc] at h
  have h' : (c * σ c - 1) * β v w = 0 := by
    rw [sub_mul, one_mul, mul_comm c (σ c), h, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hvw)

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
