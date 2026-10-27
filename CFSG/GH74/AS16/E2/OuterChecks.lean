module

public import CFSG.GH74.AS16.E2.Local3Checks
public import CFSG.GH74.AS16.E2.Outer1

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups

variable {n : ℕ}

theorem exists3_of_model {K G : Type*} [Group K] [Group G] (P : Subgroup G) (e : K ≃* P)
    (t : G) (htP : t ∈ P) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (hone : ∀ u v : K, orderOf u = 2 → orderOf v = 2 → ∃ g : K, g * u * g⁻¹ = v)
    (hex : ∃ c ∈ P, c ^ 3 = 1 ∧ c ≠ 1 ∧ c * t = t * c) :
    ∀ v : K, orderOf v = 2 → ∃ c : K, orderOf c = 3 ∧ c * v = v * c := by
  intro v hv
  set u₀ : K := e.symm ⟨t, htP⟩ with hu₀
  have heu₀ : e u₀ = ⟨t, htP⟩ := e.apply_symm_apply _
  have hu₀2 : u₀ ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, heu₀, map_one]
    exact Subtype.ext (by simpa using ht2)
  have hu₀1 : u₀ ≠ 1 := by
    intro h
    apply ht1
    have := congrArg (fun z => ((e z : P) : G)) h
    simpa [heu₀] using this
  have hu₀o : orderOf u₀ = 2 := orderOf_eq_prime hu₀2 hu₀1
  obtain ⟨c, hcP, hc3, hc1, hct⟩ := hex
  have hc₀3 : (e.symm ⟨c, hcP⟩) ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, MulEquiv.apply_symm_apply, map_one]
    exact Subtype.ext (by simpa using hc3)
  have hc₀1 : e.symm ⟨c, hcP⟩ ≠ 1 := by
    intro h
    apply hc1
    have := congrArg (fun z => ((e z : P) : G)) h
    simpa using this
  have hc₀o : orderOf (e.symm ⟨c, hcP⟩) = 3 := orderOf_eq_prime hc₀3 hc₀1
  have hc₀u : e.symm ⟨c, hcP⟩ * u₀ = u₀ * e.symm ⟨c, hcP⟩ := by
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, heu₀]
    exact Subtype.ext (by simpa using hct)
  obtain ⟨g, hg⟩ := hone u₀ v hu₀o hv
  refine ⟨g * e.symm ⟨c, hcP⟩ * g⁻¹, ?_, ?_⟩
  · have h1 : orderOf (g * e.symm ⟨c, hcP⟩ * g⁻¹) = orderOf (e.symm ⟨c, hcP⟩) := by
      have := (MulAut.conj g).orderOf_eq (e.symm ⟨c, hcP⟩)
      simpa using this
    rw [h1]
    exact hc₀o
  · rw [← hg]
    calc g * e.symm ⟨c, hcP⟩ * g⁻¹ * (g * u₀ * g⁻¹) = g * (e.symm ⟨c, hcP⟩ * u₀) * g⁻¹ := by group
      _ = g * (u₀ * e.symm ⟨c, hcP⟩) * g⁻¹ := by rw [hc₀u]
      _ = g * u₀ * g⁻¹ * (g * e.symm ⟨c, hcP⟩ * g⁻¹) := by group

theorem rank3Table_of_model {K G : Type*} [Group K] [Group G] [Finite K] (P : Subgroup G)
    (e : K ≃* P) (t : G) (htP : t ∈ P) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (hone : ∀ u v : K, orderOf u = 2 → orderOf v = 2 → ∃ g : K, g * u * g⁻¹ = v)
    (hex : ∃ c ∈ P, c ^ 3 = 1 ∧ c ≠ 1 ∧ c * t = t * c)
    (hsyl : ∀ S : Sylow 3 K, 9 ∣ Nat.card S ∧ Nat.card S ∣ 27)
    (hexp : ∀ x ∈ P, x ^ 27 = 1 → x ^ 3 = 1) : Rank3Table K := by
  refine ⟨?_, exists3_of_model P e t htP ht2 ht1 hone hex⟩
  have hexpK : ∀ x : K, x ^ 27 = 1 → x ^ 3 = 1 := by
    intro x hx
    have hx' : ((e x : P) : G) ^ 27 = 1 := by
      have := congrArg (fun z : P => (z : G)) (show (e x) ^ 27 = 1 by rw [← map_pow, hx, map_one])
      simpa using this
    have h3 := hexp _ (e x).2 hx'
    apply e.injective
    rw [map_pow, map_one]
    exact Subtype.ext (by simpa using h3)
  obtain ⟨E, hEc, hE3, hE9⟩ := exists_elemAb9 hsyl hexpK
  exact ⟨E, ⟨hEc, hE3⟩, hE9⟩

end CFSG.GH74.AS16.E2
