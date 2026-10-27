module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5AaFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5Card

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B : Subgroup G} {z : G}

section

variable (H : ThCyc G L R t)

include H

theorem ThCyc.theta_conj {k : G} (hkL : k ∈ L) (r : G) :
    theta t (k * r * k⁻¹) = k * theta t r * k⁻¹ := by
  have hkt : k * t * k⁻¹ = t := by
    rw [← H.comm_of_mem_L hkL]
    group
  have : theta t (k * r * k⁻¹) = k * (r * (k⁻¹ * t * k) * r⁻¹ * (k⁻¹ * t⁻¹ * k)) * k⁻¹ := by
    simp only [theta]
    group
  rw [this]
  have hkt' : k⁻¹ * t * k = t := by
    rw [← H.comm_of_mem_L (L.inv_mem hkL)]
    group
  have hkt'' : k⁻¹ * t⁻¹ * k = t⁻¹ := by
    have : k⁻¹ * t⁻¹ * k = (k⁻¹ * t * k)⁻¹ := by group
    rw [this, hkt']
  rw [hkt', hkt'']
  simp only [theta]

end

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z)

include H W

theorem ThCyc.centralizer_le_Y {k : G} (hkL : k ∈ L)
    (hfix : ∀ x ∈ A, k * x * k⁻¹ = x → x = 1) {r : G} (hr : r ∈ Bp A t) (hkr : k * r = r * k) :
    r ∈ centralizer ((W5 A t : Subgroup G) : Set G) := by
  have hθ : theta t r ∈ A := H.theta_mem_A W hr
  have hfixθ : k * theta t r * k⁻¹ = theta t r := by
    rw [← H.theta_conj hkL r]
    have : k * r * k⁻¹ = r := by rw [hkr]; group
    rw [this]
  exact (H.theta_eq_one_iff W hr).1 (hfix _ hθ hfixθ)

end

omit [Finite G] in
theorem ThLocalIn2.eq_one_of_fixed {L S A B Aa : Subgroup G} {z b : G}
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) {k : G}
    (hfix : ∀ x ∈ A, k * x * k⁻¹ = x → x = 1) {x : G} (hx : x ∈ Aa)
    (hkx : k * x * k⁻¹ = x) : x = 1 := by
  have h2 : x ^ 2 ∈ A := W2.sq_mem_A hx
  have hk2 : k * x ^ 2 * k⁻¹ = x ^ 2 := by
    have : k * x ^ 2 * k⁻¹ = (k * x * k⁻¹) ^ 2 := conj_pow.symm
    rw [this, hkx]
  have hx2 : x ^ 2 = 1 := hfix _ h2 hk2
  exact hfix x (W2.mem_A_of_sq_eq_one W hx hx2) hkx

end CFSG.EvenSporadicStandard.ThStd
