module

public import CFSG.ClassicalInvolution.Asc77.AscC5O9H

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

variable {G : Type} [Group G]

theorem comm_mem_of_factor {S P N₀ : Subgroup G}
    (hPn : ∀ s ∈ S, ∀ q ∈ P, s * q * s⁻¹ ∈ P) (hN₀ : N₀ ≤ S)
    (hfac : ∀ s ∈ S, ∃ n ∈ N₀, ∃ q ∈ P, s = n * q)
    (hcomm : ∀ x ∈ N₀, ∀ y ∈ N₀, x * y * x⁻¹ * y⁻¹ ∈ P) :
    ∀ x ∈ S, ∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ P := by
  intro x hx y hy
  obtain ⟨n₁, hn₁, q₁, hq₁, rfl⟩ := hfac x hx
  obtain ⟨n₂, hn₂, q₂, hq₂, rfl⟩ := hfac y hy
  have hS₁ := hN₀ hn₁
  have hS₂ := hN₀ hn₂
  have hr₁ : n₂⁻¹ * q₁ * n₂ ∈ P := by
    have := hPn _ (S.inv_mem hS₂) q₁ hq₁
    simpa using this
  have hr : n₂⁻¹ * q₁ * n₂ * q₂ * q₁⁻¹ ∈ P :=
    mul_mem (mul_mem hr₁ hq₂) (inv_mem hq₁)
  have hr' : n₁ * (n₂⁻¹ * q₁ * n₂ * q₂ * q₁⁻¹) * n₁⁻¹ ∈ P := hPn _ hS₁ _ hr
  have hr'' : n₂ * (n₁ * (n₂⁻¹ * q₁ * n₂ * q₂ * q₁⁻¹) * n₁⁻¹ * q₂⁻¹) * n₂⁻¹ ∈ P :=
    hPn _ hS₂ _ (mul_mem hr' (inv_mem hq₂))
  have e : n₁ * q₁ * (n₂ * q₂) * (n₁ * q₁)⁻¹ * (n₂ * q₂)⁻¹ =
      (n₁ * n₂ * n₁⁻¹ * n₂⁻¹) *
        (n₂ * (n₁ * (n₂⁻¹ * q₁ * n₂ * q₂ * q₁⁻¹) * n₁⁻¹ * q₂⁻¹) * n₂⁻¹) := by group
  rw [e]
  exact mul_mem (hcomm n₁ hn₁ n₂ hn₂) hr''

variable [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}

namespace Swaps

variable {τ σ : G}

theorem mem_hInf_of_triv [IsSimpleGroup G] (hM : ModelFacts p f)
    (D : Swaps p f Ω K K' W S R R' z t u₁ u₂ a τ σ) {c w : G}
    (hca : c ∈ Subgroup.centralizer ({a} : Set G))
    (hcaz : c ∈ Subgroup.centralizer ({a * z} : Set G))
    (hwa : w ∈ exactLayer Ω a) (hwaz : w ∈ exactLayer Ω (a * z))
    (h1 : c * w⁻¹ ∈ trivialOnQuot (exactLayer Ω a))
    (h2 : c * w⁻¹ ∈ trivialOnQuot (exactLayer Ω (a * z))) :
    c ∈ hSub D.ctx.hyp.std.setting.stand.hyp.conjInvariant a τ D.τC ⊓
      hSub D.ctx.hyp.std.setting.stand.hyp.conjInvariant (a * z) σ D.σC := by
  have C := D.ctx
  have hΩ := D.ctx.hyp.std.setting.stand.hyp.conjInvariant
  set c' := c * w⁻¹ with hc'
  have hc'a : c' ∈ Subgroup.centralizer ({a} : Set G) :=
    mul_mem hca (inv_mem (exactLayer_le_centralizer Ω a hwa))
  have hc'az : c' ∈ Subgroup.centralizer ({a * z} : Set G) :=
    mul_mem hcaz (inv_mem (exactLayer_le_centralizer Ω (a * z) hwaz))
  have hK1 : c' ∈ kerLayer Ω a := ⟨hc'a, h1⟩
  have hK2 : c' ∈ kerLayer Ω (a * z) := ⟨hc'az, h2⟩
  have hodd : Odd (orderOf c') := by
    obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c').ne'
    have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
    have hord : orderOf (c' ^ m) = 2 ^ k := by
      rw [orderOf_pow_of_dvd hm0 (Dvd.intro_left _ hn.symm), hn, Nat.mul_div_cancel _ (by omega)]
    have h2p : IsPGroup 2 (Subgroup.zpowers (c' ^ m)) :=
      IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hord])
    have hpa : c' ^ m * a = a * c' ^ m :=
      Subgroup.mem_centralizer_singleton_iff.mp (pow_mem hc'a m)
    have hpaz : c' ^ m * (a * z) = (a * z) * c' ^ m :=
      Subgroup.mem_centralizer_singleton_iff.mp (pow_mem hc'az m)
    have hone : c' ^ m = 1 := by
      rcases C.twoElt_triv hM.centerless hpa (pow_mem h1 m) h2p with e | e
      · exact e
      · exfalso
        rcases C.swap.twoElt_triv hM.centerless hpaz (pow_mem h2 m) h2p with e' | e'
        · exact C.ha1 (e.symm.trans e')
        · apply C.hz1
          have : a = a * z := e.symm.trans e'
          calc z = a⁻¹ * (a * z) := by group
            _ = a⁻¹ * a := by rw [← this]
            _ = 1 := by group
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hone)
  have hO1 := C.mem_oddCore_of_odd hM.centerless hK1 hodd
  have hO2 := C.swap.mem_oddCore_of_odd hM.centerless hK2 hodd
  have e : c = c' * w := by rw [hc']; group
  rw [e]
  exact ⟨mul_mem (le_hSub_odd hΩ D.τC hO1) (le_hSub_layer hΩ D.τC hwa),
    mul_mem (le_hSub_odd hΩ D.σC hO2) (le_hSub_layer hΩ D.σC hwaz)⟩

end Swaps

end CFSG.ClassicalInvolution.Asc77.C5O
