module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryFreeBound

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem card_lt_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    Nat.card T < (2 ^ f) ^ 6 := by
  obtain ⟨φ, hφ, -⟩ := h.exists_outHom_of_card_sylow hS2
  obtain ⟨e, Q, hB, -, -⟩ := h.exists_bender_of_card_sylow hS2
  have : Finite (MulAut L) := finite_mulAut L
  obtain ⟨Dd, hDn, -, hDcard, -, hQcard⟩ := hB.outer_unitary
  have hout : Nat.card (Outer L) = Nat.gcd 3 (2 ^ f + 1) * (2 * f) := by
    rw [← hDcard, ← hQcard, mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup Dd
  have hrange : Nat.card φ.range ≤ 6 * f := by
    have h1 := Subgroup.card_le_card_group φ.range
    have h2 : Nat.gcd 3 (2 ^ f + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    rw [hout] at h1
    nlinarith
  have hle : szT₁ L T ⊔ zpowers t ≤ T := by
    obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
    exact sup_le (szT₁_le_left L T) (zpowers_le.mpr htT)
  have hker : φ.ker = (szT₁ L T ⊔ zpowers t).subgroupOf T := by
    ext x
    rw [MonoidHom.mem_ker, hφ x, mem_subgroupOf]
  have hcard := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hker, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
    h.card_szT₁_sup_of_card_sylow hS2] at hcard
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hfq : f < 2 ^ f := Nat.lt_two_pow_self
  have h12 : 12 * f < (2 ^ f) ^ 3 := by
    have h3 : 12 * 2 ^ f ≤ (2 ^ f) ^ 3 := by
      have h16 : 4 * 4 ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul hq4 hq4
      calc 12 * 2 ^ f ≤ (2 ^ f * 2 ^ f) * 2 ^ f := Nat.mul_le_mul_right _ (by omega)
        _ = (2 ^ f) ^ 3 := by ring
    omega
  have hpos : 0 < (2 ^ f) ^ 3 := by positivity
  rw [← hcard]
  calc 2 * (2 ^ f) ^ 3 * Nat.card φ.range ≤ 2 * (2 ^ f) ^ 3 * (6 * f) :=
        Nat.mul_le_mul_left _ hrange
    _ = (2 ^ f) ^ 3 * (12 * f) := by ring
    _ < (2 ^ f) ^ 3 * (2 ^ f) ^ 3 := (Nat.mul_lt_mul_left hpos).mpr h12
    _ = (2 ^ f) ^ 6 := by ring

section Certificates


theorem conj_t_not_mem_u3U₁_of_elem_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2)
    {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))} (hE : E ≤ (u3OmegaAction L T R₂ t).range)
    (hEn : (E.subgroupOf (u3OmegaAction L T R₂ t).range).Normal)
    (hEreg : ∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b)
    (hR₂2 : ∀ r ∈ R₂, r ^ 2 = 1) (g : G) :
    g * t * g⁻¹ ∉ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G) :=
  h.conj_t_not_mem_u3U₁_of_card_T_lt_of_card_sylow hS2 hR hc hΩ hE hEn hEreg hR₂2
    (h.card_lt_of_card_sylow hS2) g

theorem conj_t_of_mem_u3U₁_sup_of_elem_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2)
    {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))} (hE : E ≤ (u3OmegaAction L T R₂ t).range)
    (hEn : (E.subgroupOf (u3OmegaAction L T R₂ t).range).Normal)
    (hEreg : ∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b)
    (hR₂2 : ∀ r ∈ R₂, r ^ 2 = 1)
    (hU₁c : ∀ x ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G),
      ∀ y ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G), x * y * x⁻¹ * y⁻¹ ∈ R₂)
    (hU₁2 : ∀ x ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G), x ^ 2 ∈ R₂) (g : G)
    (hg : g * t * g⁻¹ ∈ (u3U L T R₂ t E ⊓ centralizer (R₂ : Set G)) ⊔ zpowers t) :
    ∃ u ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G), g * t * g⁻¹ = u * t * u⁻¹ :=
  h.conj_t_of_mem_u3U₁_sup_of_card_T_lt_of_card_sylow hS2 hR hc hΩ hE hEn hEreg hR₂2 hU₁c hU₁2
    (h.card_lt_of_card_sylow hS2) g hg

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
