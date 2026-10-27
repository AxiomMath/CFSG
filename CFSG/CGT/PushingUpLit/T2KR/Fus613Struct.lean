module

public import CFSG.CGT.PushingUpLit.T2KR.Fus613Pres
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.CGT.PushingUpLit.T2KR.Model613

open DihedralGroup
open scoped commutatorElement

namespace Struct613Rel

variable {G : Type} [Group G] {g₀ g₁ g₂ g₃ ξ ρ u β : G}
  (hR : Struct613Rel g₀ g₁ g₂ g₃ ξ ρ u β)
include hR

theorem Phi_injective (hg : g₀ ≠ 1) : Function.Injective hR.Phi := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 T0 := IsPGroup.of_card (n := 8) (by rw [card_T0]; norm_num)
  have hnil : Group.IsNilpotent T0 := hp.isNilpotent
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal (H := hR.Phi.ker) hne
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h
  have hzK : (z : T0) ∈ hR.Phi.ker := (Subgroup.mem_inf.1 z.2).1
  have hzC : (z : T0) ∈ Subgroup.center T0 := (Subgroup.mem_inf.1 z.2).2
  rcases center_T0 z (fun g => (Subgroup.mem_center_iff.1 hzC g).symm) with h1 | h1
  · exact hz1 (Subtype.ext h1)
  · have h0 : hR.Phi (e 0) = g₀ := hR.Phi_e0
    have : hR.Phi (e 0) = 1 := by rw [← h1]; exact hzK
    exact hg (by rw [← h0]; exact this)

end Struct613Rel

theorem struct613 {G : Type} [Group G] {g₀ g₁ g₂ g₃ ξ ρ u β : G}
    (hR : Struct613Rel g₀ g₁ g₂ g₃ ξ ρ u β) (hg0 : g₀ ≠ 1) :
    (g₀ ≠ 1 ∧ ∀ t ∈ S613 g₀ g₁ g₂ g₃ ξ ρ u β, t * g₀ = g₀ * t) ∧
    (∀ t ∈ S613 g₀ g₁ g₂ g₃ ξ ρ u β, t * t = 1 → t ≠ 1 → t ≠ g₀ →
      t ∈ ⁅S613 g₀ g₁ g₂ g₃ ξ ρ u β ⊓ Subgroup.centralizer ({t} : Set G),
        S613 g₀ g₁ g₂ g₃ ξ ρ u β ⊓ Subgroup.centralizer ({t} : Set G)⁆ →
      ∀ w ∈ ⁅S613 g₀ g₁ g₂ g₃ ξ ρ u β ⊓ Subgroup.centralizer ({t} : Set G),
        S613 g₀ g₁ g₂ g₃ ξ ρ u β ⊓ Subgroup.centralizer ({t} : Set G)⁆,
        w = 1 ∨ w = t ∨ w = g₀ ∨ w = t * g₀) ∧
    (g₀ ∈ ⁅S613 g₀ g₁ g₂ g₃ ξ ρ u β ⊓ Subgroup.centralizer ({ξ * ρ} : Set G),
      S613 g₀ g₁ g₂ g₃ ξ ρ u β ⊓ Subgroup.centralizer ({ξ * ρ} : Set G)⁆ ∧
    ∃ w ∈ ⁅S613 g₀ g₁ g₂ g₃ ξ ρ u β ⊓ Subgroup.centralizer ({ξ * ρ} : Set G),
      S613 g₀ g₁ g₂ g₃ ξ ρ u β ⊓ Subgroup.centralizer ({ξ * ρ} : Set G)⁆, w ≠ 1 ∧ w ≠ g₀) ∧
    ⁅S613 g₀ g₁ g₂ g₃ ξ ρ u β, S613 g₀ g₁ g₂ g₃ ξ ρ u β⁆ ≤
      Subgroup.closure ({g₀, g₁, g₂, g₃, ρ, u} : Set G) := by
  have hinj := hR.Phi_injective hg0
  exact ⟨hR.part_Z hinj, hR.part_A hinj, hR.part_B hinj, hR.part_L⟩

end CFSG.CGT.PushingUpLit.T2KR.Model613
