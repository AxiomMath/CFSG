module

public import CFSG.CharacterTheory.BrauerFowler.Helpers
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG

namespace BrauerFowler

open Helpers

theorem brauer_fowler :
    ∃ f : ℕ → ℕ, ∀ (G : Type) [Group G] [Finite G],
      IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
      ∀ t : G, orderOf t = 2 →
        Nat.card G ≤ f (Nat.card (Subgroup.centralizer ({t} : Set G))) := by
  refine ⟨fun c => (c ^ 2 + c).factorial, ?_⟩
  intro G _ _ hsimple hnoncomm t ht
  let : IsSimpleGroup G := hsimple
  have hcenter : Subgroup.center G = ⊥ := by
    rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G)) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnoncomm
      let : IsMulCommutative G := Subgroup.center_eq_top_iff.mp h
      exact False.elim (hab (IsMulCommutative.is_comm.comm a b))
  have htne : t ≠ 1 := by
    intro h
    have : orderOf t = 1 := orderOf_eq_one_iff.mpr h
    omega
  have htnc : t ∉ Subgroup.center G := by
    rw [hcenter]
    simpa using htne
  obtain ⟨x, hxne, hindex⟩ := exists_centralizer_index_le ht htnc
  let H := Subgroup.centralizer ({x} : Set G)
  have hH : H ≠ ⊤ := by
    intro htop
    have hxcenter : x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ H := by rw [htop]; trivial
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    have : x ∈ (⊥ : Subgroup G) := hcenter ▸ hxcenter
    exact hxne (by simpa using this)
  calc
    Nat.card G ≤ H.index.factorial :=
      natCard_le_factorial_index_of_simple H hH
    _ ≤ (Nat.card (Subgroup.centralizer ({t} : Set G)) ^ 2 +
          Nat.card (Subgroup.centralizer ({t} : Set G))).factorial :=
      Nat.factorial_le (by simpa [H] using hindex)

end BrauerFowler

end CFSG
