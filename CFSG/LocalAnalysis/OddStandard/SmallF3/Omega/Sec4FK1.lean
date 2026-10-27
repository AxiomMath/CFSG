module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FEven

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem Sec4FSetup.k1_outer (h : Sec4FSetup t L S z A B φ) {y : G}
    (hy : ∃ g : G, y = g⁻¹ * t * g) (hyN : y ∈ normalizer (A : Set G))
    {a b : Option (Fin 7)} (hab : a ≠ b) (hσ : Sec4MRealizes t φ y (Equiv.swap a b))
    {r : Option (Fin 7)} (hra : r ≠ a) (hrb : r ≠ b) :
    ∃ (m : G) (ν : Equiv.Perm (Option (Fin 7))), m ∈ normalizer (A : Set G) ∧
      Sec4MRealizes t φ m ν ∧ ν none = r ∧ (m⁻¹ * y * m) * t = t * (m⁻¹ * y * m) ∧
        Sec4MRealizes t φ (m⁻¹ * y * m) (Equiv.swap (ν⁻¹ a) (ν⁻¹ b)) ∧
          InducesTypeSome L (m⁻¹ * y * m) 7 1 6 1 := by
  have hfix : Equiv.swap a b r = r := Equiv.swap_apply_of_ne_of_ne hra hrb
  obtain ⟨m, ν, hm, hν, hν0, hcomm, hreal⟩ := h.exists_move_fixed hσ hfix
  have hswap : ν⁻¹ * Equiv.swap a b * ν = Equiv.swap (ν⁻¹ a) (ν⁻¹ b) := by
    rw [Equiv.swap_apply_apply]
    simp
  rw [hswap] at hreal
  refine ⟨m, ν, hm, hν, hν0, hcomm, hreal, ?_⟩
  have hμ : ∃ g : G, m⁻¹ * y * m = g⁻¹ * t * g := by
    obtain ⟨g, hg⟩ := hy
    exact ⟨g * m, by rw [hg]; group⟩
  have hμN : m⁻¹ * y * m ∈ normalizer (A : Set G) :=
    (normalizer (A : Set G)).mul_mem
      ((normalizer (A : Set G)).mul_mem ((normalizer (A : Set G)).inv_mem hm) hyN) hm
  have hodd : Equiv.Perm.sign (Equiv.swap (ν⁻¹ a) (ν⁻¹ b)) = -1 := by
    rw [Equiv.Perm.sign_swap]
    intro hh
    exact hab ((ν⁻¹).injective hh)
  exact h.outer_of_odd hμ hμN hcomm hreal hodd

end CFSG.OddStandard.SmallF3.Omega
