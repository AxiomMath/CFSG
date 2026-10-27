module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CharacterTheory.Semidihedral.NormalForm

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

theorem shape_of_card_sixteen {G : Type} [Group G] {S : Subgroup G}
    (hS : (∃ k : ℕ, 2 ≤ k ∧ Nonempty (↥S ≃* DihedralGroup (2 ^ k))) ∨
      ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥S ≃* CFSG.Open.SemidihedralGroup n))
    (h16 : Nat.card ↥S = 16) :
    Nonempty (↥S ≃* DihedralGroup 8) ∨ Nonempty (↥S ≃* CFSG.Open.SemidihedralGroup 4) := by
  rcases hS with ⟨k, hk, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · left
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at h16
    have h8 : 2 ^ k = 2 ^ 3 := by omega
    have hk3 : k = 3 := Nat.pow_right_injective (le_refl 2) h8
    subst hk3
    exact ⟨e⟩
  · right
    have hn3 : 3 ≤ n := by omega
    rw [Nat.card_congr e.toEquiv, Nat.card_congr (CFSG.Semidihedral.coordinateEquiv n hn3),
      Nat.card_prod] at h16
    have hmod : CFSG.Semidihedral.modulus n = 2 ^ (n - 1) := rfl
    rw [hmod] at h16
    have h1 : Nat.card (ZMod (2 ^ (n - 1))) = 2 ^ (n - 1) := by
      have : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
      simp
    have h2 : Nat.card (ZMod 2) = 2 := by simp
    rw [h1, h2] at h16
    have h8 : 2 ^ (n - 1) = 2 ^ 3 := by omega
    have hn1 : n - 1 = 3 := Nat.pow_right_injective (le_refl 2) h8
    have hn4 : n = 4 := by omega
    subst hn4
    exact ⟨e⟩

end CFSG.EvenSporadicStandard.Fin76b
