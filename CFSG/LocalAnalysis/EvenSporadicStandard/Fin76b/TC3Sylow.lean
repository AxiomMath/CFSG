module

public import CFSG.CharacterTheory.Semidihedral.NormalForm
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

variable {G : Type} [Group G]

theorem eight_le_card_of_shape {S : Subgroup G}
    (hS : (∃ k : ℕ, 2 ≤ k ∧ Nonempty (↥S ≃* DihedralGroup (2 ^ k))) ∨
      ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥S ≃* CFSG.Open.SemidihedralGroup n)) :
    8 ≤ Nat.card ↥S := by
  rcases hS with ⟨k, hk, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  · have hn3 : 3 ≤ n := by omega
    rw [Nat.card_congr e.toEquiv, Nat.card_congr (CFSG.Semidihedral.coordinateEquiv n hn3),
      Nat.card_prod]
    have hmod : CFSG.Semidihedral.modulus n = 2 ^ (n - 1) := rfl
    rw [hmod]
    have h1 : Nat.card (ZMod (2 ^ (n - 1))) = 2 ^ (n - 1) := by
      have : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
      simp
    have h2 : Nat.card (ZMod 2) = 2 := by simp
    rw [h1, h2]
    have : 8 ≤ 2 ^ (n - 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem exists_noncomm_of_shape [Finite G] {E S : Subgroup G} {z t : G} (hS2 : IsPGroup 2 S)
    (hSC : S ≤ centralizer (E : Set G)) (hzS : z ∈ S)
    (hS : (∃ k : ℕ, 2 ≤ k ∧ Nonempty (↥S ≃* DihedralGroup (2 ^ k))) ∨
      ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥S ≃* CFSG.Open.SemidihedralGroup n))
    (hcent : ∀ v ∈ centralizer (E : Set G), v * z = z * v →
      v = 1 ∨ v = z ∨ v = t ∨ v = t * z) :
    ∃ s ∈ S, z * s * z⁻¹ * s⁻¹ ≠ 1 ∧ ∃ n : ℕ, (z * s * z⁻¹ * s⁻¹) ^ (2 ^ n) = 1 := by
  classical
  by_contra hcon
  have hall : ∀ s ∈ S, s * z = z * s := by
    intro s hs
    by_contra hne
    apply hcon
    refine ⟨s, hs, fun h1 => hne ?_, ?_⟩
    · exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)).symm
    · have hx : z * s * z⁻¹ * s⁻¹ ∈ S :=
        S.mul_mem (S.mul_mem (S.mul_mem hzS hs) (S.inv_mem hzS)) (S.inv_mem hs)
      obtain ⟨n, hn⟩ := hS2 ⟨_, hx⟩
      exact ⟨n, congrArg Subtype.val hn⟩
  have hsub : (S : Set G) ⊆ ↑({1, z, t, t * z} : Finset G) := by
    intro s hs
    rcases hcent s (hSC hs) (hall s hs) with h | h | h | h <;> simp [h]
  have hcard : Nat.card ↥S ≤ 4 := by
    have h1 : (S : Set G).ncard ≤ (↑({1, z, t, t * z} : Finset G) : Set G).ncard :=
      Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h1
    have h2 : Nat.card ↥S = (S : Set G).ncard := (Nat.card_coe_set_eq (S : Set G))
    exact h2 ▸ h1.trans Finset.card_le_four
  have := eight_le_card_of_shape hS
  omega

end CFSG.EvenSporadicStandard.Fin76b
