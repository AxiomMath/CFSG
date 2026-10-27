module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem y7c_mem_conjSub {g x : Γ} {Y : Subgroup Γ} : x ∈ conjSub g Y ↔ g⁻¹ * x * g ∈ Y := by
  unfold conjSub
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem y7c_mul_mem_conjSub {g y : Γ} {Y : Subgroup Γ} (hy : y ∈ Y) :
    g * y * g⁻¹ ∈ conjSub g Y := by
  rw [y7c_mem_conjSub]
  simpa [mul_assoc] using hy

theorem y7c_conjSub_mul (a b : Γ) (Y : Subgroup Γ) :
    conjSub (a * b) Y = conjSub a (conjSub b Y) := by
  ext x
  simp only [y7c_mem_conjSub, mul_inv_rev, mul_assoc]

theorem y7c_conjSub_one (Y : Subgroup Γ) : conjSub 1 Y = Y := by
  ext x
  simp [y7c_mem_conjSub]

theorem y7c_conjSub_conjSub_of_sq {t : Γ} (ht : t ^ 2 = 1) (Y : Subgroup Γ) :
    conjSub t (conjSub t Y) = Y := by
  rw [← y7c_conjSub_mul, ← pow_two, ht, y7c_conjSub_one]

theorem y7c_conjSub_sup (g : Γ) (H K : Subgroup Γ) :
    conjSub g (H ⊔ K) = conjSub g H ⊔ conjSub g K := by
  unfold conjSub
  exact Subgroup.map_sup _ _ _

theorem y7c_conjSub_le {g : Γ} {H K : Subgroup Γ} (h : H ≤ K) : conjSub g H ≤ conjSub g K := by
  unfold conjSub
  exact Subgroup.map_mono h

theorem y7c_card_conjSub (g : Γ) (Y : Subgroup Γ) : Nat.card ↥(conjSub g Y) = Nat.card ↥Y := by
  unfold conjSub
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem y7c_conjSub_eq_of_normal {Y : Subgroup Γ} [Y.Normal] (g : Γ) : conjSub g Y = Y := by
  ext x
  rw [y7c_mem_conjSub]
  constructor
  · intro h
    simpa [mul_assoc] using Subgroup.Normal.conj_mem ‹Y.Normal› _ h g
  · intro h
    simpa [mul_assoc] using Subgroup.Normal.conj_mem ‹Y.Normal› _ h g⁻¹

theorem y7c_isComponent_conjSub {K : Subgroup Γ} (hK : CFSG.IsComponent K) (g : Γ) :
    CFSG.IsComponent (conjSub g K) := by
  unfold conjSub
  exact CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK

theorem y7c_comm_of_components [Finite Γ] {K₁ K₂ : Subgroup Γ} (h₁ : CFSG.IsComponent K₁)
    (h₂ : CFSG.IsComponent K₂) (hne : K₁ ≠ K₂) : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a := by
  intro a ha b hb
  rcases CFSG.LocalCores.distinct_components_commute h₁ h₂ with h | h
  · exact absurd h hne
  · have h1 : ⁅a, b⁆ ∈ ⁅K₁, K₂⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1

end CFSG.OddStandard.HigherRank.YamadaG23
