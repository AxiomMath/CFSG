module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open CFSG.OddStandard.HigherRank.G2Three.Sec1 Subgroup
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {D : TabData} {elt : ℕ → Γ}

private theorem has_setIfInBounds {D : TabData} (acc : BSet) (hacc : acc.size = D.n) {k i : ℕ}
    (hk : k < D.n) (hi : i < D.n) :
    BSet.has (acc.set! k true) i = true ↔ acc.has i = true ∨ k = i := by
  have hilt : i < acc.size := by omega
  rw [BSet.has, Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?]
  by_cases hki : k = i
  · subst hki
    rw [Array.getElem?_setIfInBounds_self_of_lt hilt]
    simp [BSet.has, Array.getD_eq_getD_getElem?]
  · rw [Array.getElem?_setIfInBounds_ne hki]
    rw [BSet.has, Array.getD_eq_getD_getElem?]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | h)
      · exact h
      · exact absurd h hki

theorem mem_zSeries_succ (k : ℕ) (V : Subgroup Γ) (x : Γ) :
    x ∈ zSeries (k + 1) V ↔ x ∈ V ∧ ∀ y ∈ V, ⁅x, y⁆ ∈ zSeries k V := by
  constructor
  · intro hx
    rw [zSeries, Subgroup.mem_map] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    refine ⟨hzx ▸ z.2, ?_⟩
    intro y hy
    have hmem := (Subgroup.mem_upperCentralSeries_succ_iff (G := ↥V)).1 hz (⟨y, hy⟩ : V)
    rw [zSeries, Subgroup.mem_map]
    refine ⟨⁅z, (⟨y, hy⟩ : V)⁆, hmem, ?_⟩
    rw [← hzx]
    simp [commutatorElement_def]
  · rintro ⟨hxV, hcomm⟩
    rw [zSeries, Subgroup.mem_map]
    refine ⟨⟨x, hxV⟩, ?_, rfl⟩
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    have h := hcomm (y : Γ) y.2
    rw [zSeries, Subgroup.mem_map] at h
    obtain ⟨w, hw, hwz⟩ := h
    have heq : ⁅(⟨x, hxV⟩ : V), y⁆ = w := by
      apply Subtype.ext
      have hcoe : ((⁅(⟨x, hxV⟩ : V), y⁆ : V) : Γ) = ⁅x, (y : Γ)⁆ := by
        simp [commutatorElement_def]
      exact hcoe.trans hwz.symm
    rw [heq]
    exact hw

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
