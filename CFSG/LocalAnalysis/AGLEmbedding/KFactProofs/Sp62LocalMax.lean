module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalGroups
public import Certificates.Certificate9443

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp62Local

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.Quasithin.H13 CFSG.KGroups.Sp6

theorem sp62_double_cosets (x : H6) :
    x ∈ W0 ∨ ∃ w ∈ W0, ∃ w' ∈ W0, x = w * elt cG1 * w' :=
  Certificates.certificate9443 x

theorem exists_mem_W0_or (x : H6) :
    x ∈ W0 ∨ ∃ w ∈ W0, ∃ w' ∈ W0, x = w * elt cG1 * w' :=
  sp62_double_cosets x

theorem eq_top_of_mem_not_mem
    {X₀ : Subgroup H6} (hW : W0 ≤ X₀) {g : H6} (hg : g ∈ X₀) (hgW : g ∉ W0) : X₀ = ⊤ := by
  rcases exists_mem_W0_or g with h | ⟨w, hw, w', hw', hgeq⟩
  · exact absurd h hgW
  · have hg1 : elt cG1 ∈ X₀ := by
      have : elt cG1 = w⁻¹ * g * w'⁻¹ := by rw [hgeq]; group
      rw [this]
      exact mul_mem (mul_mem (inv_mem (hW hw)) hg) (inv_mem (hW hw'))
    rw [eq_top_iff]
    intro x _
    rcases exists_mem_W0_or x with hx | ⟨u, hu, u', hu', rfl⟩
    · exact hW hx
    · exact mul_mem (mul_mem (hW hu) hg1) (hW hu')

theorem eq_W0_of_ne_top
    {X₀ : Subgroup H6} (hW : W0 ≤ X₀) (hne : X₀ ≠ ⊤) : X₀ = W0 := by
  by_contra h
  obtain ⟨g, hg, hgW⟩ : ∃ g ∈ X₀, g ∉ W0 := by
    by_contra hcon
    push Not at hcon
    exact h (le_antisymm hcon hW)
  exact hne (eq_top_of_mem_not_mem hW hg hgW)

end CFSG.AGLEmbedding.KFactProofs.Sp62Local
