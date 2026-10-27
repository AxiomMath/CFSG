module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8SplData

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

namespace S8Data

variable {P : Type} [Group P] {V1 V2 : Subgroup P} {φ1 φ2 : (Fin 5 → ZMod 2) → P}
  {α β : P →* S8A5}

theorem alpha_surj_H (h : S8Data V1 V2 φ1 φ2 α β) (a : S8A5) : ∃ x ∈ s8H V2, α x = a := by
  have hM : β.ker.map α = ⊤ := by
    rw [eq_top_iff]
    intro b _
    obtain ⟨g, hgb, hg1⟩ := h.surj b 1
    exact Subgroup.mem_map.mpr ⟨g, MonoidHom.mem_ker.mpr hg1, hgb⟩
  have hmap : (s8H V2).map α = ⊤ := by
    unfold s8H
    rw [h.cent_V2, Subgroup.map_commutator, hM]
    exact commutator_alternatingGroup_eq_top (by simp)
  have ha : a ∈ (s8H V2).map α := by rw [hmap]; trivial
  obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp ha
  exact ⟨x, hx, hxa⟩

theorem V1_le_H (h : S8Data V1 V2 φ1 φ2 α β) : V1 ≤ s8H V2 := by
  have key : ∀ (a : S8A5) (w : Fin 5 → ZMod 2), IsEvenVec w →
      φ1 (permVec (a : Equiv.Perm (Fin 5)) w + w) ∈ s8H V2 := by
    intro a w hw
    obtain ⟨g, hga, hgb⟩ := h.surj a 1
    have hgM : g ∈ centralizer (V2 : Set P) := by
      rw [h.cent_V2]; exact MonoidHom.mem_ker.mpr hgb
    have hwM : φ1 w ∈ centralizer (V2 : Set P) := by
      rw [h.cent_V2]; exact MonoidHom.mem_ker.mpr (h.beta_V1 (h.coord1.mem w hw))
    have hmem : g * φ1 w * g⁻¹ * (φ1 w)⁻¹ ∈ s8H V2 := Subgroup.commutator_mem_commutator hgM hwM
    rwa [h.act1 g w hw, hga, h.coord1.inv_eq' hw,
      ← h.coord1.mul _ _ (s8_isEvenVec_permVec _ hw) hw] at hmem
  intro x hx
  obtain ⟨u, hu, rfl⟩ := h.coord1.surj x hx
  obtain ⟨a1, a2, w1, w2, hw1, hw2, hu12⟩ := s8_fin_sum2 u hu
  rw [hu12, h.coord1.mul _ _ (s8_isEvenVec_add (s8_isEvenVec_permVec _ hw1) hw1)
    (s8_isEvenVec_add (s8_isEvenVec_permVec _ hw2) hw2)]
  exact mul_mem (key a1 w1 hw1) (key a2 w2 hw2)

end S8Data

end CFSG.OddStandard.SmallF3.Omega
