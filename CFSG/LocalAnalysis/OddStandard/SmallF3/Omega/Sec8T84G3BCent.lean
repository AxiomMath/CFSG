module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F3Yd
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84g3b_card_subgroupOf {G : Type} [Group G] {Y O : Subgroup G} (h : O ≤ Y) :
    Nat.card (O.subgroupOf Y) = Nat.card O :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem sec8t84g3b_ydata_sub {G : Type} [Group G] [Finite G] {Y O V H : Subgroup G}
    (hY : Sec8T84YData G Y O V H) :
    Odd (Nat.card (O.subgroupOf Y)) ∧ IsElemAb2 (V.subgroupOf Y) 4 ∧
      (∀ v ∈ V.subgroupOf Y, ∀ n ∈ O.subgroupOf Y, v * n = n * v) ∧
      (∃ φ : ↥Y →* alternatingGroup (Fin 6), Function.Surjective φ ∧
        φ.ker = V.subgroupOf Y ⊔ O.subgroupOf Y) ∧
      H.subgroupOf Y ⊓ (V.subgroupOf Y ⊔ O.subgroupOf Y) ≤ O.subgroupOf Y ∧
      H.subgroupOf Y ⊔ (V.subgroupOf Y ⊔ O.subgroupOf Y) = ⊤ ∧
      (∀ v ∈ V.subgroupOf Y, v ≠ 1 → ∀ w ∈ V.subgroupOf Y, w ≠ 1 → ∃ y : ↥Y, y * v * y⁻¹ = w) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sec8t84g3b_card_subgroupOf hY.O_le]; exact hY.O_odd
  · exact ⟨hY.V_e16.1.subgroupOf Y, by rw [sec8t84g3b_card_subgroupOf hY.V_le, hY.V_e16.2]⟩
  · exact fun v hv n hn => Subtype.ext (hY.V_O v hv n hn)
  · obtain ⟨φ, hφ, hker⟩ := hY.quot
    exact ⟨φ, hφ, by rw [hker, Subgroup.subgroupOf_sup hY.V_le hY.O_le]⟩
  · intro x hx
    have hxH : (x : G) ∈ H := hx.1
    have hxVO : (x : G) ∈ V ⊔ O := by
      rw [← Subgroup.subgroupOf_sup hY.V_le hY.O_le] at hx
      exact hx.2
    exact hY.H_inf (Subgroup.mem_inf.mpr ⟨hxH, hxVO⟩)
  · have h1 : (H ⊔ (V ⊔ O)).subgroupOf Y = ⊤ := by
      rw [hY.H_sup, Subgroup.subgroupOf_self]
    rw [Subgroup.subgroupOf_sup hY.H_le (sup_le hY.V_le hY.O_le),
      Subgroup.subgroupOf_sup hY.V_le hY.O_le] at h1
    exact h1
  · intro v hv hv1 w hw hw1
    obtain ⟨y, hy, hconj⟩ := hY.trans (v : G) hv (fun h => hv1 (Subtype.ext h))
      (w : G) hw (fun h => hw1 (Subtype.ext h))
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hconj)⟩

end CFSG.OddStandard.SmallF3.Omega
