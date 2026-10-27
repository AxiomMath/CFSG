module

public import CFSG.GH74.QTGen4.Recog.Ku.HStructC

public section

namespace CFSG.GH74.QTGen4.Ku

variable {G : Type} [Group G] [Finite G] {T M H P : Subgroup G} {z : G}

namespace KuHyp

theorem orderOf_z (h : KuHyp G T M H P z) : orderOf z = 2 := by
  have h2 := h.orderOf_zP
  rwa [Subgroup.orderOf_mk] at h2

omit [Finite G] in
theorem center_T_eq (h : KuHyp G T M H P z) :
    Subgroup.center ↥T = Subgroup.zpowers (⟨z, h.z_mem_center_T.1⟩ : ↥T) := by
  ext x
  constructor
  · intro hx
    have hcomm : ∀ y ∈ T, y * (x : G) = (x : G) * y := fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨y, hy⟩)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h.center_T_le_zpowers x x.2 hcomm)
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hzc : (⟨z, h.z_mem_center_T.1⟩ : ↥T) ∈ Subgroup.center ↥T := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact h.z_mem_center_T.2 g g.2
    exact Subgroup.zpow_mem _ hzc k

theorem card_center_T (h : KuHyp G T M H P z) : Nat.card (Subgroup.center ↥T) = 2 := by
  rw [h.center_T_eq, Nat.card_zpowers, Subgroup.orderOf_mk, h.orderOf_z]

theorem exists_sylow_card_center_eq_two (h : KuHyp G T M H P z) :
    ∃ S : Sylow 2 G, Nat.card (Subgroup.center (S : Subgroup G)) = 2 := by
  refine ⟨h.sylow.1.toSylow h.sylow.2, ?_⟩
  exact h.card_center_T

end KuHyp

end CFSG.GH74.QTGen4.Ku

end
