module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

theorem sylow_comm_of_subgroup {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) (h : ∀ S : Sylow p G, IsMulCommutative (S : Subgroup G)) :
    ∀ S : Sylow p H, IsMulCommutative (S : Subgroup H) := by
  intro S
  have hS : IsPGroup p (S.map H.subtype) := by
    obtain ⟨k, hk⟩ := (S.isPGroup').exists_card_eq
    exact IsPGroup.of_card (n := k) (by rw [Subgroup.card_map_of_injective H.subtype_injective]; exact hk)
  obtain ⟨T, hT⟩ := hS.exists_le_sylow
  have hTc := h T
  refine ⟨⟨fun a b => ?_⟩⟩
  apply Subtype.ext
  apply Subtype.ext
  have ha : ((a : H) : G) ∈ (T : Subgroup G) := hT ⟨a, a.2, rfl⟩
  have hb : ((b : H) : G) ∈ (T : Subgroup G) := hT ⟨b, b.2, rfl⟩
  have := congrArg Subtype.val (hTc.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
  simpa using this

theorem sylow_comm_of_surjective {G K : Type} [Group G] [Finite G] [Group K] [Finite K] {p : ℕ}
    [Fact p.Prime] (π : G →* K) (hπ : Function.Surjective π)
    (h : ∀ S : Sylow p G, IsMulCommutative (S : Subgroup G)) :
    ∀ S : Sylow p K, IsMulCommutative (S : Subgroup K) := by
  intro S
  obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective hπ p S
  have hP := h P
  rw [Sylow.coe_mapSurjective]
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
  obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
  apply Subtype.ext
  show (a : K) * b = b * a
  rw [← hxa, ← hyb, ← map_mul, ← map_mul]
  exact congrArg π (congrArg Subtype.val (hP.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
