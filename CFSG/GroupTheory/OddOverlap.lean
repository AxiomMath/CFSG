module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group

public section

namespace CFSG.StandardSubgroupAPI

variable {G : Type*} [Group G]

theorem even_card_of_mem_of_orderOf_eq_two {Q : Subgroup G} {u : G} (hu : u ∈ Q)
    (hu2 : orderOf u = 2) : Even (Nat.card Q) := by
  have h2 := orderOf_dvd_natCard (⟨u, hu⟩ : Q)
  rw [Subgroup.orderOf_mk, hu2] at h2
  exact even_iff_two_dvd.2 h2

theorem mem_of_odd_inf_map_conj_of_le {N Q T : Subgroup G}
    (htight : ∀ g : G, g ∉ N → Odd (Nat.card ↥(Q ⊓ Q.map (MulAut.conj g).toMonoidHom)))
    {g : G} (hTQ : T ≤ Q) (hTg : T ≤ Q.map (MulAut.conj g).toMonoidHom)
    (hev : 2 ∣ Nat.card T) : g ∈ N := by
  by_contra hgN
  exact (Nat.not_even_iff_odd.2 (htight g hgN))
    (even_iff_two_dvd.2 (hev.trans (Subgroup.card_dvd_of_le (le_inf hTQ hTg))))

theorem mem_of_odd_inf_map_conj {N Q T : Subgroup G}
    (htight : ∀ g : G, g ∉ N → Odd (Nat.card ↥(Q ⊓ Q.map (MulAut.conj g).toMonoidHom)))
    (hTQ : T ≤ Q) (hev : 2 ∣ Nat.card T) {y : G} (hy : ∀ x ∈ T, x * y = y * x) : y ∈ N := by
  refine mem_of_odd_inf_map_conj_of_le htight hTQ (fun x hx => ⟨x, hTQ hx, ?_⟩) hev
  show y * x * y⁻¹ = x
  calc y * x * y⁻¹ = (x * y) * y⁻¹ := by rw [hy x hx]
    _ = x := by group

theorem mem_of_odd_inf_map_conj_of_commute {N Q : Subgroup G}
    (htight : ∀ g : G, g ∉ N → Odd (Nat.card ↥(Q ⊓ Q.map (MulAut.conj g).toMonoidHom)))
    {u y : G} (hu : u ∈ Q) (hu2 : orderOf u = 2) (hy : y * u = u * y) : y ∈ N :=
  mem_of_odd_inf_map_conj htight (Subgroup.zpowers_le.2 hu) (by rw [Nat.card_zpowers, hu2])
    fun x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact ((Commute.zpow_right (show Commute y u from hy) k).symm).eq

end CFSG.StandardSubgroupAPI
