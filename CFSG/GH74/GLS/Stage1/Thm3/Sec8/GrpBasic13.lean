module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic9

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

section Transport2

variable {G : Type*} [Group G]

theorem comm_central_of_equiv {Y U : Subgroup G} (e : ↥Y ≃* UT3 F4) (hUY : U ≤ Y)
    (hU4 : Nat.card ↥U = 4) (hUN : ∀ y ∈ Y, ∀ w ∈ U, y * w * y⁻¹ ∈ U) :
    (∀ a ∈ Y, ∀ b ∈ Y, a * b * a⁻¹ * b⁻¹ ∈ U) ∧ (∀ a ∈ Y, ∀ c ∈ U, a * c = c * a) := by
  let Ubar : Subgroup (UT3 F4) := (U.subgroupOf Y).map e.toMonoidHom
  have hUbar4 : Nat.card ↥Ubar = 4 := by
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUY).toEquiv, hU4]
  have hUbarN : ∀ y, ∀ x ∈ Ubar, y * x * y⁻¹ ∈ Ubar := by
    intro y x hx
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨e.symm y * x₀ * (e.symm y)⁻¹, ?_, ?_⟩
    · show ((e.symm y * x₀ * (e.symm y)⁻¹ : ↥Y) : G) ∈ U
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hUN _ (e.symm y).2 _ hx₀
    · simp
  have hUbarZ : Ubar = ZUT := normal_four_eq_Z hUbarN hUbar4
  have hmemU : ∀ g : ↥Y, e g ∈ ZUT ↔ (g : G) ∈ U := by
    intro g
    rw [← hUbarZ]
    constructor
    · intro hg
      obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.1 hg
      have hcg : c = g := e.injective hce
      rw [hcg] at hc
      exact Subgroup.mem_subgroupOf.1 hc
    · intro hg
      exact Subgroup.mem_map.2 ⟨g, Subgroup.mem_subgroupOf.2 hg, rfl⟩
  constructor
  · intro a ha b hb
    have h1 : e (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹) ∈ ZUT := by
      simp only [map_mul, map_inv]
      rw [ut3_comm]
      exact ⟨rfl, rfl⟩
    have := (hmemU _).1 h1
    simpa using this
  · intro a ha c hc
    have hc' := (hmemU ⟨c, hUY hc⟩).2 hc
    have h1 : e (⟨a, ha⟩ * ⟨c, hUY hc⟩ * ⟨a, ha⟩⁻¹ * ⟨c, hUY hc⟩⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [ut3_comm]
      have hx1 : (e ⟨c, hUY hc⟩).a = 0 := hc'.1
      have hx2 : (e ⟨c, hUY hc⟩).b = 0 := hc'.2
      ext
      · rfl
      · rfl
      · show (e ⟨a, ha⟩).a * (e ⟨c, hUY hc⟩).b - (e ⟨c, hUY hc⟩).a * (e ⟨a, ha⟩).b = 0
        rw [hx1, hx2]
        ring
    have h2 : (⟨a, ha⟩ * ⟨c, hUY hc⟩ * ⟨a, ha⟩⁻¹ * ⟨c, hUY hc⟩⁻¹ : ↥Y) = 1 :=
      e.injective (by rw [h1, map_one])
    have h3 := congrArg Subtype.val h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h3
    calc a * c = (a * c * a⁻¹ * c⁻¹) * (c * a) := by group
      _ = c * a := by rw [h3, one_mul]

end Transport2

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
