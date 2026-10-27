module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic5
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic9

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

section Transport3

theorem mem_map_subgroupOf_equiv_iff {G : Type*} [Group G] {Y : Subgroup G} (E : Subgroup G) (e : ↥Y ≃* UT3 F4)
    (g : ↥Y) : e g ∈ (E.subgroupOf Y).map e.toMonoidHom ↔ (g : G) ∈ E := by
  constructor
  · intro hg
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.1 hg
    have hcg : c = g := e.injective hce
    rw [hcg] at hc
    exact Subgroup.mem_subgroupOf.1 hc
  · intro hg
    exact Subgroup.mem_map.2 ⟨g, Subgroup.mem_subgroupOf.2 hg, rfl⟩

theorem equiv_mem_ZUT_iff_mem_normal_four {G : Type*} [Group G] {Y U : Subgroup G} (e : ↥Y ≃* UT3 F4) (hUY : U ≤ Y)
    (hU4 : Nat.card ↥U = 4) (hUN : ∀ y ∈ Y, ∀ w ∈ U, y * w * y⁻¹ ∈ U) (g : ↥Y) :
    e g ∈ ZUT ↔ (g : G) ∈ U := by
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
  rw [← hUbarZ]
  exact mem_map_subgroupOf_equiv_iff U e g

theorem equiv_image_eq_E1UT_or_E2UT {G : Type*} [Group G] {Y E : Subgroup G} (e : ↥Y ≃* UT3 F4)
    (hEY : E ≤ Y) (hEs : ∀ a ∈ E, a * a = 1) (hE16 : Nat.card ↥E = 16) :
    (E.subgroupOf Y).map e.toMonoidHom = E1UT ∨ (E.subgroupOf Y).map e.toMonoidHom = E2UT := by
  set Ebar : Subgroup (UT3 F4) := (E.subgroupOf Y).map e.toMonoidHom with hEbar
  have hcard : Nat.card ↥Ebar = 16 := by
    rw [hEbar, Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEY).toEquiv, hE16]
  have hsq : ∀ t ∈ Ebar, t * t = 1 := by
    intro t ht
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 ht
    have hgE : (g : G) ∈ E := Subgroup.mem_subgroupOf.1 hg
    have h1 : g * g = 1 := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_one]
      exact hEs _ hgE)
    have h2 : e.toMonoidHom g * e.toMonoidHom g = e.toMonoidHom (g * g) := (map_mul _ _ _).symm
    rw [h2, h1, map_one]
  have h1 := card_E1
  have h2 := card_E2
  rcases subgroup_le_or_of_le_union (fun t ht => invol_E (hsq t ht)) with h | h
  · left
    have : Finite ↥E1UT := Nat.finite_of_card_ne_zero (by omega)
    exact Subgroup.eq_of_le_of_card_ge h (by omega)
  · right
    have : Finite ↥E2UT := Nat.finite_of_card_ne_zero (by omega)
    exact Subgroup.eq_of_le_of_card_ge h (by omega)

theorem centralizer_of_noncentral_of_card_sixteen {G : Type*} [Group G] {Y U E : Subgroup G} (e : ↥Y ≃* UT3 F4)
    (hUY : U ≤ Y) (hU4 : Nat.card ↥U = 4) (hUN : ∀ y ∈ Y, ∀ w ∈ U, y * w * y⁻¹ ∈ U) (hEY : E ≤ Y)
    (hEs : ∀ a ∈ E, a * a = 1) (hE16 : Nat.card ↥E = 16) :
    ∀ x ∈ E, x ∉ U → ∀ y ∈ Y, y * x = x * y → y ∈ E := by
  intro x hxE hxU y hyY hxy
  have hxY : x ∈ Y := hEY hxE
  have hXE : e ⟨x, hxY⟩ ∈ (E.subgroupOf Y).map e.toMonoidHom := (mem_map_subgroupOf_equiv_iff E e ⟨x, hxY⟩).2 hxE
  have hXZ : e ⟨x, hxY⟩ ∉ ZUT := fun h => hxU ((equiv_mem_ZUT_iff_mem_normal_four e hUY hU4 hUN _).1 h)
  have hcomm : e ⟨x, hxY⟩ * e ⟨y, hyY⟩ * (e ⟨x, hxY⟩)⁻¹ * (e ⟨y, hyY⟩)⁻¹ = 1 := by
    have h1 : (⟨y, hyY⟩ : ↥Y) * ⟨x, hxY⟩ = ⟨x, hxY⟩ * ⟨y, hyY⟩ := Subtype.ext hxy
    have h2 : e ⟨y, hyY⟩ * e ⟨x, hxY⟩ = e ⟨x, hxY⟩ * e ⟨y, hyY⟩ := by
      rw [← map_mul, ← map_mul, h1]
    rw [← h2]
    group
  rw [ut3_comm] at hcomm
  have hc0 : (e ⟨x, hxY⟩).a * (e ⟨y, hyY⟩).b - (e ⟨y, hyY⟩).a * (e ⟨x, hxY⟩).b = 0 :=
    congrArg UT3.c hcomm
  suffices hWE : e ⟨y, hyY⟩ ∈ (E.subgroupOf Y).map e.toMonoidHom from
    (mem_map_subgroupOf_equiv_iff E e ⟨y, hyY⟩).1 hWE
  rcases equiv_image_eq_E1UT_or_E2UT e hEY hEs hE16 with h | h
  · rw [h] at hXE ⊢
    have hXb : (e ⟨x, hxY⟩).b = 0 := mem_E1UT.1 hXE
    have hXa : (e ⟨x, hxY⟩).a ≠ 0 := fun ha => hXZ (mem_ZUT.2 ⟨ha, hXb⟩)
    rw [hXb, mul_zero, sub_zero] at hc0
    exact mem_E1UT.2 ((mul_eq_zero.1 hc0).resolve_left hXa)
  · rw [h] at hXE ⊢
    have hXa : (e ⟨x, hxY⟩).a = 0 := mem_E2UT.1 hXE
    have hXb : (e ⟨x, hxY⟩).b ≠ 0 := fun hb => hXZ (mem_ZUT.2 ⟨hXa, hb⟩)
    rw [hXa, zero_mul, zero_sub, neg_eq_zero] at hc0
    exact mem_E2UT.2 ((mul_eq_zero.1 hc0).resolve_right hXb)

theorem centralizer_noncentral {G : Type*} [Group G] {Y U E₁ E₂ : Subgroup G} (e : ↥Y ≃* UT3 F4)
    (hUY : U ≤ Y) (hU4 : Nat.card ↥U = 4) (hUN : ∀ y ∈ Y, ∀ w ∈ U, y * w * y⁻¹ ∈ U)
    (h₁Y : E₁ ≤ Y) (h₂Y : E₂ ≤ Y)
    (hE₁c : ∀ a ∈ E₁, ∀ b ∈ E₁, a * b = b * a) (hE₁s : ∀ a ∈ E₁, a * a = 1)
    (hE₂c : ∀ a ∈ E₂, ∀ b ∈ E₂, a * b = b * a) (hE₂s : ∀ a ∈ E₂, a * a = 1)
    (hc₁ : Nat.card ↥E₁ = 16) (hc₂ : Nat.card ↥E₂ = 16) (hint : E₁ ⊓ E₂ = U) (hprod : E₁ ⊔ E₂ = Y)
    (hinv : ∀ y ∈ Y, y * y = 1 → y ∈ E₁ ∨ y ∈ E₂) :
    (∀ x ∈ E₁, x ∉ U → ∀ y ∈ Y, y * x = x * y → y ∈ E₁) ∧
    (∀ x ∈ E₂, x ∉ U → ∀ y ∈ Y, y * x = x * y → y ∈ E₂) :=
  ⟨centralizer_of_noncentral_of_card_sixteen e hUY hU4 hUN h₁Y hE₁s hc₁,
    centralizer_of_noncentral_of_card_sixteen e hUY hU4 hUN h₂Y hE₂s hc₂⟩

theorem sq_mem_of_equiv {G : Type*} [Group G] {Y U : Subgroup G} (e : ↥Y ≃* UT3 F4) (hUY : U ≤ Y)
    (hU4 : Nat.card ↥U = 4) (hUN : ∀ y ∈ Y, ∀ w ∈ U, y * w * y⁻¹ ∈ U) :
    ∀ y ∈ Y, y * y ∈ U := by
  intro y hy
  have h1 : e (⟨y, hy⟩ * ⟨y, hy⟩) ∈ ZUT := by
    rw [map_mul, ut3_sq]
    exact mem_ZUT.2 ⟨rfl, rfl⟩
  have := (equiv_mem_ZUT_iff_mem_normal_four e hUY hU4 hUN _).1 h1
  simpa using this

end Transport3

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
