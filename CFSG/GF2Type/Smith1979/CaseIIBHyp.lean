module

public import CFSG.GF2Type.Smith1979.CaseIIBRank

public section

namespace CFSG.GF2Type.Smith1979.Case2

namespace PhaseB

open Module QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V} {a : V} {E : Submodule (ZMod 2) V}
  {L : Subgroup (V ≃ₗ[ZMod 2] V)}

private theorem zmod2_cases' (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem Ctx.exists_Kbar [FiniteDimensional (ZMod 2) V] (C : Ctx q a E L)
    {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ L)
    (h6 : finrank (ZMod 2) (LinearMap.range ((t : V →ₗ[ZMod 2] V) - 1)) = 6) :
    ∃ Kb : Subgroup (V ≃ₗ[ZMod 2] V), Kb ≤ L ∧
      (∀ s ∈ L, s ∈ Kb ↔
        finrank (ZMod 2) (LinearMap.range ((s : V →ₗ[ZMod 2] V) - 1)) ≠ 6) ∧
      t ∉ Kb ∧ ∀ l ∈ L, l ∈ Kb ∨ t * l ∈ Kb := by
  obtain ⟨W, T, S, hW, h1, h2, h3, hSmem, hSsurj, hSadd, hS0, -, hrank⟩ := C.exists_model
  obtain ⟨w₀, hw₀⟩ := hSsurj t ht
  have hr0 : finrank (ZMod 2) (LinearMap.range (((S 0 : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - 1)) =
      0 := by
    rw [hS0]
    have : (((1 : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - 1) = 0 := by
      ext x
      simp
    rw [this, LinearMap.range_zero, finrank_bot]
  have hw₀ne : w₀ ≠ 0 := by
    rintro rfl
    rw [hw₀] at hr0
    omega
  have hrad : finrank (ZMod 2) (rad T w₀) = 1 := by
    have := hrank w₀ hw₀ne
    rw [hw₀, h6] at this
    omega
  obtain ⟨α, hα1, hα⟩ := exists_hyperplane_of_trilinear hW T h1 h2 h3 hrad
  have key : ∀ w, α w = 0 ↔
      finrank (ZMod 2) (LinearMap.range (((S w : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - 1)) ≠ 6 := by
    intro w
    by_cases hw : w = 0
    · subst hw
      rw [hr0, map_zero]
      simp
    · have hr := hrank w hw
      obtain ⟨hα3, hα1'⟩ := hα w
      rcases zmod2_cases' (α w) with h | h
      · have := hα3 h
        rw [h]
        simp only [true_iff, ne_eq]
        omega
      · have := hα1' h
        rw [h]
        simp only [one_ne_zero, false_iff, not_not]
        omega
  refine ⟨{ carrier := {s | ∃ w, α w = 0 ∧ S w = s}
            mul_mem' := ?_
            one_mem' := ⟨0, map_zero α, hS0⟩
            inv_mem' := ?_ }, ?_, ?_, ?_, ?_⟩
  · rintro _ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
    exact ⟨w + w', by rw [map_add, hw, hw', add_zero], hSadd w w'⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨w, hw, (inv_eq_of_mul_eq_one_right (C.mul_self _ (hSmem w))).symm⟩
  · rintro _ ⟨w, -, rfl⟩
    exact hSmem w
  · intro s hs
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (key w).mp hw
    · intro h
      obtain ⟨w, rfl⟩ := hSsurj s hs
      exact ⟨w, (key w).mpr h, rfl⟩
  · rintro ⟨w, hw, hwt⟩
    have := (key w).mp hw
    rw [hwt, h6] at this
    exact this rfl
  · intro l hl
    obtain ⟨w, rfl⟩ := hSsurj l hl
    rcases zmod2_cases' (α w) with h | h
    · exact Or.inl ⟨w, h, rfl⟩
    · refine Or.inr ⟨w₀ + w, ?_, ?_⟩
      · rw [map_add, hα1, h]
        decide
      · rw [hSadd, hw₀]

end PhaseB

end CFSG.GF2Type.Smith1979.Case2
