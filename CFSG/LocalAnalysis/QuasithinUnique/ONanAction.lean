module

public import CFSG.LocalAnalysis.QuasithinUnique.ONanBasic

public section

namespace CFSG.QuasithinUnique.ONan

open Module
open scoped Pointwise

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {X R : Subgroup (V ≃ₗ[ZMod 2] V)} {A C : Submodule (ZMod 2) V}

omit [Finite V] in
theorem mem_smul_iff (x : V ≃ₗ[ZMod 2] V) (D : Submodule (ZMod 2) V) (v : V) :
    v ∈ x • D ↔ x⁻¹ v ∈ D := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro h
    exact ⟨x⁻¹ v, h, by simp⟩

omit [Finite V] in
theorem finrank_smul (x : V ≃ₗ[ZMod 2] V) (D : Submodule (ZMod 2) V) :
    finrank (ZMod 2) (x • D : Submodule (ZMod 2) V) = finrank (ZMod 2) D :=
  LinearEquiv.finrank_map_eq x D

theorem Setting.finrank_space (S : Setting X R A C) :
    finrank (ZMod 2) V = finrank (ZMod 2) A + finrank (ZMod 2) C := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq A C
  rw [S.isCompl.sup_eq_top, S.isCompl.inf_eq_bot, finrank_top, finrank_bot] at h
  omega

omit [Finite V] in
theorem Setting.smul_C (S : Setting X R A C) {r : V ≃ₗ[ZMod 2] V} (hr : r ∈ R) : r • C = C := by
  ext v
  rw [mem_smul_iff]
  constructor
  · intro h
    have h1 : r (r⁻¹ v) = r⁻¹ v := S.fixes r hr _ h
    have h2 : r (r⁻¹ v) = v := by simp
    rw [h2] at h1
    rw [h1]
    exact h
  · intro h
    have h1 : r⁻¹ v = v := S.fixes r⁻¹ (R.inv_mem hr) v h
    rw [h1]
    exact h

theorem Setting.smul_A (S : Setting X R A C) {r : V ≃ₗ[ZMod 2] V} (hr : r ∈ R) : r • A = A := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro v hv
    obtain ⟨a, ha, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hv
    exact S.preserves r hr a ha
  · exact finrank_smul r A

theorem Setting.exists_ne_one (S : Setting X R A C) (hA : 2 ≤ finrank (ZMod 2) A) :
    ∃ ρ ∈ R, ρ ≠ 1 := by
  obtain ⟨a, ha, ha0, -⟩ := exists_mem_ne_two A hA 0 0
  obtain ⟨b, hb, hb0, hba⟩ := exists_mem_ne_two A hA 0 a
  obtain ⟨r, hr, hra⟩ := S.trans a ha b hb ha0 hb0
  refine ⟨r, hr, fun h => hba ?_⟩
  rw [← hra, h]
  rfl

end CFSG.QuasithinUnique.ONan
