module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveTwoGroups

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2

open Subgroup CFSG.ComponentClassification.AschbacherTheorem5.SectionSix.TwoGroups

section Generic

variable {T D : Type*} [Group T] [Group D]

theorem exists_dihedral_pair (ι : T →* D) (hι : Function.Injective ι) (A : Subgroup D)
    (hA : A.index = 2) [IsCyclic A] (hinv : ∀ σ ∉ A, ∀ x ∈ A, σ * x * σ⁻¹ = x⁻¹) {u₀ : T}
    (hu₀ : ι u₀ ∉ A) :
    ∃ ρ σ : T, Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ = ⊤ ∧ ι σ ∉ A ∧ σ * ρ * σ⁻¹ = ρ⁻¹ := by
  set A₀ : Subgroup T := A.comap ι with hA₀
  have hA₀c : IsCyclic ↥A₀ := by
    refine isCyclic_of_injective ((ι.comp A₀.subtype).codRestrict A fun x => x.2) ?_
    intro x y hxy
    exact Subtype.ext (hι (congrArg Subtype.val hxy))
  obtain ⟨g, hg⟩ := hA₀c.exists_generator
  have hmemρ : ∀ x : T, ι x ∈ A → x ∈ Subgroup.zpowers (g : T) := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, congrArg Subtype.val hk⟩
  refine ⟨(g : T), u₀, ?_, hu₀, ?_⟩
  · rw [eq_top_iff]
    intro x _
    by_cases hx : ι x ∈ A
    · exact Subgroup.mem_sup_left (hmemρ x hx)
    · have hinvu : (ι u₀)⁻¹ ∉ A := fun h => hu₀ (by simpa using A.inv_mem h)
      have hxu : ι x * (ι u₀)⁻¹ ∈ A :=
        (Subgroup.mul_mem_iff_of_index_two hA).mpr (iff_of_false hx hinvu)
      have hxu' : x * u₀⁻¹ ∈ Subgroup.zpowers (g : T) :=
        hmemρ _ (by rw [map_mul, map_inv]; exact hxu)
      have : x = (x * u₀⁻¹) * u₀ := by group
      rw [this]
      exact Subgroup.mul_mem_sup hxu' (Subgroup.mem_zpowers u₀)
  · apply hι
    rw [map_mul, map_mul, map_inv, map_inv]
    exact hinv _ hu₀ _ g.2

end Generic

section Dihedral

open DihedralGroup

theorem dihedral_hinv {k : ℕ} [NeZero k] :
    ∀ σ ∉ Subgroup.zpowers (r 1 : DihedralGroup k), ∀ x ∈ Subgroup.zpowers (r 1 : DihedralGroup k),
      σ * x * σ⁻¹ = x⁻¹ := by
  intro σ hσ x hx
  obtain ⟨i, rfl⟩ := (mem_zpowers_r_one_iff x).1 hx
  cases σ with
  | r j => exact absurd ((mem_zpowers_r_one_iff _).2 ⟨j, rfl⟩) hσ
  | sr j => rw [sr_mul_r, inv_sr, sr_mul_sr, inv_r]; congr 1; ring

end Dihedral

section Quaternion

open QuaternionGroup

theorem quaternion_hinv {m : ℕ} [NeZero m] :
    ∀ σ ∉ Subgroup.zpowers (a 1 : QuaternionGroup m),
      ∀ x ∈ Subgroup.zpowers (a 1 : QuaternionGroup m), σ * x * σ⁻¹ = x⁻¹ := by
  intro σ hσ x hx
  obtain ⟨i, rfl⟩ := (mem_zpowers_a_one_iff x).1 hx
  cases σ with
  | a j => exact absurd ((mem_zpowers_a_one_iff _).2 ⟨j, rfl⟩) hσ
  | xa j =>
    have h1 : (a i)⁻¹ = a (-i) := by
      apply inv_eq_of_mul_eq_one_right
      rw [a_mul_a, add_neg_cancel, a_zero]
    have h2 : (xa j)⁻¹ = xa ((m : ZMod (2 * m)) + j) := by
      apply inv_eq_of_mul_eq_one_right
      rw [xa_mul_xa, ← a_zero]
      congr 1
      have : (2 * m : ZMod (2 * m)) = 0 := by
        rw [show (2 * m : ZMod (2 * m)) = ((2 * m : ℕ) : ZMod (2 * m)) by push_cast; rfl]
        exact ZMod.natCast_self _
      linear_combination this
    rw [h1, h2, xa_mul_a, xa_mul_xa]
    congr 1
    have : (2 * m : ZMod (2 * m)) = 0 := by
      rw [show (2 * m : ZMod (2 * m)) = ((2 * m : ℕ) : ZMod (2 * m)) by push_cast; rfl]
      exact ZMod.natCast_self _
    linear_combination this

end Quaternion

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2
