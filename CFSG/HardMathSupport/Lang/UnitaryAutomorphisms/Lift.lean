module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open scoped commutatorElement

variable {L : Type*} [Group L]

theorem central_conj {z : L} (hz : z ∈ Subgroup.center L) (x : L) : z * x * z⁻¹ = x := by
  rw [← Subgroup.mem_center_iff.mp hz x]
  group

theorem comm_central_mul_left {z : L} (hz : z ∈ Subgroup.center L) (a b : L) :
    ⁅z * a, b⁆ = ⁅a, b⁆ := by
  have := central_conj hz (a * b * a⁻¹)
  calc ⁅z * a, b⁆ = (z * (a * b * a⁻¹) * z⁻¹) * b⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [this]; simp only [commutatorElement_def]

theorem comm_central_mul_right {z : L} (hz : z ∈ Subgroup.center L) (a b : L) :
    ⁅a, z * b⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv, comm_central_mul_left hz, commutatorElement_inv]

theorem fixed_of_mem_commutator (α : L ≃* L) (W : Subgroup L)
    (hfix : ∀ w ∈ W, α w * w⁻¹ ∈ Subgroup.center L) :
    ∀ c ∈ ⁅W, W⁆, α c = c := by
  have key : ⁅W, W⁆ ≤ MonoidHom.eqLocus (α : L →* L) (MonoidHom.id L) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨za, hza, hza'⟩ : ∃ z ∈ Subgroup.center L, α a = z * a :=
      ⟨α a * a⁻¹, hfix a ha, by group⟩
    obtain ⟨zb, hzb, hzb'⟩ : ∃ z ∈ Subgroup.center L, α b = z * b :=
      ⟨α b * b⁻¹, hfix b hb, by group⟩
    show α ⁅a, b⁆ = ⁅a, b⁆
    rw [map_commutatorElement, hza', hzb', comm_central_mul_left hza,
      comm_central_mul_right hzb]
  intro c hc
  exact key hc

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
