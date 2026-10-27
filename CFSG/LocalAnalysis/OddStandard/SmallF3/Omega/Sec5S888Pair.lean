module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Q
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

structure Sec5Pair (K₁ K₂ : Subgroup G) (z : G) : Prop where
  comm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a
  iso₁ : Nonempty (↥K₁ ≃* SL23)
  iso₂ : Nonempty (↥K₂ ≃* SL23)
  z_mem₁ : z ∈ K₁
  z_mem₂ : z ∈ K₂
  z_sq : z * z = 1
  z_ne : z ≠ 1

theorem Sec5Pair.symm {K₁ K₂ : Subgroup G} {z : G} (h : Sec5Pair K₁ K₂ z) :
    Sec5Pair K₂ K₁ z := by
  exact ⟨fun a ha b hb => (h.comm b hb a ha).symm, h.iso₂, h.iso₁, h.z_mem₂, h.z_mem₁,
    h.z_sq, h.z_ne⟩

theorem Sec5Pair.ne {K₁ K₂ : Subgroup G} {z : G} (h : Sec5Pair K₁ K₂ z) : K₁ ≠ K₂ := by
  intro heq
  obtain ⟨a, ha, ha2⟩ :=
    sec5b517_exists_sq (Classical.choice h.iso₁) h.z_mem₁ h.z_sq h.z_ne
  have hcomm : ∀ v ∈ K₁, a * v = v * a := fun v hv => h.comm a ha v (heq ▸ hv)
  rcases sec5b517_central (Classical.choice h.iso₁) h.z_mem₁ h.z_sq h.z_ne ha hcomm with
    h1 | hz
  · rw [h1, one_mul] at ha2
    exact h.z_ne ha2.symm
  · rw [hz] at ha2
    exact h.z_ne (by rw [← ha2, h.z_sq])

theorem Sec5Pair.of_quad {K : Fin 4 → Subgroup G} {z : G} (hq : Sec5B517Quad K z) {i j : Fin 4}
    (hij : i ≠ j) : Sec5Pair (K i) (K j) z := by
  exact ⟨hq.comm i j hij, hq.iso i, hq.iso j, hq.z_mem i, hq.z_mem j, hq.z_sq, hq.z_ne⟩

theorem Sec5Pair.of_kctx [Finite G] {t : G} {L S : Subgroup G} {z r : G} {B A K₁ K₂ : Subgroup G}
    (c : Sec5KCtx G t L S z r B A K₁ K₂) : Sec5Pair K₁ K₂ z := by
  refine ⟨?_, c.iso₁, c.iso₂, c.pocket₁.1, c.pocket₂.1, ?_, ?_⟩
  · intro a ha b hb
    have hmem : ⁅a, b⁆ ∈ ⁅K₁, K₂⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [c.comm, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  · have hz2 : orderOf z = 2 := c.pocket.1
    rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  · intro h1
    have hz2 : orderOf z = 2 := c.pocket.1
    rw [h1, orderOf_one] at hz2
    omega

theorem Sec5Pair.comm_z₁ {K₁ K₂ : Subgroup G} {z : G} (h : Sec5Pair K₁ K₂ z) :
    ∀ x ∈ K₁, x * z = z * x := by
  intro x hx
  exact h.comm x hx z h.z_mem₂

theorem Sec5Pair.comm_z₂ {K₁ K₂ : Subgroup G} {z : G} (h : Sec5Pair K₁ K₂ z) :
    ∀ x ∈ K₂, x * z = z * x := by
  intro x hx
  exact (h.comm z h.z_mem₁ x hx).symm

theorem Sec5Pair.le_centralizer {K₁ K₂ : Subgroup G} {z : G} (h : Sec5Pair K₁ K₂ z) :
    K₁ ⊔ K₂ ≤ centralizer ({z} : Set G) := by
  apply sup_le
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h.comm_z₁ x hx
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h.comm_z₂ x hx

theorem Sec5Pair.inf_eq {K₁ K₂ : Subgroup G} {z : G} (h : Sec5Pair K₁ K₂ z) {x : G}
    (h₁ : x ∈ K₁) (h₂ : x ∈ K₂) : x = 1 ∨ x = z := by
  have hcomm : ∀ v ∈ K₁, x * v = v * x := fun v hv => (h.comm v hv x h₂).symm
  exact sec5b517_central (Classical.choice h.iso₁) h.z_mem₁ h.z_sq h.z_ne h₁ hcomm

end CFSG.OddStandard.SmallF3.Omega
