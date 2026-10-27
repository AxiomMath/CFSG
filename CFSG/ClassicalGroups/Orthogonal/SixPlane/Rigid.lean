module

public import CFSG.ClassicalGroups.Orthogonal.SixPlane.Toral

import CFSG.ClassicalGroups.Orthogonal.SixPlane.Restrict

public section

namespace CFSG.ClassicalGroups.Orthogonal.SixPlane

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {n : ℕ}

theorem existsUnique_torus_of_mulEquiv {S : Finset (Fin n)} (hS : S.card = 4)
    (θ : ↥(supp n S) ≃* ↥(supp n S))
    (hθ : ∀ g : ↥(supp n S), (g : V n ≃ₗ[ZMod 2] V n) ∈ torus n S → θ g = g) :
    ∃! t : ↥(supp n S), (t : V n ≃ₗ[ZMod 2] V n) ∈ torus n S ∧ ∀ g, θ g = t * g * t⁻¹ := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have hrot : rot n i ∈ torus n S := Subgroup.subset_closure ⟨i, hi, rfl⟩
  obtain ⟨g, -, hgfix, hgθ⟩ :=
    exists_isometry_of_mulEquiv_fix_rot hS θ hi (hθ _ hrot)
  have hcomm : ∀ j ∈ S, Commute g (rot n j) := by
    intro j hj
    have hcoe : (θ ⟨rot n j, rot_mem_supp hj⟩ : V n ≃ₗ[ZMod 2] V n) = rot n j := by
      rw [hθ ⟨rot n j, rot_mem_supp hj⟩ (Subgroup.subset_closure ⟨j, hj, rfl⟩)]
    have hconj := hgθ ⟨rot n j, rot_mem_supp hj⟩
    rw [hcoe] at hconj
    rw [commute_iff_eq]
    calc g * rot n j = (g * rot n j * g⁻¹) * g := by group
      _ = rot n j * g := by rw [hconj.symm]
  have hgT : g ∈ torus n S := mem_torus_of_fix_compl_of_commute hgfix hcomm
  have hex : ∀ y : ↥(supp n S),
      θ y = ⟨g, torus_le_supp S hgT⟩ * y * ⟨g, torus_le_supp S hgT⟩⁻¹ := by
    intro y
    apply Subtype.ext
    simpa using hgθ y
  refine ⟨⟨g, torus_le_supp S hgT⟩, ⟨hgT, hex⟩, ?_⟩
  intro t' ht'
  obtain ⟨ht'T, ht'θ⟩ := ht'
  have hsub : ∀ y : ↥(supp n S),
      (⟨g, torus_le_supp S hgT⟩ : ↥(supp n S)) * y *
          (⟨g, torus_le_supp S hgT⟩ : ↥(supp n S))⁻¹ = t' * y * t'⁻¹ :=
    fun y => (hex y).symm.trans (ht'θ y)
  have hcongr : ∀ y : ↥(supp n S),
      (g : V n ≃ₗ[ZMod 2] V n) * (y : V n ≃ₗ[ZMod 2] V n) * g⁻¹ =
        (t' : V n ≃ₗ[ZMod 2] V n) * (y : V n ≃ₗ[ZMod 2] V n) *
          (t' : V n ≃ₗ[ZMod 2] V n)⁻¹ := by
    intro y
    simpa using congrArg (fun z : ↥(supp n S) => (z : V n ≃ₗ[ZMod 2] V n)) (hsub y)
  have hcommu : ∀ y ∈ supp n S,
      Commute ((t' : V n ≃ₗ[ZMod 2] V n)⁻¹ * g) y := by
    intro y hy
    rw [commute_iff_eq]
    calc (t' : V n ≃ₗ[ZMod 2] V n)⁻¹ * g * y
        = (t' : V n ≃ₗ[ZMod 2] V n)⁻¹ * (g * y * g⁻¹) * g := by group
      _ = (t' : V n ≃ₗ[ZMod 2] V n)⁻¹ *
            ((t' : V n ≃ₗ[ZMod 2] V n) * y * (t' : V n ≃ₗ[ZMod 2] V n)⁻¹) * g := by
          rw [hcongr ⟨y, hy⟩]
      _ = y * ((t' : V n ≃ₗ[ZMod 2] V n)⁻¹ * g) := by group
  have huT : (t' : V n ≃ₗ[ZMod 2] V n)⁻¹ * g ∈ torus n S :=
    (torus n S).mul_mem ((torus n S).inv_mem ht'T) hgT
  have hu0 : (t' : V n ≃ₗ[ZMod 2] V n)⁻¹ * g ∈ torus n (S \ S) :=
    mem_torus_sdiff_of_commute (S := S) (T := S) (by omega) huT hcommu
  have hempty : torus n (∅ : Finset (Fin n)) = ⊥ := by
    rw [torus, Finset.coe_empty, Set.image_empty, Subgroup.closure_empty]
  rw [Finset.sdiff_self, hempty] at hu0
  have hone : (t' : V n ≃ₗ[ZMod 2] V n)⁻¹ * g = 1 := Subgroup.mem_bot.mp hu0
  exact Subtype.ext (inv_mul_eq_one.mp hone)

end CFSG.ClassicalGroups.Orthogonal.SixPlane
