module

public import CFSG.GroupTheory.ThreeTranspositions.FischerResidual

public section

namespace CFSG.GroupTheory.ThreeTranspositions

variable {X : Type} [Group X]

theorem mem_threeResidualJoin_self (d : X) : d ∈ threeResidualJoin d :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers d)

@[expose] def residualSelf (d : X) : ↥(threeResidualJoin d) :=
  ⟨d, mem_threeResidualJoin_self d⟩

@[simp]
theorem residualSelf_coe (d : X) : (residualSelf d : X) = d :=
  rfl

@[expose] noncomputable def residualProj (d : X) :
    ↥(threeResidualJoin d) →* ↥(threeResidualQuot d) :=
  (QuotientGroup.mk' (Subgroup.center X)).subgroupMap (threeResidualJoin d)

theorem residualProj_apply (d : X) (x : ↥(threeResidualJoin d)) :
    ((residualProj d x : ↥(threeResidualQuot d)) : X ⧸ Subgroup.center X) =
      QuotientGroup.mk (x : X) := by
  unfold residualProj threeResidualQuot
  rw [MonoidHom.subgroupMap_apply_coe, QuotientGroup.mk'_apply]

theorem residualProj_surjective (d : X) : Function.Surjective (residualProj d) := by
  unfold residualProj threeResidualQuot
  exact (QuotientGroup.mk' (Subgroup.center X)).subgroupMap_surjective (threeResidualJoin d)

theorem residualProj_ker_le_center (d : X) :
    (residualProj d).ker ≤ Subgroup.center ↥(threeResidualJoin d) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hxZ : (x : X) ∈ Subgroup.center X := by
    have hxq : (QuotientGroup.mk (x : X) : X ⧸ Subgroup.center X) = 1 := by
      rw [← residualProj_apply d x, MonoidHom.mem_ker.mp hx]
      simp
    exact (QuotientGroup.eq_one_iff (x : X)).1 hxq
  exact Subgroup.mem_center_iff.mp hxZ (y : X)

theorem odd_card_ker_residualProj [Finite X] (d : X)
    (hodd : Odd (Nat.card (Subgroup.center X))) :
    Odd (Nat.card (residualProj d).ker) := by
  let φ : ↥(residualProj d).ker →* ↥(Subgroup.center X) :=
    { toFun := fun x =>
        ⟨(x.1 : X), by
          have hxq : (QuotientGroup.mk (x.1 : X) : X ⧸ Subgroup.center X) = 1 := by
            rw [← residualProj_apply d x.1, MonoidHom.mem_ker.mp x.2]
            simp
          exact (QuotientGroup.eq_one_iff (x.1 : X)).1 hxq⟩
      map_one' := rfl
      map_mul' := by intro a b; ext; rfl }
  have hinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(Subgroup.center X) => (z : X)) hab
  exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_injective φ hinj)

@[expose] def residualClassW (d : X) : Set ↥(threeResidualJoin d) :=
  {w | ∃ g : ↥(threeResidualJoin d), w = g * residualSelf d * g⁻¹}

theorem residualClassW_conj_mem (d : X) {w : ↥(threeResidualJoin d)}
    (hw : w ∈ residualClassW d) (g : ↥(threeResidualJoin d)) :
    g * w * g⁻¹ ∈ residualClassW d := by
  obtain ⟨h, rfl⟩ := hw
  exact ⟨g * h, by group⟩

theorem image_residualProj_residualClassW (d : X) :
    residualProj d '' residualClassW d = threeResidualClass d := by
  ext q
  constructor
  · rintro ⟨w, ⟨g, rfl⟩, rfl⟩
    refine ⟨(g : X), g.2, ?_⟩
    rw [residualProj_apply]
    congr 1
  · rintro ⟨w, hw, hwq⟩
    refine ⟨⟨w, hw⟩ * residualSelf d * ⟨w, hw⟩⁻¹, ⟨⟨w, hw⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    rw [residualProj_apply]
    rw [← hwq]
    congr 1

end CFSG.GroupTheory.ThreeTranspositions
