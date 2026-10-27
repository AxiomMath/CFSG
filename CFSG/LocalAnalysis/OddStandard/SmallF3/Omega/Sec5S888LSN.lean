module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Ctx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888F2A

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

section Quad

variable {G : Type} [Group G] {K : Fin 4 → Subgroup G} {z : G}

theorem Sec5B517Quad.not_le_pair (hq : Sec5B517Quad K z) {a b l : Fin 4} (hla : l ≠ a)
    (hlb : l ≠ b) : ¬ K l ≤ K a ⊔ K b := by
  intro hle
  obtain ⟨u, hu, hu2⟩ := hq.exists_sq l
  have hcomm : ∀ v ∈ K l, u * v = v * u := by
    intro v hv
    have hle' := hq.le_centralizer_of_mem_pair hla hlb (hle hu)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle' hv)).symm
  rcases hq.eq_of_central hu hcomm with h1 | hz
  · rw [h1, one_mul] at hu2
    exact hq.z_ne hu2.symm
  · rw [hz, hq.z_sq] at hu2
    exact hq.z_ne hu2.symm

end Quad

section Ctx

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

theorem l515S_pocket_not_le_L (h514 : Asc82Lemma514) (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {j : Fin 4} (hj : j = 2 ∨ j = 3) : ¬ Kfam5 K₁ K₂ h j ≤ L := by
  intro hle
  have hq : Sec5B517Quad (Kfam5 K₁ K₂ h) z := sec5b517_quad h514 c
  have hK0 : Kfam5 K₁ K₂ h 0 = K₁ := by simp [Kfam5]
  have hK1 : Kfam5 K₁ K₂ h 1 = K₂ := by simp [Kfam5]
  have hle2 : Kfam5 K₁ K₂ h j ≤ K₁ ⊔ K₂ := by
    refine sec5_le_of_odd (Classical.choice (hq.iso j)) fun x hx hodd => ?_
    rw [c.prod]
    refine Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨hle hx, ?_⟩, hodd⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hq.z_comm hx).symm
  have hle3 : Kfam5 K₁ K₂ h j ≤ Kfam5 K₁ K₂ h 0 ⊔ Kfam5 K₁ K₂ h 1 := by
    rw [hK0, hK1]
    exact hle2
  have hj0 : j ≠ 0 := by rcases hj with rfl | rfl <;> decide
  have hj1 : j ≠ 1 := by rcases hj with rfl | rfl <;> decide
  exact hq.not_le_pair hj0 hj1 hle3

end Ctx

end CFSG.OddStandard.SmallF3.Omega
