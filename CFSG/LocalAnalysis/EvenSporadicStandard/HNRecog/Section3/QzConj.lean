module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Transport

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G]

theorem Qz_conj_mem {x y : G} (c : G) (hy : y ∈ Qz x) : c * y * c⁻¹ ∈ Qz (c * x * c⁻¹) := by
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
  let f := centralizerMulEquiv (MulAut.conj c) (z := x) (w := c * x * c⁻¹) rfl
  have h1 : f y' ∈ CFSG.pCore 2 ↥(Gx (c * x * c⁻¹)) := by
    rw [← CFSG.pCore_map_iso 2 f]
    exact Subgroup.mem_map_of_mem _ hy'
  exact Subgroup.mem_map.mpr ⟨f y', h1, rfl⟩

theorem Qz_conj_mem_iff {x y : G} (c : G) : c * y * c⁻¹ ∈ Qz (c * x * c⁻¹) ↔ y ∈ Qz x := by
  refine ⟨fun h => ?_, Qz_conj_mem c⟩
  have := Qz_conj_mem (x := c * x * c⁻¹) c⁻¹ h
  simpa [mul_assoc] using this

end CFSG.EvenSporadicStandard.HNRecog.Section3
