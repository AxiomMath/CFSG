module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.IsoOn

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

variable {G : Type} [Group G]

theorem IsIsoOn.map_mem_pCoreOf {K : Subgroup G} {φ : G → G} (hφ : IsIsoOn K K φ) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 K) : φ x ∈ CFSG.Open.pCoreOf 2 K := by
  let e : ↥K ≃* ↥K := hφ.toMulEquiv
  have he : ∀ u : ↥K, (e u : G) = φ u := fun u => hφ.toMulEquiv_apply u
  change x ∈ (CFSG.pCore 2 ↥K).map K.subtype at hx
  change φ x ∈ (CFSG.pCore 2 ↥K).map K.subtype
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_map.mpr ⟨e y, ?_, ?_⟩
  · rw [← CFSG.pCore_map_iso 2 e]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hy
  · change (e y : G) = φ x
    rw [he y]
    exact congrArg φ hyx

end CFSG.EvenSporadicStandard.HNRecog.Section4
