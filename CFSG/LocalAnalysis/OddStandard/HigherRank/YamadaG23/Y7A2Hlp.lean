module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G]

theorem y7a_conj_mem_centralizer {X : Subgroup G} {k m : G}
    (hk : k ∈ normalizer (X : Set G)) (hm : m ∈ centralizer (X : Set G)) :
    k * m * k⁻¹ ∈ centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hm ⊢
  intro f hf
  have hkf : k⁻¹ * f * k ∈ X := (Subgroup.mem_normalizer_iff''.mp hk f).mp hf
  calc f * (k * m * k⁻¹) = k * ((k⁻¹ * f * k) * m) * k⁻¹ := by group
    _ = k * (m * (k⁻¹ * f * k)) * k⁻¹ := by rw [hm (k⁻¹ * f * k) hkf]
    _ = (k * m * k⁻¹) * f := by group

theorem y7a_conj_mem_centIn {V X : Subgroup G} {k m : G}
    (hV : ∀ a ∈ V, k * a * k⁻¹ ∈ V) (hkX : k ∈ normalizer (X : Set G))
    (hm : m ∈ centIn V X) : k * m * k⁻¹ ∈ centIn V X :=
  Subgroup.mem_inf.mpr
    ⟨hV m (Subgroup.mem_inf.mp hm).1,
      y7a_conj_mem_centralizer hkX (Subgroup.mem_inf.mp hm).2⟩

theorem y7a_conj_mem_cen {T : Subgroup G} {k m : G}
    (hk : k ∈ normalizer (T : Set G)) (hm : m ∈ cen T) : k * m * k⁻¹ ∈ cen T :=
  Subgroup.mem_inf.mpr
    ⟨(Subgroup.mem_normalizer_iff.mp hk m).mp (Subgroup.mem_inf.mp hm).1,
      y7a_conj_mem_centralizer hk (Subgroup.mem_inf.mp hm).2⟩

end CFSG.OddStandard.HigherRank.YamadaG23
