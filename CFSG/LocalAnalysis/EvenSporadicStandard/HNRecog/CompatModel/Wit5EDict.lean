module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Dict

public section

namespace CFSG.EvenSporadicStandard.HNRecog.CompatModel

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.EvenSporadicStandard.HNRecog.Section3Model CFSG.EvenSporadicStandard.HNRecog.Section4

section Cert


theorem exists_vertexIso_at_pZ₁ {G : Type} [Group G] {a z : G} (h : F5Std a z) {d y : G}
    (hd : IsConj a d) (hy : y ∈ orb2BB a z d) :
    ∃ hyd : y ∈ Gx d, ∃ Ψ : ↥(Gx d) ≃* ↥P1408, VertexIso d z Ψ ∧ Ψ ⟨y, hyd⟩ = pZ₁ := by
  have hyd : y ∈ Gx d := h.mem_Gx_of_orb2BB hd hy
  obtain ⟨E, z₀, b₀, u₀, hE, L, hD⟩ := exists_hSideData_at h hd
  have hyu : IsConj u₀ (⟨y, hyd⟩ : ↥(Gx d)) := by
    have hB : IsConj z₀ (⟨y, hyd⟩ : ↥(Gx d)) ∨ IsConj u₀ (⟨y, hyd⟩ : ↥(Gx d)) :=
      (L.isB_iff ⟨y, hyd⟩).2 hy.1
    rcases hB with h1 | h1
    · exact absurd (((L.isConj_z₀_iff (t := ⟨y, hyd⟩) hy.1).1 h1).trans hy.2.symm) L.not_conj
    · exact h1
  obtain ⟨Ψ₀, hΨ₀, -⟩ := exists_labelled_iso_dict hE L.facts hD
  have hz : IsConj pZ₁ (Ψ₀ ⟨y, hyd⟩) :=
    hΨ₀.z₁_conj.trans (TwoHSData.isConj_map_mulEquiv Ψ₀ hyu)
  obtain ⟨Ψ, hΨ, hΨy⟩ := hΨ₀.exists_eq hz
  exact ⟨hyd, Ψ, vertexIso_of_labelled L hΨ, hΨy⟩

end Cert

end CFSG.EvenSporadicStandard.HNRecog.CompatModel
