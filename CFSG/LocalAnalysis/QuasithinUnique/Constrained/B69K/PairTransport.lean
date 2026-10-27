module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.Pair

public section

namespace CFSG.Quasithin

namespace B69K

theorem ParabolicPair.map_mulEquiv {C D : Type} [Group C] [Group D] (e : C ≃* D) {U : Subgroup C}
    (h : ParabolicPair U) : ParabolicPair (U.map e.toMonoidHom) := by
  obtain ⟨P₀, P₁, hU₀, hU₁, hP₀, hP₁, hgen, hinv⟩ := h
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have htop : ∀ P : Subgroup C, P.map e.toMonoidHom = ⊤ → P = ⊤ := by
    intro P hP
    rw [eq_top_iff]
    intro x _
    have hmem : e x ∈ P.map e.toMonoidHom := by
      rw [hP]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
    have hxy : y = x := e.injective hyx
    rw [← hxy]
    exact hy
  have hsurj : (⊤ : Subgroup C).map e.toMonoidHom = ⊤ := by
    rw [eq_top_iff]
    intro d _
    obtain ⟨c, rfl⟩ := e.surjective d
    exact Subgroup.mem_map.mpr ⟨c, Subgroup.mem_top c, rfl⟩
  refine ⟨P₀.map e.toMonoidHom, P₁.map e.toMonoidHom, Subgroup.map_mono hU₀,
    Subgroup.map_mono hU₁, fun h => hP₀ (htop P₀ h), fun h => hP₁ (htop P₁ h), ?_, ?_⟩
  · rw [← Subgroup.map_sup, hgen, hsurj]
  · intro α hα
    obtain ⟨β, hβdef⟩ : ∃ β : MulAut C, β = e.trans (α.trans e.symm) := ⟨_, rfl⟩
    have hcomp : α.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp β.toMonoidHom := by
      ext x
      simp [hβdef]
    have key : ∀ P : Subgroup C, (P.map e.toMonoidHom).map α.toMonoidHom =
        (P.map β.toMonoidHom).map e.toMonoidHom := by
      intro P
      rw [Subgroup.map_map, Subgroup.map_map, hcomp]
    have hβU : U.map β.toMonoidHom = U := by
      refine Subgroup.map_injective hinj ?_
      exact (key U).symm.trans hα
    exact ⟨by rw [key P₀, (hinv β hβU).1], by rw [key P₁, (hinv β hβU).2]⟩

end B69K

end CFSG.Quasithin

end
