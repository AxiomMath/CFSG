module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36Rows

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup GrSLit.L34Facts

theorem isTwoComponentIn_map_conj {Y : Type} [Group Y] [Finite Y] {J A : Subgroup Y}
    (hJ : IsTwoComponentIn J A) {c : Y} (hc : c ∈ A) :
    IsTwoComponentIn (J.map (MulAut.conj c).toMonoidHom) A := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact A.mul_mem (A.mul_mem hc (hJ.1 hx)) (A.inv_mem hc)
  · have heq : (J.map (MulAut.conj c).toMonoidHom).subgroupOf A =
        (J.subgroupOf A).map (MulAut.conj (⟨c, hc⟩ : ↥A)).toMonoidHom := by
      ext y
      rw [mem_subgroupOf, mem_map, mem_map]
      constructor
      · rintro ⟨x, hx, hxy⟩
        refine ⟨⟨x, hJ.1 hx⟩, hx, Subtype.ext ?_⟩
        rw [← hxy]
        rfl
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
    rw [heq]
    exact hJ.2.1.map (MulAut.conj (⟨c, hc⟩ : ↥A)).surjective
  · exact isTwoQuasisimple_of_mulEquiv
      (J.equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective) hJ.2.2

namespace Config

variable {G : Type} [Group G] [Finite G] {p m : ℕ} {τ : MulAut G} {K : Subgroup G}

theorem bar_normal (h : Config G p m τ K) :
    ((K.map (QuotientGroup.mk' (center G))).subgroupOf (fixedPoints (quotAut τ))).Normal := by
  refine ⟨fun n hn c => ?_⟩
  rw [mem_subgroupOf] at hn ⊢
  have hc := isTwoComponentIn_map_conj h.isTwoComponentIn_bar c.2
  have heq := h.eq_bar hc
  rw [← heq]
  exact ⟨n, hn, by simp [MulAut.conj_apply]⟩

end Config

end CFSG.ComponentClassification.HarrisLit.N36
