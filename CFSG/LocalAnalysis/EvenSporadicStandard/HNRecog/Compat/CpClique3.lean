module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Lines

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

variable {G : Type} [Group G] {c u v w : G}

theorem cp_isConj_conj {c x : G} (hx : IsConj c x) (g : G) : IsConj c (g * x * g⁻¹) :=
  hx.trans (isConj_iff.2 ⟨g, rfl⟩)

theorem cp_isConj_mul_comm (c u v : G) : IsConj c (u * v) ↔ IsConj c (v * u) := by
  have h : IsConj (u * v) (v * u) := isConj_iff.2 ⟨u⁻¹, by group⟩
  exact ⟨fun h1 => h1.trans h, fun h1 => h1.trans h.symm⟩

theorem IsClique3.swap12 (h : IsClique3 c u v w) : IsClique3 c v u w := by
  obtain ⟨⟨huv, h1⟩, ⟨huw, h2⟩, ⟨hvw, h3⟩⟩ := h
  exact ⟨⟨huv.symm, (cp_isConj_mul_comm c u v).1 h1⟩, ⟨hvw, h3⟩, ⟨huw, h2⟩⟩

theorem IsClique3.rotate (h : IsClique3 c u v w) : IsClique3 c v w u := by
  obtain ⟨⟨huv, h1⟩, ⟨huw, h2⟩, ⟨hvw, h3⟩⟩ := h
  exact ⟨⟨hvw, h3⟩, ⟨huv.symm, (cp_isConj_mul_comm c u v).1 h1⟩,
    ⟨huw.symm, (cp_isConj_mul_comm c u w).1 h2⟩⟩

end CFSG.EvenSporadicStandard.HNRecog.Section4
