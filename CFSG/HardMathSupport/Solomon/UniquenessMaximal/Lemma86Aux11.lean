module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Vocab
public import CFSG.LocalAnalysis.GLTheoremB.PGroupBasics

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centerOf_iff {P : Subgroup G} {z : G} :
    z ∈ centerOf P ↔ z ∈ P ∧ ∀ y ∈ P, y * z = z * y := by
  constructor
  · rintro ⟨z', hz', rfl⟩
    refine ⟨z'.2, fun y hy => ?_⟩
    have := Subgroup.mem_center_iff.1 hz' ⟨y, hy⟩
    exact congrArg Subtype.val this
  · rintro ⟨hz, h⟩
    refine ⟨⟨z, hz⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext (h y y.2), rfl⟩

omit [Finite G] in
theorem centerOf_gLBConj (g : G) (P : Subgroup G) :
    centerOf (GLBConj g P) = GLBConj g (centerOf P) := by
  ext z
  rw [mem_centerOf_iff, mem_gLBConj, mem_gLBConj, mem_centerOf_iff]
  constructor
  · rintro ⟨hz, h⟩
    refine ⟨hz, fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ GLBConj g P := by
      rw [mem_gLBConj]; simpa [mul_assoc] using hy
    have := h _ hy'
    calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = (g * z * g⁻¹) * y := by group
  · rintro ⟨hz, h⟩
    refine ⟨hz, fun y hy => ?_⟩
    rw [mem_gLBConj] at hy
    have := h _ hy
    have e : g * (y * z) * g⁻¹ = g * (z * y) * g⁻¹ := by
      calc g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
        _ = (g * z * g⁻¹) * (g * y * g⁻¹) := this
        _ = g * (z * y) * g⁻¹ := by group
    simpa using e

theorem pRank_gLBConj {p : ℕ} (hp : 1 < p) (g : G) (H : Subgroup G) :
    CFSG.Open.pRank p (GLBConj g H) = CFSG.Open.pRank p H := by
  have h1 : CFSG.Open.pRank p H ≤ CFSG.Open.pRank p (GLBConj g H) :=
    CFSG.SectionRank.pRank_le_map hp (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective H
  have h2 : CFSG.Open.pRank p (GLBConj g H) ≤ CFSG.Open.pRank p H := by
    have := CFSG.SectionRank.pRank_le_map hp (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
      (GLBConj g H)
    have e : (GLBConj g H).map (MulAut.conj g).toMonoidHom = H := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have := (mem_gLBConj).1 hy
        simpa using this
      · intro hx
        exact ⟨g⁻¹ * x * g, (mem_gLBConj).2 (by simpa [mul_assoc] using hx), by
          show g * (g⁻¹ * x * g) * g⁻¹ = x
          group⟩
    rwa [e] at this
  exact le_antisymm h2 h1

theorem isUGroup_gLBConj {P U : Subgroup G} (hU : IsUGroup 2 P U) (g : G) :
    IsUGroup 2 (GLBConj g P) (GLBConj g U) := by
  obtain ⟨hUP, hPU, hplane, hcen⟩ := hU
  refine ⟨gLBConj_mono g hUP, ?_, isPPlane_gLBConj g hplane, ?_⟩
  · intro x hx
    rw [mem_gLBConj] at hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [mem_gLBConj, mem_gLBConj]
    have := Subgroup.mem_normalizer_iff.1 (hPU hx) (g * y * g⁻¹)
    rw [this]
    have e : (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * (x * y * x⁻¹) * g⁻¹ := by group
    rw [e]
  · intro h
    rw [centerOf_gLBConj, pRank_gLBConj Nat.one_lt_two] at h
    rw [centerOf_gLBConj]
    exact gLBConj_mono g (hcen h)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
