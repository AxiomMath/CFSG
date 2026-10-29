module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.QzBasic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem tableIII_five_type {a z : G} (h : IsF5Type a z) (hSGz : StructGzFacts a z)
    {ρ : ↥(Gx z)} (hρ : orderOf ρ = 5) {q : G} (hq : q ∈ Qz z) (hq1 : q ≠ 1) (hqz : q ≠ z)
    (hρq : (ρ : G) * q = q * ρ) :
    IsShapeZpTimesZp 5 ↥(CbarCent z ρ) ∧ IsMinusExtraspecial 2 (Qz z ⊓ Gx (ρ : G)) := by
  have hqmem : q ∈ Qz z ⊓ Gx (ρ : G) := Subgroup.mem_inf.2 ⟨hq, mem_Gx.2 hρq⟩
  have hnot : q ∉ Subgroup.zpowers z := by
    rw [tableIII_mem_zpowers_iff h]
    push Not
    exact ⟨hq1, hqz⟩
  rcases hSGz.five.1 ρ hρ with ⟨-, h1⟩ | h2 | ⟨-, h3⟩
  · exact absurd (h1 ▸ hqmem) hnot
  · exact h2
  · exact absurd (h3 ▸ hqmem) hnot

end CFSG.EvenSporadicStandard.HNRecog.Section3
