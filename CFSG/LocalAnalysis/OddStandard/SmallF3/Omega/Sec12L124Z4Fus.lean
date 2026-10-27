module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}

theorem sec124_fusion (F : Sec12Frame t L S) {u l b : G} (hl : l ∈ L) (hb : b ∈ secB S L)
    (hlb : l⁻¹ * u * l = b) : ∃ h : G, h⁻¹ * t * h = t * u := by
  have htb : t * b ∈ conjClassIn ⊤ t := by
    have h1 : t * b ∈ secTB t S L := ⟨b, hb, rfl⟩
    rw [← F.alt1.1] at h1
    exact h1.1
  obtain ⟨g, -, hg⟩ := htb
  have hlt : l * t = t * l := Subgroup.mem_centralizer_iff.mp F.htC l hl
  have hu : u = l * b * l⁻¹ := by rw [← hlb]; group
  refine ⟨(l * g)⁻¹, ?_⟩
  calc (l * g)⁻¹⁻¹ * t * (l * g)⁻¹ = l * (g * t * g⁻¹) * l⁻¹ := by group
    _ = l * (t * b) * l⁻¹ := by rw [← hg]
    _ = (l * t) * b * l⁻¹ := by group
    _ = t * (l * b * l⁻¹) := by rw [hlt]; group
    _ = t * u := by rw [← hu]

end CFSG.OddStandard.SmallF3.Omega
