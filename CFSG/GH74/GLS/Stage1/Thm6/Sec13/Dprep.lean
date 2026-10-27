module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.SylowB
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Grow
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Vocab

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

variable {G : Type*} [Group G]

@[expose] def Mm (V H : Subgroup G) : Subgroup G :=
  centralizer (V : Set G) ⊓ normalizer (H : Set G)

theorem exists_sylow_gt [Finite G] {V H : Subgroup G} (hH : IsPGroup 2 ↥H)
    (hHC : H ≤ centralizer (V : Set G)) (hns : ¬ Sylow2In H (centralizer (V : Set G))) :
    ∃ R : Subgroup G, SylowIn 2 R (Mm V H) ∧ H < R := by
  obtain ⟨P, hP, hHP⟩ := SylowIn.exists_ge (p := 2) hHC hH
  have hne : H ≠ P := by
    intro heq
    have : SylowIn 2 H (centralizer (V : Set G)) := heq ▸ hP
    exact hns this
  have hlt : H < P := lt_of_le_of_ne hHP hne
  obtain ⟨g, hgP, hgH, hgN⟩ := exists_mem_normalizer_not_mem hP.isPGroup hlt
  let R₁ : Subgroup G := normalizer (H : Set G) ⊓ P
  have hR₁M : R₁ ≤ Mm V H := fun a ha => ⟨hP.le ha.2, ha.1⟩
  have hR₁2 : IsPGroup 2 ↥R₁ := hP.isPGroup.to_le inf_le_right
  have hHR₁ : H ≤ R₁ := fun a ha => ⟨le_normalizer ha, hHP ha⟩
  obtain ⟨R, hR, hR₁R⟩ := SylowIn.exists_ge (p := 2) hR₁M hR₁2
  refine ⟨R, hR, lt_of_le_of_ne (hHR₁.trans hR₁R) ?_⟩
  intro heq
  have h1 : g ∈ R₁ := ⟨hgN, hgP⟩
  have h2 := hR₁R h1
  rw [← heq] at h2
  exact hgH h2

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
