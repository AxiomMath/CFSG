module

public import CFSG.ClassicalInvolution.Q3.TL3T10

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c

open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section Transport

variable {G G' : Type} [Group G] [Group G'] {P : Set (Subgroup G)} {P' : Set (Subgroup G')} {n : ℕ}

@[expose] noncomputable def transportIdent (ψ : ↥(pSpan P) ≃* ↥(pSpan P'))
    (h1 : ∀ L ∈ P, ∃ L' ∈ P', (L.subgroupOf (pSpan P)).map ψ.toMonoidHom = L'.subgroupOf (pSpan P'))
    (h2 : ∀ L' ∈ P', ∃ L ∈ P, (L.subgroupOf (pSpan P)).map ψ.toMonoidHom = L'.subgroupOf (pSpan P'))
    (I : AEIdent P' n) : AEIdent P n where
  φ := I.φ.comp ψ.toMonoidHom
  range_eq := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ψ.surjective, Subgroup.map_top, I.range_eq]
  ker_le := by
    intro x hx
    have hx' : ψ x ∈ I.φ.ker := hx
    have hc := Subgroup.mem_center_iff.mp (I.ker_le hx')
    refine Subgroup.mem_center_iff.mpr fun z => ?_
    apply ψ.injective
    rw [map_mul, map_mul]
    exact hc (ψ z)
  label := by
    intro L hL
    obtain ⟨L', hL', hLL'⟩ := h1 L hL
    obtain ⟨α, h, b, hlab⟩ := I.label L' hL'
    refine ⟨α, h, b, ?_⟩
    show (L.subgroupOf (pSpan P)).map (I.φ.comp ψ.toMonoidHom) = _
    rw [← Subgroup.map_map, hLL', hlab]
  label_surj := by
    intro α h b
    obtain ⟨L', hL', hlab⟩ := I.label_surj α h b
    obtain ⟨L, hL, hLL'⟩ := h2 L' hL'
    refine ⟨L, hL, ?_⟩
    show (L.subgroupOf (pSpan P)).map (I.φ.comp ψ.toMonoidHom) = _
    rw [← Subgroup.map_map, hLL', hlab]

end Transport

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c
