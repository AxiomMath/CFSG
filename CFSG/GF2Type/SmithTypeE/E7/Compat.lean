module

public import CFSG.GF2Type.SmithTypeE.E7.ModDefs
public import CFSG.GF2Type.SmithTypeE.DMod.RhoTD6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.GF2Type.SmithTypeE.DMod (TD6 tvP tvP_mem rhoMod)

@[expose] def SmithE7Compat :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 16 →
    Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6) →
      ∃ (φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)) (ψ : S.Mbar ≃* ↥TD6),
        SmithE7Clauses1235 S φ ∧ SmithE7Clause4 S φ ∧
        (∀ (c : G) (hc : c ∈ S.M) (u : G), u ∈ S.QG →
            φ (S.cl (c * u * c⁻¹)) =
              rhoMod (ψ ⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩) (φ (S.cl u))) ∧
        (∀ (x : G) (hx : x ∈ S.M), IsConj S.z x → x ∉ S.QG →
          ∃ k : Fin 365211, ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩) ∧
        (∀ k : Fin 365211, ∃ (x : G) (hx : x ∈ S.M), IsConj S.z x ∧ x ∉ S.QG ∧
          ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩)

theorem smithE7Model_of_compat
    (h : SmithE7Compat) : SmithE7Model := by
  intro G _ _ _ S hw hO
  obtain ⟨φ, ψ, h1235, h4, -⟩ := h G S hw hO
  exact ⟨φ, h1235.1, h1235.2.1, h1235.2.2.1, h4, h1235.2.2.2⟩

end CFSG.GF2Type.SmithTypeE.E7
