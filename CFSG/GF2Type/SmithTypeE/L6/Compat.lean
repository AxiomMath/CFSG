module

public import CFSG.GF2Type.SmithTypeE.L6.Defs
public import CFSG.GF2Type.SmithTypeE.LMod.RhoT6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.GF2Type.SmithTypeE.LMod (T6 tvP tvP_mem rhoMod)
open scoped MatrixGroups

@[expose] def SmithL6Compat :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)) →
      ∃ (φ : S.Qt ≃ₗ[ZMod 2] (Fin 20 → ZMod 2)) (ψ : Mbar0 S ≃* ↥T6),
        SmithL6Clauses1235 S φ ∧ SmithL6Clause4 S φ ∧
        (∀ (c : G) (hc : c ∈ S.M)
          (h0 : (⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩ : S.Mbar) ∈ Mbar0 S) (u : G), u ∈ S.QG →
            φ (S.cl (c * u * c⁻¹)) =
              rhoMod (ψ ⟨⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩, h0⟩) (φ (S.cl u))) ∧
        (∀ (x : G) (hx : x ∈ S.M), IsConj S.z x → x ∉ S.QG →
          ∃ (k : Fin 1953) (h0 : (⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ : S.Mbar) ∈ Mbar0 S),
            ψ ⟨⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩, h0⟩ = ⟨tvP k, tvP_mem k⟩) ∧
        (∀ k : Fin 1953, ∃ (x : G) (hx : x ∈ S.M), IsConj S.z x ∧ x ∉ S.QG ∧
          ∃ h0 : (⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ : S.Mbar) ∈ Mbar0 S,
            ψ ⟨⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩, h0⟩ = ⟨tvP k, tvP_mem k⟩)

theorem smithL6Model_of_compat
    (h : SmithL6Compat) : SmithL6Model := by
  intro G _ _ _ S hw hU
  obtain ⟨φ, ψ, h1235, h4, -⟩ := h G S hw hU
  exact ⟨φ, h1235.1, h1235.2.1, h1235.2.2.1, h4, h1235.2.2.2⟩

end CFSG.GF2Type.SmithTypeE.L6
