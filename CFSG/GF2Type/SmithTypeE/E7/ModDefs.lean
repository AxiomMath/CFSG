module

public import CFSG.GF2Type.SmithTypeE.DMod.Code
public import CFSG.LargeExtraspecial.S14Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.SmithD6 (wt adjW tvCols applyCols)
open CFSG.GF2Type.SmithTypeE.DMod (code32)

@[expose] def SmithE7Module : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 16 →
    Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6) →
      ∃ φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2),
        (∀ c : G, IsConj S.z c → c ∈ S.QG → c ≠ S.z → ∃ i < 75735, code32 (φ (S.cl c)) = wt i) ∧
        (∀ i < 75735, ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ code32 (φ (S.cl c)) = wt i) ∧
        (∀ h b : G, h * S.z * h⁻¹ ∈ S.QG → h * S.z * h⁻¹ ≠ S.z → IsConj S.z b → b ∈ S.QG →
          b ≠ S.z → ∀ i j, i < 75735 → j < 75735 → code32 (φ (S.cl (h * S.z * h⁻¹))) = wt i →
            code32 (φ (S.cl b)) = wt j → (b ∈ S.Qa h ↔ adjW i j = true)) ∧
        (∀ x : G, IsConj S.z x → x ∈ S.M → x ∉ S.QG → ∃ k < 365211, ∀ y ∈ S.QG,
          code32 (φ (S.cl (x * y * x⁻¹))) = applyCols (tvCols k) (code32 (φ (S.cl y))))

@[expose] def SmithE7Model : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 16 →
    Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6) →
      ∃ φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2),
        (∀ c : G, IsConj S.z c → c ∈ S.QG → c ≠ S.z → ∃ i < 75735, code32 (φ (S.cl c)) = wt i) ∧
        (∀ i < 75735, ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ code32 (φ (S.cl c)) = wt i) ∧
        (∀ h b : G, h * S.z * h⁻¹ ∈ S.QG → h * S.z * h⁻¹ ≠ S.z → IsConj S.z b → b ∈ S.QG →
          b ≠ S.z → ∀ i j, i < 75735 → j < 75735 → code32 (φ (S.cl (h * S.z * h⁻¹))) = wt i →
            code32 (φ (S.cl b)) = wt j → (b ∈ S.Qa h ↔ adjW i j = true)) ∧
        (∀ x : G, IsConj S.z x → x ∈ S.M → x ∉ S.QG → ∃ k < 365211, ∀ y ∈ S.QG,
          code32 (φ (S.cl (x * y * x⁻¹))) = applyCols (tvCols k) (code32 (φ (S.cl y)))) ∧
        (∀ k < 365211, ∃ m ∈ S.M, ∀ y ∈ S.QG,
          code32 (φ (S.cl (m * y * m⁻¹))) = applyCols (tvCols k) (code32 (φ (S.cl y))))

theorem smithE7Module_of_model (h : SmithE7Model) : SmithE7Module := by
  intro G _ _ _ S hw hO
  obtain ⟨φ, h1, h2, h3, h4, -⟩ := h G S hw hO
  exact ⟨φ, h1, h2, h3, h4⟩

variable {G : Type} [Group G]

@[expose] def SmithE7Clauses1235 (S : Setting G)
    (φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)) : Prop :=
  (∀ c : G, IsConj S.z c → c ∈ S.QG → c ≠ S.z → ∃ i < 75735, code32 (φ (S.cl c)) = wt i) ∧
  (∀ i < 75735, ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ code32 (φ (S.cl c)) = wt i) ∧
  (∀ h b : G, h * S.z * h⁻¹ ∈ S.QG → h * S.z * h⁻¹ ≠ S.z → IsConj S.z b → b ∈ S.QG →
    b ≠ S.z → ∀ i j, i < 75735 → j < 75735 → code32 (φ (S.cl (h * S.z * h⁻¹))) = wt i →
      code32 (φ (S.cl b)) = wt j → (b ∈ S.Qa h ↔ adjW i j = true)) ∧
  (∀ k < 365211, ∃ m ∈ S.M, ∀ y ∈ S.QG,
    code32 (φ (S.cl (m * y * m⁻¹))) = applyCols (tvCols k) (code32 (φ (S.cl y))))

@[expose] def SmithE7Clause4 (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)) : Prop :=
  ∀ x : G, IsConj S.z x → x ∈ S.M → x ∉ S.QG → ∃ k < 365211, ∀ y ∈ S.QG,
    code32 (φ (S.cl (x * y * x⁻¹))) = applyCols (tvCols k) (code32 (φ (S.cl y)))

end CFSG.GF2Type.SmithTypeE.E7
