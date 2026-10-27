module

public import CFSG.LargeExtraspecial.S14SMKDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open CFSG.SmithE

variable {G : Type} [Group G]

@[expose] def SmithEClauses1235 (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] (Fin 20 → ZMod 2)) :
    Prop :=
  (∀ c : G, IsConj S.z c → c ∈ S.QG → c ≠ S.z → ∃ i < 891, SMG.code (φ (S.cl c)) = wt i) ∧
  (∀ i < 891, ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ SMG.code (φ (S.cl c)) = wt i) ∧
  (∀ h b : G, h * S.z * h⁻¹ ∈ S.QG → h * S.z * h⁻¹ ≠ S.z → IsConj S.z b → b ∈ S.QG →
    b ≠ S.z → ∀ i j, i < 891 → j < 891 → SMG.code (φ (S.cl (h * S.z * h⁻¹))) = wt i →
      SMG.code (φ (S.cl b)) = wt j → (b ∈ S.Qa h ↔ adjW i j = true)) ∧
  (∀ k < 693, ∃ m ∈ S.M, ∀ y ∈ S.QG,
    SMG.code (φ (S.cl (m * y * m⁻¹))) = applyCols (tvCols k) (SMG.code (φ (S.cl y))))

@[expose] def SmithEClause4 (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] (Fin 20 → ZMod 2)) : Prop :=
  ∀ x : G, IsConj S.z x → x ∈ S.M → x ∉ S.QG → ∃ k < 693, ∀ y ∈ S.QG,
    SMG.code (φ (S.cl (x * y * x⁻¹))) = applyCols (tvCols k) (SMG.code (φ (S.cl y)))

@[expose] def SmithEClause4Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* timmesfeldPSU 6) → ∀ φ : S.Qt ≃ₗ[ZMod 2] (Fin 20 → ZMod 2),
      SmithEClauses1235 S φ → SmithEClause4 S φ

theorem smithEModel_of_clauses
    (h : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
      Nonempty (Mbar0 S ≃* timmesfeldPSU 6) →
        ∃ φ : S.Qt ≃ₗ[ZMod 2] (Fin 20 → ZMod 2), SmithEClauses1235 S φ)
    (h4 : SmithEClause4Stmt) : SmithEModel := by
  intro G _ _ _ S hw hU
  obtain ⟨φ, hφ⟩ := h G S hw hU
  exact ⟨φ, hφ.1, hφ.2.1, hφ.2.2.1, h4 G S hw hU φ hφ, hφ.2.2.2⟩

end CFSG.LargeExtraspecial.S14
