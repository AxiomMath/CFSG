module

public import CFSG.LargeExtraspecial.S14SMGDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open CFSG.SmithE

@[expose] def SmithEModel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* timmesfeldPSU 6) →
      ∃ φ : S.Qt ≃ₗ[ZMod 2] (Fin 20 → ZMod 2),
        (∀ c : G, IsConj S.z c → c ∈ S.QG → c ≠ S.z → ∃ i < 891, SMG.code (φ (S.cl c)) = wt i) ∧
        (∀ i < 891, ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ SMG.code (φ (S.cl c)) = wt i) ∧
        (∀ h b : G, h * S.z * h⁻¹ ∈ S.QG → h * S.z * h⁻¹ ≠ S.z → IsConj S.z b → b ∈ S.QG →
          b ≠ S.z → ∀ i j, i < 891 → j < 891 → SMG.code (φ (S.cl (h * S.z * h⁻¹))) = wt i →
            SMG.code (φ (S.cl b)) = wt j → (b ∈ S.Qa h ↔ adjW i j = true)) ∧
        (∀ x : G, IsConj S.z x → x ∈ S.M → x ∉ S.QG → ∃ k < 693, ∀ y ∈ S.QG,
          SMG.code (φ (S.cl (x * y * x⁻¹))) = applyCols (tvCols k) (SMG.code (φ (S.cl y)))) ∧
        (∀ k < 693, ∃ m ∈ S.M, ∀ y ∈ S.QG,
          SMG.code (φ (S.cl (m * y * m⁻¹))) = applyCols (tvCols k) (SMG.code (φ (S.cl y))))

theorem smithE22Module_of_model (h : SmithEModel) : SmithE22Module := by
  intro G _ _ _ S hw hU
  obtain ⟨φ, h1, h2, h3, h4, -⟩ := h G S hw hU
  exact ⟨φ, h1, h2, h3, h4⟩

end CFSG.LargeExtraspecial.S14
