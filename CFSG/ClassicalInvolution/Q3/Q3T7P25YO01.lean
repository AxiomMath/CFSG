module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25U03
public import CFSG.ClassicalInvolution.Asc77.AscCX9W

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

set_option linter.unusedSectionVars false
namespace Asc77.CX
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups
section Facts

@[expose] def Om5StabDiag : Prop :=
  ∀ (K₀ K₀' : Type) [Group K₀] [Group K₀'] (L : TwinGroup K₀ K₀'), IsOm5 L →
    ∀ (s : L.X ≃* L.X) (hA : L.A.map (s : L.X →* L.X) = L.A)
      (hA' : L.A'.map (s : L.X →* L.X) = L.A'),
      DiagTriv 3 (TwinGroup.restr s hA) ↔ DiagTriv 3 (TwinGroup.restr' s hA')

@[expose] def Om6ReflWit : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    Om6mData Y Φ A A' z' a₀ b₀ → ∀ β : MulAut Y,
      (∀ y ∈ A, β y = y) → (∀ y ∈ A', β y = y) → β * β = 1 → β ≠ 1 → β ≠ MulAut.conj z' →
        ∃ (hA : A ≤ Goldschmidt75.perfRes (fixSubgroup β))
          (hA' : A' ≤ Goldschmidt75.perfRes (fixSubgroup β))
          (hB : A ≤ Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj z')))
          (hB' : A' ≤ Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj z'))),
          IsOm5 (centTG A A' β hA hA') ∧
            IsOm5 (centTG A A' (β * MulAut.conj z') hB hB') ∧
            DiagWit 3 (centTG A A' β hA hA') (centTG A A' (β * MulAut.conj z') hB hB')

theorem not_diagRel_of_diagWit (ha : Om5StabDiag) {K₀ K₀' : Type} [Group K₀] [Group K₀']
    {L₁ L₂ : TwinGroup K₀ K₀'} (h₁ : IsOm5 L₁) (hw : DiagWit 3 L₁ L₂) :
    ¬ DiagRel 3 L₁ L₂ := by
  rintro ⟨φ, hA, hA', hiff⟩
  obtain ⟨φ₀, hB, hB', hxor⟩ := hw
  obtain ⟨⟨eK⟩, ⟨eK'⟩⟩ :=
      CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.exists_sl2_equiv_of_isOm5 h₁
  obtain ⟨Φ, z', a₀, b₀, hD⟩ := h₁
  have h2 : (2 : GaloisField 3 1) ≠ 0 := C5O.M.two_ne_zero_gf 1 (by norm_num : (3 : ℕ) ≠ 2)
  have hchar : ringChar (GaloisField 3 1) = 3 := ringChar.eq (GaloisField 3 1) 3
  have hsl : C5P.TwoClasses 3 (SL(2, GaloisField 3 1)) := by
    have h := C5P.twoClasses_sl2 h2
    rwa [hchar] at h
  have hT : C5P.TwoClasses 3 K₀ := C5P.twoClasses_of_mulEquiv eK hsl
  have hT' : C5P.TwoClasses 3 K₀' := C5P.twoClasses_of_mulEquiv eK' hsl
  have hs := ha K₀ K₀' L₁ ⟨Φ, z', a₀, b₀, hD⟩ (φ.trans φ₀.symm)
    (TwinGroup.map_trans φ φ₀.symm hA (TwinGroup.map_symm φ₀ hB))
    (TwinGroup.map_trans φ φ₀.symm hA' (TwinGroup.map_symm φ₀ hB'))
  rw [TwinGroup.restr_trans φ φ₀.symm hA (TwinGroup.map_symm φ₀ hB),
    TwinGroup.restr'_trans φ φ₀.symm hA' (TwinGroup.map_symm φ₀ hB'),
    TwinGroup.restr_symm φ₀ hB, TwinGroup.restr'_symm φ₀ hB', diagTriv_trans_symm_iff hT,
    diagTriv_trans_symm_iff hT'] at hs
  exact hxor (by tauto)

theorem om6ReflDiag_of (ha : Om5StabDiag) (hb : Om6ReflWit) : Om6ReflDiag := by
  intro Y _ _ Φ A A' z' a₀ b₀ hY β hβA hβA' hβ2 hβ1 hβz
  obtain ⟨hA, hA', hB, hB', h5, h5', hw⟩ := hb Y Φ A A' z' a₀ b₀ hY β hβA hβA' hβ2 hβ1 hβz
  exact ⟨hA, hA', hB, hB', h5, h5', not_diagRel_of_diagWit ha h5 hw⟩
end Facts
end Asc77.CX

end

end CFSG.ClassicalInvolution.Q3.Q3T8
