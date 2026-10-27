module

public import CFSG.ClassicalInvolution.Asc77.AscC5P2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Defs

variable (p : ℕ)

@[expose] def DiagWit {K₀ K₀' : Type} [Group K₀] [Group K₀'] (L₁ L₂ : TwinGroup K₀ K₀') : Prop :=
  ∃ φ : L₁.X ≃* L₂.X, ∃ hA : L₁.A.map (φ : L₁.X →* L₂.X) = L₂.A,
    ∃ hA' : L₁.A'.map (φ : L₁.X →* L₂.X) = L₂.A',
      ¬ (DiagTriv p (TwinGroup.restr φ hA) ↔ DiagTriv p (TwinGroup.restr' φ hA'))

end Defs

section Calc

variable {p : ℕ}

theorem diagTriv_trans_symm_iff {H : Type} [Group H] (h : C5P.TwoClasses p H) (α β : H ≃* H) :
    DiagTriv p (α.trans β.symm) ↔ (DiagTriv p α ↔ DiagTriv p β) := by
  by_cases hβ : DiagTriv p β
  · rw [diagTriv_trans_iff_left hβ.symm]
    exact ⟨fun h => ⟨fun _ => hβ, fun _ => h⟩, fun h => h.2 hβ⟩
  · have hβ' : ¬ DiagTriv p β.symm := fun h => hβ (diagTriv_symm_iff.mp h)
    constructor
    · intro hαβ
      refine ⟨fun hα => absurd ((diagTriv_trans_iff_right hα).mp hαβ) hβ', fun h => absurd h hβ⟩
    · intro hiff
      have hα : ¬ DiagTriv p α := fun hα => hβ (hiff.mp hα)
      exact C5P.diagTriv_trans_of_not h hα hβ'

end Calc

section Facts

variable (p f : ℕ) [Fact p.Prime]


@[expose] def Om5StabDiag : Prop :=
  ∀ (K₀ K₀' : Type) [Group K₀] [Group K₀'] (L : TwinGroup K₀ K₀'), IsOm5 p f L →
    ∀ (s : L.X ≃* L.X) (hA : L.A.map (s : L.X →* L.X) = L.A)
      (hA' : L.A'.map (s : L.X →* L.X) = L.A'),
      DiagTriv p (TwinGroup.restr s hA) ↔ DiagTriv p (TwinGroup.restr' s hA')

@[expose] def Om6ReflWit : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    Om6mData p f Y Φ A A' z' a₀ b₀ → ∀ β : MulAut Y,
      (∀ y ∈ A, β y = y) → (∀ y ∈ A', β y = y) → β * β = 1 → β ≠ 1 → β ≠ MulAut.conj z' →
        ∃ (hA : A ≤ Goldschmidt75.perfRes (fixSubgroup β))
          (hA' : A' ≤ Goldschmidt75.perfRes (fixSubgroup β))
          (hB : A ≤ Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj z')))
          (hB' : A' ≤ Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj z'))),
          IsOm5 p f (centTG A A' β hA hA') ∧
            IsOm5 p f (centTG A A' (β * MulAut.conj z') hB hB') ∧
            DiagWit p (centTG A A' β hA hA') (centTG A A' (β * MulAut.conj z') hB hB')

variable {p f}

theorem not_diagRel_of_diagWit (ha : Om5StabDiag p f) {K₀ K₀' : Type} [Group K₀] [Group K₀']
    {L₁ L₂ : TwinGroup K₀ K₀'} (h₁ : IsOm5 p f L₁) (hw : DiagWit p L₁ L₂) :
    ¬ DiagRel p L₁ L₂ := by
  rintro ⟨φ, hA, hA', hiff⟩
  obtain ⟨φ₀, hB, hB', hxor⟩ := hw
  obtain ⟨⟨eK⟩, ⟨eK'⟩⟩ := C5P.exists_sl2_equiv_of_isOm5 h₁
  obtain ⟨Φ, z', a₀, b₀, hD⟩ := h₁
  have h2 : (2 : GaloisField p f) ≠ 0 := C5O.M.two_ne_zero_gf f hD.odd
  have hchar : ringChar (GaloisField p f) = p := ringChar.eq (GaloisField p f) p
  have hsl : C5P.TwoClasses p (SL(2, GaloisField p f)) := by
    have h := C5P.twoClasses_sl2 h2
    rwa [hchar] at h
  have hT : C5P.TwoClasses p K₀ := C5P.twoClasses_of_mulEquiv eK hsl
  have hT' : C5P.TwoClasses p K₀' := C5P.twoClasses_of_mulEquiv eK' hsl
  have hs := ha K₀ K₀' L₁ ⟨Φ, z', a₀, b₀, hD⟩ (φ.trans φ₀.symm)
    (TwinGroup.map_trans φ φ₀.symm hA (TwinGroup.map_symm φ₀ hB))
    (TwinGroup.map_trans φ φ₀.symm hA' (TwinGroup.map_symm φ₀ hB'))
  rw [TwinGroup.restr_trans φ φ₀.symm hA (TwinGroup.map_symm φ₀ hB),
    TwinGroup.restr'_trans φ φ₀.symm hA' (TwinGroup.map_symm φ₀ hB'),
    TwinGroup.restr_symm φ₀ hB, TwinGroup.restr'_symm φ₀ hB', diagTriv_trans_symm_iff hT,
    diagTriv_trans_symm_iff hT'] at hs
  exact hxor (by tauto)

theorem om6ReflDiag_of (ha : Om5StabDiag p f) (hb : Om6ReflWit p f) : Om6ReflDiag p f := by
  intro Y _ _ Φ A A' z' a₀ b₀ hY β hβA hβA' hβ2 hβ1 hβz
  obtain ⟨hA, hA', hB, hB', h5, h5', hw⟩ := hb Y Φ A A' z' a₀ b₀ hY β hβA hβA' hβ2 hβ1 hβz
  exact ⟨hA, hA', hB, hB', h5, h5', not_diagRel_of_diagWit ha h5 hw⟩

end Facts

end CFSG.ClassicalInvolution.Asc77.CX
