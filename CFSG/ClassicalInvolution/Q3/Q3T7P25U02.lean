module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25Y01
public import CFSG.ClassicalInvolution.Asc77.AscCX9P

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77.CX
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap

section Layers


@[expose] def IsOm5 {K₀ K₀' : Type} [Group K₀] [Group K₀'] (L : TwinGroup K₀ K₀') : Prop :=
  ∃ (Φ : Set (Subgroup L.X)) (z' a₀ b₀ : L.X), C5O.Om5Data L.X Φ L.A L.A' z' a₀ b₀

theorem isOm5_rebase_iff {K₀ K₀' K₁ K₁' : Type} [Group K₀] [Group K₀'] [Group K₁] [Group K₁']
    (L : TwinGroup K₁ K₁') (ψ : K₀ ≃* K₁) (ψ' : K₀' ≃* K₁') :
    IsOm5 (L.rebase ψ ψ') ↔ IsOm5 L :=
  Iff.rfl

structure Om6mData (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y)
    (z' a₀ b₀ : Y) : Prop where
  lie : ∃ D : LieSystemData 3 1 Y Φ, D.card = 1 ∧
    ∃ i : Fin D.card, IsOrthTag 6 (!piSign 3 1) (D.tag i) (D.rank i)
  twin : TwinSect0 Φ A A' z' a₀ b₀
  conj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ

@[expose] def DiagThree : Prop :=
  ∀ (K₀ K₀' : Type) [Group K₀] [Group K₀'] (L₁ L₂ L₃ : TwinGroup K₀ K₀'),
    IsOm5 L₁ → IsOm5 L₂ → IsOm5 L₃ →
      DiagRel 3 L₁ L₂ ∨ DiagRel 3 L₁ L₃ ∨ DiagRel 3 L₂ L₃

@[expose] def Om6ReflDiag : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    Om6mData Y Φ A A' z' a₀ b₀ → ∀ β : MulAut Y,
      (∀ y ∈ A, β y = y) → (∀ y ∈ A', β y = y) → β * β = 1 → β ≠ 1 → β ≠ MulAut.conj z' →
        ∃ (hA : A ≤ Goldschmidt75.perfRes (fixSubgroup β))
          (hA' : A' ≤ Goldschmidt75.perfRes (fixSubgroup β))
          (hB : A ≤ Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj z')))
          (hB' : A' ≤ Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj z'))),
          IsOm5 (centTG A A' β hA hA') ∧
            IsOm5 (centTG A A' (β * MulAut.conj z') hB hB') ∧
            ¬ DiagRel 3 (centTG A A' β hA hA') (centTG A A' (β * MulAut.conj z') hB hB')

end Layers

end Asc77.CX

end

end CFSG.ClassicalInvolution.Q3.Q3T8
