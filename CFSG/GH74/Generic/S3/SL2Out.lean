module

public import CFSG.GH74.Generic.S3.Prop21Leaves
public import CFSG.LieType.HighestRoot.SL2Outer

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups

section SL2Out

theorem b_SL2_outAbelian_of_outComm
    (hcomm : ∀ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) →
      ∀ α β : MulAut SL(2, F), ∃ y : SL(2, F), α * β * α⁻¹ * β⁻¹ = MulAut.conj y) :
    B_SL2_outAbelian := by
  intro F _ _ hodd A _ ⟨e⟩
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro α _ β _
  let c : MulAut SL(2, F) ≃* MulAut A := MulAut.congr e
  obtain ⟨y, hy⟩ := hcomm F inferInstance inferInstance hodd (c.symm α) (c.symm β)
  refine ⟨e y, ?_⟩
  have hcy : c (MulAut.conj y) = MulAut.conj (e y) := by
    ext z
    simp [c, MulAut.congr_apply, MulAut.conj_apply]
  rw [commutatorElement_def]
  have h1 : α * β * α⁻¹ * β⁻¹ = c (c.symm α * c.symm β * (c.symm α)⁻¹ * (c.symm β)⁻¹) := by
    simp
  rw [h1, hy, hcy]

end SL2Out

theorem b_SL2_outAbelian : B_SL2_outAbelian :=
  b_SL2_outAbelian_of_outComm CFSG.ComponentClassification.RankTwoOddLie.sl2OuterComm

end CFSG.GH74.Generic.S3
