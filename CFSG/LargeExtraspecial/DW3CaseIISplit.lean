module

public import CFSG.LargeExtraspecial.DW3CaseI
public import CFSG.LargeExtraspecial.DW2ABasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}
  [IsElementaryAbelian 2 A]

namespace MaxEA

theorem exists_split_of_isCompl (hA : MaxEA S A) (hw : S.width = 3)
    {B : Submodule (ZMod 2) S.Qt} (hBinv : IsMbarInvariant S B) (hBq : ∀ b ∈ B, S.q b = 0)
    (hAB : IsCompl (S.clSub A) B) {h : G}
    (hxA : h * S.z * h⁻¹ ∈ A) (hxz : h * S.z * h⁻¹ ≠ S.z) :
    ∃ (W₁ W₂ : Submodule (ZMod 2) S.Qt) (H : W3.Hyp S W₁ W₂),
      Function.Surjective H.res ∧
        ∃ x : G, x ∈ S.M ∧ x ∉ S.QG ∧ x * x = 1 ∧
          ∃ A' : Subgroup G, IsElementaryAbelian 2 A' ∧ MaxEA S A' ∧
            ∀ a ∈ A', x * a = a * x := by
  have hxQ : h * S.z * h⁻¹ ∈ S.QG := hA.le_QG hxA
  have : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  have hBmax : MaxEA S (S.clPre B) := by
    refine ⟨S.clPre_le_QG B, ?_⟩
    have hfin : finrank (ZMod 2) B = 3 := by
      have h := Submodule.finrank_add_eq_of_isCompl hAB
      rw [hA.finrank_clSub, hw, S.finrank_Qt_eq_two_mul_width, hw] at h
      omega
    rw [S.card_clPre, S.card_submodule, hfin, hw]
    norm_num
  haveI : IsElementaryAbelian 2 (S.clPre B) := W4.isElementaryAbelian_clPre hBq
  have hBM : S.M ≤ normalizer (S.clPre B : Set G) := M_le_normalizer_clPre hBinv
  have hx1 : h * S.z * h⁻¹ ≠ 1 := by
    intro h1
    apply S.z_ne_one
    calc S.z = h⁻¹ * (h * S.z * h⁻¹) * h := by group
      _ = 1 := by rw [h1]; group
  have hxnotB : h * S.z * h⁻¹ ∉ S.clPre B := by
    intro hxB
    have hcl : S.cl (h * S.z * h⁻¹) ∈ S.clSub A ⊓ B :=
      ⟨S.cl_mem_clSub hxA hxQ, hxB.2⟩
    rw [hAB.inf_eq_bot, Submodule.mem_bot] at hcl
    rcases (S.cl_eq_zero_iff hxQ).mp hcl with h1 | hz
    · exact hx1 h1
    · exact hxz hz
  exact hBmax.exists_split_of_not_mem hBM hxQ hxnotB hw

end MaxEA

end CFSG.LargeExtraspecial.DW
