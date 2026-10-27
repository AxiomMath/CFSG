module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Sp62

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

private theorem mulAut_congr_apply {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (ζ : MulAut K) (x : K') : MulAut.congr e ζ x = e (ζ (e.symm x)) := rfl

private theorem mem_fixedSubgroup {G : Type*} [Group G] {α : MulAut G} {s : G} :
    s ∈ fixedSubgroup α ↔ α s = s := Iff.rfl

private def fixedSubgroupCongrAut {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (ζ : MulAut K) : fixedSubgroup ζ ≃* fixedSubgroup (MulAut.congr e ζ) where
  toFun x := ⟨e x, by
    rw [mem_fixedSubgroup, mulAut_congr_apply, MulEquiv.symm_apply_apply]
    exact congrArg e (mem_fixedSubgroup.mp x.2)⟩
  invFun y := ⟨e.symm y, by
    rw [mem_fixedSubgroup]
    apply e.injective
    rw [← mulAut_congr_apply, MulEquiv.apply_symm_apply]
    exact mem_fixedSubgroup.mp y.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply (x : K))
  right_inv y := Subtype.ext (e.apply_symm_apply (y : K'))
  map_mul' x y := Subtype.ext (map_mul e (x : K) (y : K))

theorem FixLarge.of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (h : FixLarge K) : FixLarge K' := by
  intro ζ' hζ'
  let ζ : MulAut K := (MulAut.congr e).symm ζ'
  have hcongr : MulAut.congr e ζ = ζ' := MulEquiv.apply_symm_apply (MulAut.congr e) ζ'
  have hζ : ζ * ζ = 1 := by
    apply (MulAut.congr e).injective
    rw [map_mul, map_one, hcongr, hζ']
  have hcard : Nat.card (fixedSubgroup ζ') = Nat.card (fixedSubgroup ζ) := by
    rw [← hcongr]
    exact (Nat.card_congr (fixedSubgroupCongrAut e ζ).toEquiv).symm
  rw [hcard]
  exact h ζ hζ

section Sp62Certified


theorem fixLarge_of_isSp62Cover {K : Type} [Group K] [Finite K] (h : IsSp62Cover K) :
    FixLarge K := by
  intro ζ hζ
  exact h.four_lt_fixed ζ hζ

end Sp62Certified

end CFSG.EvenSporadicStandard.Co3Std.CentT
