module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup
open scoped commutatorElement

private def coordEmb (x : Multiplicative (ZMod 2)) :
    alternatingGroup (Fin 5) →* A5WrTwo where
  toFun a := ⟨Pi.mulSingle x a, 1⟩
  map_one' := by
    apply RegularWreathProduct.ext
    · simp [Pi.mulSingle_one]
    · rfl
  map_mul' a b := by
    apply RegularWreathProduct.ext
    · funext q
      simp [RegularWreathProduct.mul_def, Pi.mulSingle_mul, inv_one, one_mul]
    · simp [RegularWreathProduct.mul_def]

private theorem coord_cases (q : Multiplicative (ZMod 2)) :
    q = 1 ∨ q = Multiplicative.ofAdd 1 := by
  rcases (show ∀ e : ZMod 2, e = 0 ∨ e = 1 by decide) (Multiplicative.toAdd q) with h | h
  · left
    rw [← ofAdd_toAdd q, h]
    rfl
  · right
    rw [← ofAdd_toAdd q, h]

private theorem eq_coord_mul (g : A5WrTwo) (hg : g.right = 1) :
    g = coordEmb 1 (g.left 1) *
      coordEmb (Multiplicative.ofAdd 1) (g.left (Multiplicative.ofAdd 1)) := by
  apply RegularWreathProduct.ext
  · funext q
    rcases coord_cases q with rfl | rfl <;>
      simp [coordEmb, RegularWreathProduct.mul_def, inv_one, one_mul, mul_one,
        Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne]
  · simpa [coordEmb, RegularWreathProduct.mul_def, hg]

theorem A5WrTwo.commutator_commutator :
    ⁅commutator A5WrTwo, commutator A5WrTwo⁆ = commutator A5WrTwo := by
  have hperf : commutator (alternatingGroup (Fin 5)) = ⊤ :=
    commutator_alternatingGroup_eq_top (by simp)
  have hcoord : ∀ x : Multiplicative (ZMod 2),
      (coordEmb x).range ≤ ⁅commutator A5WrTwo, commutator A5WrTwo⁆ := by
    intro x
    haveI : Group.IsPerfect (alternatingGroup (Fin 5)) := ⟨hperf⟩
    haveI : Group.IsPerfect (coordEmb x).range := Group.IsPerfect.range (coordEmb x)
    have hxB : (coordEmb x).range ≤ commutator A5WrTwo :=
      calc (coordEmb x).range = ⁅(coordEmb x).range, (coordEmb x).range⁆ :=
            (Subgroup.commutator_eq_self (H := (coordEmb x).range)).symm
        _ ≤ ⁅(⊤ : Subgroup A5WrTwo), ⊤⁆ := Subgroup.commutator_mono le_top le_top
        _ = commutator A5WrTwo := (commutator_def A5WrTwo).symm
    calc (coordEmb x).range = ⁅(coordEmb x).range, (coordEmb x).range⁆ :=
          (Subgroup.commutator_eq_self (H := (coordEmb x).range)).symm
      _ ≤ ⁅commutator A5WrTwo, commutator A5WrTwo⁆ := Subgroup.commutator_mono hxB hxB
  haveI : IsMulCommutative (Multiplicative (ZMod 2)) :=
    IsMulCommutative.of_comm (fun a b => mul_comm a b)
  have hle : commutator A5WrTwo ≤
      (RegularWreathProduct.rightHom : A5WrTwo →* Multiplicative (ZMod 2)).ker :=
    Abelianization.commutator_subset_ker _
  apply le_antisymm
  · calc ⁅commutator A5WrTwo, commutator A5WrTwo⁆
        ≤ ⁅(⊤ : Subgroup A5WrTwo), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator A5WrTwo := (commutator_def A5WrTwo).symm
  · intro g hg
    have hgright : g.right = 1 := hle hg
    rw [eq_coord_mul g hgright]
    exact mul_mem (hcoord 1 (MonoidHom.mem_range.mpr ⟨g.left 1, rfl⟩))
      (hcoord (Multiplicative.ofAdd 1)
        (MonoidHom.mem_range.mpr ⟨g.left (Multiplicative.ofAdd 1), rfl⟩))

end CFSG.EvenSporadicStandard.HNRecog
