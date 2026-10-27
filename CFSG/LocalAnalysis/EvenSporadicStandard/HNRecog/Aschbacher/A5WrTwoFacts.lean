module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

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

private def sigmaA5 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2,
    Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
      (show Equiv.Perm.IsSwap (Equiv.swap (0 : Fin 5) 1) from ⟨0, 1, by decide, rfl⟩)
      (show Equiv.Perm.IsSwap (Equiv.swap (1 : Fin 5) 2) from ⟨1, 2, by decide, rfl⟩)⟩

private def tauA5 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 3,
    Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
      (show Equiv.Perm.IsSwap (Equiv.swap (0 : Fin 5) 1) from ⟨0, 1, by decide, rfl⟩)
      (show Equiv.Perm.IsSwap (Equiv.swap (1 : Fin 5) 3) from ⟨1, 3, by decide, rfl⟩)⟩

private theorem sigmaA5_mul_tauA5_ne :
    sigmaA5 * tauA5 ≠ tauA5 * sigmaA5 := by
  decide

theorem A5WrTwo.exists_mul_ne_mul : ∃ a b : A5WrTwo, a * b ≠ b * a := by
  refine ⟨⟨fun _ => sigmaA5, 1⟩, ⟨fun _ => tauA5, 1⟩, ?_⟩
  intro h
  apply sigmaA5_mul_tauA5_ne
  have h2 := congrArg (fun g : A5WrTwo => g.left 1) h
  simpa [RegularWreathProduct.mul_def] using h2

theorem A5WrTwo.commutator_eq_ker :
    commutator A5WrTwo =
      (RegularWreathProduct.rightHom : A5WrTwo →* Multiplicative (ZMod 2)).ker := by
  have hperf : commutator (alternatingGroup (Fin 5)) = ⊤ :=
    commutator_alternatingGroup_eq_top (by simp)
  have hcoord : ∀ x : Multiplicative (ZMod 2),
      (coordEmb x).range ≤ commutator A5WrTwo := by
    intro x
    haveI : Group.IsPerfect (alternatingGroup (Fin 5)) := ⟨hperf⟩
    haveI : Group.IsPerfect (coordEmb x).range := Group.IsPerfect.range (coordEmb x)
    calc (coordEmb x).range = ⁅(coordEmb x).range, (coordEmb x).range⁆ :=
          (Subgroup.commutator_eq_self (H := (coordEmb x).range)).symm
      _ ≤ ⁅(⊤ : Subgroup A5WrTwo), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator A5WrTwo := (commutator_def A5WrTwo).symm
  haveI : IsMulCommutative (Multiplicative (ZMod 2)) :=
    IsMulCommutative.of_comm (fun a b => mul_comm a b)
  have hle : commutator A5WrTwo ≤
      (RegularWreathProduct.rightHom : A5WrTwo →* Multiplicative (ZMod 2)).ker :=
    Abelianization.commutator_subset_ker _
  have hge : (RegularWreathProduct.rightHom : A5WrTwo →* Multiplicative (ZMod 2)).ker ≤
      commutator A5WrTwo := by
    intro g hg
    have hgright : g.right = 1 := hg
    rw [eq_coord_mul g hgright]
    apply Subgroup.mul_mem
    · exact hcoord 1 (MonoidHom.mem_range.mpr ⟨g.left 1, rfl⟩)
    · exact hcoord (Multiplicative.ofAdd 1)
        (MonoidHom.mem_range.mpr ⟨g.left (Multiplicative.ofAdd 1), rfl⟩)
  exact le_antisymm hle hge

theorem A5WrTwo.index_commutator : (commutator A5WrTwo).index = 2 := by
  rw [A5WrTwo.commutator_eq_ker, Subgroup.index_ker]
  have hsurj : Function.Surjective
      (RegularWreathProduct.rightHom : A5WrTwo →* Multiplicative (ZMod 2)) :=
    fun q => ⟨RegularWreathProduct.inl q, RegularWreathProduct.fun_id q⟩
  rw [MonoidHom.range_eq_top_of_surjective _ hsurj, Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

end CFSG.EvenSporadicStandard.HNRecog
