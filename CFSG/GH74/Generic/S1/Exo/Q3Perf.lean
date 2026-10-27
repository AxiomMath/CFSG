module

public import CFSG.GH74.Generic.S1.BlkSplit
public import CFSG.CharacterTheory.Burnside
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups

theorem isSolvable_blkLin_of_card_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3)
    {a b : Fin 4} (hab : a ≠ b) : Group.IsSolvable ↥(blkLin (F := F) a b) := by
  obtain ⟨e⟩ := blkLin_equiv (F := F) a b hab
  have hcard : Nat.card SL(2, F) = 2 ^ 3 * 3 ^ 1 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F, hF]
    norm_num
  let _ : Fintype SL(2, F) := Fintype.ofFinite _
  have hsolv : Group.IsSolvable SL(2, F) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

theorem isSolvable_of_le_sup_of_commute {X : Type*} [Group X] {B₁ B₂ P : Subgroup X}
    (h : ∀ a ∈ B₁, ∀ b ∈ B₂, a * b = b * a) [Group.IsSolvable B₁] [Group.IsSolvable B₂]
    (hle : P ≤ B₁ ⊔ B₂) : Group.IsSolvable P := by
  have hc : ∀ (a : ↥B₁) (b : ↥B₂), Commute (B₁.subtype a) (B₂.subtype b) :=
    fun a b => h a a.2 b b.2
  set φ := B₁.subtype.noncommCoprod B₂.subtype hc with hφ
  have hr : φ.range = B₁ ⊔ B₂ := by
    rw [hφ, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hsup : Group.IsSolvable ↥(B₁ ⊔ B₂) := by
    rw [← hr]
    exact Group.isSolvable_of_surjective φ.rangeRestrict_surjective
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem perfect_commute_z0_eq_bot {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3)
    {z0 : ↥(StatedSL 4 F)} (hz0 : z0 ∈ blkLin (F := F) 0 1) (hz0sq : z0 * z0 = 1) (hz01 : z0 ≠ 1)
    (P : Subgroup ↥(StatedSL 4 F)) (hP : ∀ g ∈ P, g * z0 = z0 * g) (hperf : ⁅P, P⁆ = P) : P = ⊥ := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (by rw [hF]; exact ⟨1, rfl⟩)
  have hle : P ≤ blkLin (F := F) 2 3 ⊔ blkLin (F := F) 0 1 :=
    perfect_le_pair_lin h2 (a := 2) (b := 3) (c := 0) (d := 1) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hz0 hz0sq hz01 P hP hperf
  have hA := isSolvable_blkLin_of_card_three hF (a := 2) (b := 3) (by decide)
  have hB := isSolvable_blkLin_of_card_three hF (a := 0) (b := 1) (by decide)
  have hsolv : Group.IsSolvable ↥P :=
    isSolvable_of_le_sup_of_commute (fun a ha b hb => blkLin_commute 2 3 0 1 (by decide)
      (by decide) (by decide) (by decide) a ha b hb) hle
  by_contra hne
  have : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hperf
  exact Group.IsPerfect.not_isSolvable ↥P hsolv

end CFSG.GH74.Generic.S1.Exo
