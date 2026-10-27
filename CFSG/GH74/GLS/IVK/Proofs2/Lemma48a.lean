module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LieType.Classical.SteinbergBLSymplectic
public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
open scoped Pointwise

namespace Lemma48a

theorem card_proj_statedSp_two (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    2 * Nat.card (StatedProj (StatedSp 2 F)) =
      Nat.card F ^ 4 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1) := by
  have hS : Nat.card (StatedSp 2 F) =
      Nat.card F ^ 4 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
    have h12 : Finset.Icc 1 2 = {1, 2} := by decide
    rw [h12, Finset.prod_pair (by norm_num)]
    norm_num
  have hN : Nat.card ((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F)) = 2 := by
    have h1 : ((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F)).map
        (StatedSp 2 F).subtype = StatedSp 2 F ⊓ StatedScalars (Fin 2 ⊕ Fin 2) F := by
      rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype]
    have h2 : Nat.card (((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F)).map
        (StatedSp 2 F).subtype) =
        Nat.card ((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F)) :=
      Subgroup.card_map_of_injective (StatedSp 2 F).subtype_injective
    rw [h1, (CFSG.LieType.Classical.symplectic_scalar_kernel F 2 (by norm_num)).2] at h2
    rw [← h2]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, Nat.add_sub_cancel]
    exact Nat.gcd_eq_left (dvd_mul_right 2 k)
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F))
  rw [hN, hS] at h3
  have h4 : Nat.card F ^ 4 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1) =
      Nat.card F ^ 4 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1)) := mul_assoc _ _ _
  rw [h4, h3]
  ring

end Lemma48a

end CFSG.GH74.GLS.IVK.Proofs2
