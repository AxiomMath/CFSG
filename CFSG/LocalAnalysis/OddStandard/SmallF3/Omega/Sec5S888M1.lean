module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E4b

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X} {E : Subgroup X}

private noncomputable def s888M1_P (hS : PlaneSys V W) (hE : ActsElemAb V E) :
    Subgroup (Equiv.Perm (Fin 4)) where
  carrier := {a | a ∈ planeImage hS E}
  mul_mem' := by
    intro a b ha hb
    exact (planeImage_group hS hE).2.1 a ha b hb
  one_mem' := (planeImage_group hS hE).1
  inv_mem' := by
    intro a ha
    rw [inv_eq_of_mul_eq_one_right ((planeImage_group hS hE).2.2 a ha)]
    exact ha

private theorem s888M1_card_P (hS : PlaneSys V W) (hE : ActsElemAb V E) :
    Nat.card (s888M1_P hS hE) = (planeImage hS E).card := by
  rw [show Nat.card (s888M1_P hS hE) =
      Nat.card ((planeImage hS E : Finset (Equiv.Perm (Fin 4))) : Set (Equiv.Perm (Fin 4)))
      from rfl]
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem exists_pair_of_relIndex [Finite X] (hS : PlaneSys V W) (hpar : PlaneParity V W)
    (hE : ActsElemAb V E) (hcard : 16 ≤ (centralizer (V : Set X)).relIndex E) :
    ∃ c d : Fin 4, c ≠ d ∧ ∀ y : normalizer (V : Set X), (y : X) ∈ E →
      (planeHom hS y c = c ∧ planeHom hS y d = d) ∨
        (planeHom hS y c = d ∧ planeHom hS y d = c) := by
  classical
  have hcardP : 16 ≤ Nat.card (s888M1_P hS hE) * (suppSet hS E).card := by
    rw [s888M1_card_P hS hE]
    rwa [relIndex_centralizer_eq hS hE] at hcard
  obtain ⟨c, d, hcd, hprop⟩ :=
    comb_pair_of_card (P := s888M1_P hS hE)
      (fun a ha => (planeImage_group hS hE).2.2 a ha)
      (suppSet_subspace hS hE).1 (suppSet_subspace hS hE).2
      (suppSet_even hS hpar hE)
      (fun x hx a ha i => suppSet_fixed hS hE x hx a ha i) hcardP
  refine ⟨c, d, hcd, fun y hy => ?_⟩
  exact hprop (planeHom hS y) ((mem_planeImage hS).mpr ⟨y, hy, rfl⟩)

end CFSG.OddStandard.SmallF3.Omega
