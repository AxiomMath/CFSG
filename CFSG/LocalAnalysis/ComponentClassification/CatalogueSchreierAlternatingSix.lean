module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSixCount
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSmallOrders

public section

namespace CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix

open OuterAutomorphisms

theorem center_eq_bot : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
  alternatingGroup.center_eq_bot (by simp)

theorem inner_conjugation_injective :
    Function.Injective (MulAut.conj : alternatingGroup (Fin 6) →*
      MulAut (alternatingGroup (Fin 6))) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro element helement
  have hcentral : element ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    apply Subgroup.mem_center_iff.mpr
    intro other
    have hconjugate := congrArg (fun automorphism : MulAut (alternatingGroup (Fin 6)) =>
      automorphism other) helement
    change element * other * element⁻¹ = other at hconjugate
    have heq := congrArg (fun a : alternatingGroup (Fin 6) => a * element) hconjugate
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using heq.symm
  rwa [center_eq_bot] at hcentral

theorem inner_card : Nat.card (inner (alternatingGroup (Fin 6))) = 360 := by
  change Nat.card (MulAut.conj : alternatingGroup (Fin 6) →*
    MulAut (alternatingGroup (Fin 6))).range = 360
  rw [← Nat.card_congr (MonoidHom.ofInjective inner_conjugation_injective).toEquiv]
  exact card_alternating_six

set_option maxRecDepth 10000 in
theorem outer_card_le_four : Nat.card (Outer (alternatingGroup (Fin 6))) ≤ 4 := by
  change Nat.card (MulAut (alternatingGroup (Fin 6)) ⧸ inner (alternatingGroup (Fin 6))) ≤ 4
  have hquotient := (inner (alternatingGroup (Fin 6))).card_eq_card_quotient_mul_card_subgroup
  rw [inner_card] at hquotient
  have hbound := automorphism_card_le
  rw [hquotient] at hbound
  omega

theorem outer_commutative : IsMulCommutative (Outer (alternatingGroup (Fin 6))) :=
  commutative_of_card_le_four outer_card_le_four

theorem outer_solvable : Group.IsSolvable (Outer (alternatingGroup (Fin 6))) :=
  solvable_of_card_le_four outer_card_le_four

theorem outer_card_le_four_of_equiv {G : Type*} [Group G]
    (equivalence : G ≃* alternatingGroup (Fin 6)) : Nat.card (Outer G) ≤ 4 := by
  rw [Nat.card_congr (OuterAutomorphisms.equivalence equivalence).toEquiv]
  exact outer_card_le_four

theorem outer_solvable_of_equiv {G : Type*} [Group G]
    (equivalence : G ≃* alternatingGroup (Fin 6)) : Group.IsSolvable (Outer G) := by
  let := outer_solvable
  exact OuterAutomorphisms.solvable_of_equiv equivalence.symm

theorem outer_solvable_of_nonempty_equiv {G : Type*} [Group G]
    (hequivalence : Nonempty (G ≃* alternatingGroup (Fin 6))) : Group.IsSolvable (Outer G) := by
  obtain ⟨equivalence⟩ := hequivalence
  exact outer_solvable_of_equiv equivalence

end CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix
