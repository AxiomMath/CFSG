module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardInvolutionCentralizer
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoDataAux

public section

namespace CFSG.ComponentClassification.GS79bSec5

open Subgroup

theorem false_of_commute_perfect_of_odd_central_psl_three
    {A : Type} [Group A] [Finite A] {F : Type} [Field F] [Finite F] [CharP F 2]
    (π : A →* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    (hker : π.ker ≤ center A) (hodd : Odd (Nat.card π.ker)) {B C : Subgroup A}
    (hB : ⁅B, B⁆ = B) (hC : ⁅C, C⁆ = C) (hB1 : B ≠ ⊥) (hC1 : C ≠ ⊥)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) : False := by
  classical
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCeven : 2 ∣ Nat.card C := by
    by_contra h
    have hCodd : Odd (Nat.card C) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)
    exact hC1 (CFSG.AGLEmbedding.eq_bot_of_commutator_eq_self_of_le le_rfl
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hCodd) hC)
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 hCeven
  have hv' : orderOf (v : A) = 2 := by rw [Subgroup.orderOf_coe]; exact hv
  have hv2 : (v : A) * v = 1 := by
    rw [← pow_two, ← hv']
    exact pow_orderOf_eq_one (v : A)
  have hv1 : (v : A) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hv'
    exact absurd hv' (by norm_num)
  set Z : Subgroup A := centralizer ({(v : A)} : Set A) with hZ
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 Z))
  have hPn : (P : Subgroup Z).Normal :=
    normal_sylow_two_involution_centralizer_of_odd_central_psl_three π hker hodd hv2 hv1 P
  have hZsolv : Group.IsSolvable Z := by
    have hQodd : Odd (Nat.card (Z ⧸ (P : Subgroup Z))) :=
      Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp P.not_dvd_index)
    have hQ : Group.IsSolvable (Z ⧸ (P : Subgroup Z)) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hQodd
    have hPnil : Group.IsNilpotent (P : Subgroup Z) := P.isPGroup'.isNilpotent
    exact solvable_of_ker_le_range (P : Subgroup Z).subtype (QuotientGroup.mk' (P : Subgroup Z))
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  have hBZ : B ≤ Z := fun b hb => mem_centralizer_singleton_iff.mpr (hBC b hb v v.2)
  exact hB1 (CFSG.AGLEmbedding.eq_bot_of_commutator_eq_self_of_le hBZ hZsolv hB)

end CFSG.ComponentClassification.GS79bSec5
