module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSetTransitivity

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem odd_prime_overgroup_two_fixed_points
    (H P Q : Subgroup G) (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hP : IsPGroup p P) (hQ : IsPGroup p Q) (hPQ : P ≤ Q)
    (hfixed : Nat.card (pointFixedSet H P) = 2) :
    pointFixedSet H Q = pointFixedSet H P ∧ Nat.card (pointFixedSet H Q) = 2 := by
  have hsubset := pointFixedSet_antitone (H := H) hPQ
  have hle : Nat.card (pointFixedSet H Q) ≤ 2 := by
    have hh : Nat.card (pointFixedSet H Q) ≤ Nat.card (pointFixedSet H P) :=
      Set.ncard_le_ncard hsubset
    rwa [hfixed] at hh
  have hmod : Nat.card (pointFixedSet H Q) ≡ 2 [MOD p] := by
    have hh := (pointFixedSet_card_modEq p hp H Q hQ).symm.trans
      (pointFixedSet_card_modEq p hp H P hP)
    rwa [hfixed] at hh
  have hge := two_le_of_modEq_two p _ hp hodd hmod
  have hcard : Nat.card (pointFixedSet H Q) = 2 := le_antisymm hle hge
  refine ⟨Set.eq_of_subset_of_ncard_le hsubset ?_, hcard⟩
  exact (hfixed.trans hcard.symm).le

theorem maximal_two_fixed_points_is_ambient_sylow
    (H P : Subgroup G) (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hP : IsPGroup p P) (hfixed : Nat.card (pointFixedSet H P) = 2)
    (hmax : IsMaximalTwoPointPrime H p P) :
    ∃ R : Sylow p G, (R : Subgroup G) = P := by
  obtain ⟨R, hPR⟩ := hP.exists_le_sylow
  obtain ⟨_, hRfixed⟩ := odd_prime_overgroup_two_fixed_points
    H P (R : Subgroup G) p hp hodd hP R.isPGroup' hPR hfixed
  exact ⟨R, hmax _ R.isPGroup' hPR (by omega)⟩

theorem ambient_sylow_pointFixedSet_card_eq
    (H : Subgroup G) (p : ℕ) (hp : p.Prime) (P R : Sylow p G) :
    Nat.card (pointFixedSet H (R : Subgroup G)) =
      Nat.card (pointFixedSet H (P : Subgroup G)) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P R
  have hconj : rightConjugate (P : Subgroup G) g⁻¹ = (R : Subgroup G) := by
    have hh := congrArg (fun S : Sylow p G => (S : Subgroup G)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hh
    have hf : (MulDistribMulAction.toMonoidEnd (MulAut G) G) (MulAut.conj g) =
        (MulAut.conj g).toMonoidHom := by
      ext x
      rfl
    rw [hf] at hh
    simpa only [rightConjugate, Subgroup.conjBy, inv_inv] using hh
  rw [← hconj, pointFixedSet_rightConjugate_card]

omit [Finite G] in
theorem pointRightCosetSpace_card_eq_index (H : Subgroup G) :
    Nat.card (pointRightCosetSpace H) = H.index := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)

omit [Finite G] in
theorem point_stabilizer_index (H : Subgroup G) (a : pointRightCosetSpace H) :
    (rightCosetStabilizer H a).index = H.index := by
  refine Quotient.inductionOn a ?_
  intro x
  change (rightCosetStabilizer H (rightCosetMk H x)).index = H.index
  rw [rightCosetStabilizer_mk]
  change (H.map (MulAut.conj x⁻¹).toMonoidHom).index = H.index
  rw [H.index_map_of_injective (MulAut.conj x⁻¹).injective,
    MonoidHom.range_eq_top.mpr (MulAut.conj x⁻¹).surjective, Subgroup.index_top, mul_one]

theorem two_fixed_points_point_indices_prime_to
    (H P : Subgroup G) (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hP : IsPGroup p P) (hfixed : Nat.card (pointFixedSet H P) = 2) :
    ¬ p ∣ H.index ∧ ∀ a : pointRightCosetSpace H, ¬ p ∣ (rightCosetStabilizer H a).index := by
  have hmod := pointFixedSet_card_modEq p hp H P hP
  rw [hfixed, pointRightCosetSpace_card_eq_index] at hmod
  have hp2 : ¬ p ∣ 2 := by
    intro hdvd
    have heq : p = 2 := (Nat.dvd_prime Nat.prime_two).mp hdvd |>.resolve_left hp.ne_one
    rw [heq] at hodd
    norm_num at hodd
  have hindex : ¬ p ∣ H.index := by
    intro hdvd
    exact hp2 (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd)))
  refine ⟨hindex, ?_⟩
  intro a
  rwa [point_stabilizer_index]

theorem point_sylow_is_ambient_of_two_fixed_points
    (H P : Subgroup G) (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hP : IsPGroup p P) (hfixed : Nat.card (pointFixedSet H P) = 2)
    (a : pointRightCosetSpace H) (R : Sylow p (rightCosetStabilizer H a)) :
    ∃ S : Sylow p G, (S : Subgroup G) =
      (R : Subgroup (rightCosetStabilizer H a)).map (rightCosetStabilizer H a).subtype := by
  let : Fact p.Prime := ⟨hp⟩
  have hi := (two_fixed_points_point_indices_prime_to H P p hp hodd hP hfixed).2 a
  let U := (R : Subgroup (rightCosetStabilizer H a)).map (rightCosetStabilizer H a).subtype
  have hUp : IsPGroup p U := R.isPGroup'.map (rightCosetStabilizer H a).subtype
  have hUi : ¬ p ∣ U.index := by
    rw [(R : Subgroup (rightCosetStabilizer H a)).index_map_of_injective
      (rightCosetStabilizer H a).subtype_injective, Subgroup.range_subtype]
    exact hp.not_dvd_mul R.not_dvd_index hi
  exact ⟨hUp.toSylow hUi, IsPGroup.toSylow_coe hUp hUi⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet
