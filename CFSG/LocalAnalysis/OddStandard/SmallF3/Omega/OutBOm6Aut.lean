module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBOm6Gen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBOm6Inn
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem aor_card_outer_dvd_of_psu_four {T : Type} [Group T] (h : LieModel T .PSU 4 3 1) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) ∣ 2 ^ 3 := by
  rcases h with ⟨-, hcl⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  have hcard := (CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound T 4 3 1
    hcl).2.2.1
  norm_num at hcard
  rw [hcard]
  norm_num

theorem aor_card_outer_dvd_of_psl_four {T : Type} [Group T] (h : LieModel T .PSL 4 3 1) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) ∣ 2 ^ 2 := by
  rcases h with ⟨-, hcl⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  have hcard := (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound T 4 3 1
    hcl).2.2.2.2 (by norm_num)
  norm_num at hcard
  rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
  exact hcard

theorem asc82OddInner_of_isOm6M [Finite G] {L : Subgroup G} (h : IsOm6M L) : Asc82OddInner L := by
  obtain ⟨hq, hm⟩ := h
  unfold IsOmega6Minus at hm
  haveI : Group.IsPerfect ↥L := hq.1
  have hs : IsSimpleGroup (L ⧸ oddCore L) := by
    have hmodel := hm.statedClassicalModel_of_ne_zero (by norm_num : (4 : ℕ) ≠ 0)
    exact (CFSG.LieType.Simplicity.fam_classical_converse (L ⧸ oddCore L)
      ⟨.PSU, 4, 3, 1, hmodel⟩).2.2
  have hcenter := center_eq_oddCore_of_simple hq hs
  have hlie : LieModel (↥L ⧸ center ↥L) .PSU 4 3 1 :=
    LieModel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hcenter).symm hm
  have hcard := aor_card_outer_dvd_of_psu_four (T := ↥L ⧸ center ↥L) hlie
  exact aor_oddInner_of_conj_range (aor_conj_range_of_card_outer_dvd hq.1 hcard)

theorem asc82OddInner_of_isOm6P [Finite G] {L : Subgroup G} (h : IsOm6P L) : Asc82OddInner L := by
  obtain ⟨hq, hm⟩ := h
  unfold IsOmega6Plus at hm
  haveI : Group.IsPerfect ↥L := hq.1
  have hs : IsSimpleGroup (L ⧸ oddCore L) := by
    have hmodel := hm.statedClassicalModel_of_ne_zero (by norm_num : (4 : ℕ) ≠ 0)
    exact (CFSG.LieType.Simplicity.fam_classical_converse (L ⧸ oddCore L)
      ⟨.PSL, 4, 3, 1, hmodel⟩).2.2
  have hcenter := center_eq_oddCore_of_simple hq hs
  have hlie : LieModel (↥L ⧸ center ↥L) .PSL 4 3 1 :=
    LieModel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hcenter).symm hm
  have hcard := aor_card_outer_dvd_of_psl_four (T := ↥L ⧸ center ↥L) hlie
  exact aor_oddInner_of_conj_range (aor_conj_range_of_card_outer_dvd hq.1 hcard)

theorem asc82OddInner_of_twoU43 [Finite G] {L : Subgroup G} (hq : IsQuasisimple L)
    (h : IsTwoU43 (L ⧸ oddCore L)) : Asc82OddInner L := by
  obtain ⟨hcard2, hmod⟩ := h
  haveI : Group.IsPerfect ↥L := hq.1
  have hnt : oddCore ↥L ≠ ⊤ := by
    intro htop
    haveI : Subsingleton (↥L ⧸ oddCore ↥L) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    have h1 : Nat.card (Subgroup.center (↥L ⧸ oddCore ↥L)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    omega
  have hker_le : (QuotientGroup.mk' (oddCore ↥L)).ker ≤ Subgroup.center ↥L := by
    rw [QuotientGroup.ker_mk' (oddCore ↥L)]
    exact oddCore_le_center_of_isQuasisimple hq hnt
  have e := CFSG.ComponentClassification.PerfectCentralQuotient.equivalence
    (QuotientGroup.mk' (oddCore ↥L)) (QuotientGroup.mk'_surjective (oddCore ↥L)) hker_le
  have hlie : LieModel (↥L ⧸ center ↥L) .PSU 4 3 1 :=
    LieModel.of_mulEquiv e.symm hmod
  have hcard := aor_card_outer_dvd_of_psu_four (T := ↥L ⧸ center ↥L) hlie
  exact aor_oddInner_of_conj_range (aor_conj_range_of_card_outer_dvd hq.1 hcard)

end CFSG.OddStandard.SmallF3.Omega
