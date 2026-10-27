module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem ff_isSimpleGroup_oddCore_six_plus [Finite G] {L : Subgroup G} (h : IsOm6P L) :
    IsSimpleGroup (L ⧸ oddCore L) :=
  (CFSG.LieType.Simplicity.fam_classical_converse (L ⧸ oddCore L)
    ⟨.PSL, 4, 3, 1, h.2.statedClassicalModel_of_ne_zero (by norm_num : (4 : ℕ) ≠ 0)⟩).2.2

theorem ff_isSimpleGroup_oddCore_six_minus [Finite G] {L : Subgroup G} (h : IsOm6M L) :
    IsSimpleGroup (L ⧸ oddCore L) :=
  (CFSG.LieType.Simplicity.fam_classical_converse (L ⧸ oddCore L)
    ⟨.PSU, 4, 3, 1, h.2.statedClassicalModel_of_ne_zero (by norm_num : (4 : ℕ) ≠ 0)⟩).2.2

theorem ff_isSimpleGroup_oddCore_five [Finite G] {L : Subgroup G} (h : IsOm5Q L) :
    IsSimpleGroup (L ⧸ oddCore L) :=
  (CFSG.LieType.Simplicity.fam_classical_converse (L ⧸ oddCore L)
    ⟨.PSp, 2, 3, 1, h.2.statedClassicalModel_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)⟩).2.2

theorem ff_center_eq_oddCore_six_plus [Finite G] {L : Subgroup G} (h : IsOm6P L) :
    center ↥L = oddCore ↥L :=
  center_eq_oddCore_of_simple h.1 (ff_isSimpleGroup_oddCore_six_plus h)

theorem ff_center_eq_oddCore_six_minus [Finite G] {L : Subgroup G} (h : IsOm6M L) :
    center ↥L = oddCore ↥L :=
  center_eq_oddCore_of_simple h.1 (ff_isSimpleGroup_oddCore_six_minus h)

theorem ff_center_eq_oddCore_five [Finite G] {L : Subgroup G} (h : IsOm5Q L) :
    center ↥L = oddCore ↥L :=
  center_eq_oddCore_of_simple h.1 (ff_isSimpleGroup_oddCore_five h)

theorem ff_lieModel_center_six_plus [Finite G] {L : Subgroup G} (h : IsOm6P L) :
    LieModel (↥L ⧸ center ↥L) .PSL 4 3 1 :=
  LieModel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq (ff_center_eq_oddCore_six_plus h)).symm
    h.2

theorem ff_lieModel_center_six_minus [Finite G] {L : Subgroup G} (h : IsOm6M L) :
    LieModel (↥L ⧸ center ↥L) .PSU 4 3 1 :=
  LieModel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq (ff_center_eq_oddCore_six_minus h)).symm
    h.2

theorem ff_lieModel_center_five [Finite G] {L : Subgroup G} (h : IsOm5Q L) :
    LieModel (↥L ⧸ center ↥L) .PSp 2 3 1 :=
  LieModel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq (ff_center_eq_oddCore_five h)).symm
    h.2

theorem ff_isOmegaStar_center_six_plus [Finite G] {L : Subgroup G} (h : IsOm6P L) :
    IsOmegaStar (↥L ⧸ center ↥L) 6 1 :=
  isOmegaStar_of_lieModel_psl (ff_lieModel_center_six_plus h)

theorem ff_isOmegaStar_center_six_minus [Finite G] {L : Subgroup G} (h : IsOm6M L) :
    IsOmegaStar (↥L ⧸ center ↥L) 6 (-1) :=
  isOmegaStar_of_lieModel_psu (ff_lieModel_center_six_minus h)

theorem ff_isOmegaStar_center_five [Finite G] {L : Subgroup G} (h : IsOm5Q L) :
    IsOmegaStar (↥L ⧸ center ↥L) 5 1 :=
  isOmegaStar_of_lieModel_psp (ff_lieModel_center_five h)

end CFSG.OddStandard.SmallF3.Omega
