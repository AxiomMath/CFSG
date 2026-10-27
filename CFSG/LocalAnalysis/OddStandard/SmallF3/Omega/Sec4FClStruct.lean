module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FClMod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FClLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDStd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IPocketL
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Syl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec4FCl_structure [Finite G] {L : Subgroup G} (hL : IsOmega7Group L) {s : G}
    (hs2 : s * s = 1) (hs6 : InducesTypeSome L s 7 1 6 1) :
    ∃ (X : Subgroup G) (w : G),
      IsComponentIn X (L ⊓ centralizer ({s} : Set G)) ∧
      LieModel (X ⧸ oddCore X) .PSL 4 3 1 ∧ w ∈ L ∧ w ∈ centralizer ({s} : Set G) ∧
      IsI4PlusIn L w ∧
      L ⊓ centralizer ({s} : Set G) ≤ (X ⊔ Subgroup.zpowers w) ⊔ Sec4FOdd L := by
  haveI : NeZero (2 : ZMod 3) := ⟨(isUnit_of_invertible (2 : ZMod 3)).ne_zero⟩
  haveI : Finite (OGroup Sec4IQ) :=
    CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  obtain ⟨e⟩ := sec4I_exists_model hL
  obtain ⟨y, hact, hy⟩ :=
    (sec4I_inducesTypeSome_iff e (Or.inr (Or.inr rfl))).mp hs6
  obtain ⟨-, t, htt, ht6, hty⟩ := hy
  have hcov : Sec4FDCover L s (omegaGroup sec4IQ_nondegenerate) t (sec4FDCover0 e) :=
    sec4FDCover0_setting hL e hs2 hact htt hty
  obtain ⟨w, hKc, hoc, hlie, hwD, hww, hwty, hsup⟩ :=
    sec4FCl_model sec4IQ_nondegenerate sec4IQ_finrank sec4IQ_quadSign htt ht6
  obtain ⟨hwX, hwt⟩ := (mem_sec4FDDt_iff sec4IQ_nondegenerate).mp hwD
  have hKc' : IsComponentIn (sec4FClXt sec4IQ_nondegenerate htt)
      (omegaGroup sec4IQ_nondegenerate ⊓ centralizer ({t} : Set (OGroup Sec4IQ))) := by
    simpa only [Sec4FDDt] using hKc
  have hsup' : omegaGroup sec4IQ_nondegenerate ⊓
      centralizer ({t} : Set (OGroup Sec4IQ)) ≤
      sec4FClXt sec4IQ_nondegenerate htt ⊔ Subgroup.zpowers w := by
    simpa only [Sec4FDDt] using hsup
  obtain ⟨K', v, hvL, hK'c, hK'lie, hvs, hvv, hρv, hle⟩ :=
    sec4FCl_lift hcov hKc' hoc hlie hwX hwt hww hsup'
  have hw1 : w ≠ 1 := by
    intro hw
    rw [hw, invType_one] at hwty
    exact absurd (congrArg Prod.fst hwty) (by decide)
  have hv1 : v ≠ 1 := by
    intro hv
    refine hw1 ?_
    have h1 : (⟨v, hvL⟩ : ↥L) = 1 := Subtype.ext (by simpa using hv)
    exact hρv ▸ (by rw [h1, map_one]; rfl)
  have hord : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hvv) hv1
  have hHT : HasType ((e (QuotientGroup.mk (⟨v, hvL⟩ : ↥L)) : Sec4IOmega) :
      ProjOrth Sec4IQ) 4 1 :=
    (sec4I_inducesTypeSome_mem_iff e hvL (Or.inr (Or.inl rfl))).mp
      ((sec4FDCover0_type_iff e hvL hvv (Or.inr (Or.inl rfl))).mpr
        (by rw [hρv]; exact hwty))
  have hker : (sec4FDCover0 e).ker.map L.subtype ≤ Sec4FOdd L := by
    rw [Sec4FOdd]
    refine Subgroup.map_mono ?_
    rw [← sec4I_center_eq_oddCore hL]
    exact (sec4FDCover0_cover hL e).ker_le_center
  exact ⟨K', v, hK'c, hK'lie, hvL, Subgroup.mem_centralizer_singleton_iff.mpr hvs,
    (sec4I_isI4PlusIn_iff hL e).mpr ⟨hvL, hord, hHT⟩,
    le_trans hle (sup_le_sup_left hker _)⟩

end CFSG.OddStandard.SmallF3.Omega
