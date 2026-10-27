module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Core
public import CFSG.GroupTheory.ABGDGroups.LinearASeven
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.ABGLocalTools
  CFSG.ABGDGroups CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo

section Dihedral

theorem isSolvable_dihedral' (z : ℕ) [NeZero z] : Group.IsSolvable (DihedralGroup z) := by
  classical
  let R : Subgroup (DihedralGroup z) := Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z)
  have hRnormal : R.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases g with i | i
    · refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      simp [DihedralGroup.r_mul_r]
    · refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
      simp [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.inv_sr]
  have : IsCyclic R := Subgroup.isCyclic_zpowers _
  let : CommGroup R := IsCyclic.commGroup
  have hRcard : Nat.card R = z := by rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have hQcard : Nat.card (DihedralGroup z ⧸ R) = 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup R
    rw [DihedralGroup.nat_card, hRcard] at h
    have hz : 0 < z := Nat.pos_of_ne_zero (NeZero.ne z)
    exact (Nat.eq_of_mul_eq_mul_right hz h).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (DihedralGroup z ⧸ R) := isCyclic_of_prime_card hQcard
  let : CommGroup (DihedralGroup z ⧸ R) := IsCyclic.commGroup
  exact Group.isSolvable_of_ker_le_range R.subtype (QuotientGroup.mk' R)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isSolvable_of_isDihedralOrder {Y : Type} [Group Y] {m : ℕ} (h : IsDihedralOrder Y m) :
    Group.IsSolvable Y := by
  obtain ⟨k, -, hk, ⟨e⟩⟩ := h
  have : NeZero k := ⟨by omega⟩
  have := isSolvable_dihedral' k
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

end Dihedral

end CFSG.GH74.GLS.IVK.Lifted
