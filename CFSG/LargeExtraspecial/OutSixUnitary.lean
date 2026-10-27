module

public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.LargeExtraspecial.S14

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

theorem unitaryFieldData_two_one : UnitaryFieldData 2 1 (GaloisField 2 2) where
  prime := Nat.prime_two
  one_le := le_rfl
  card := (GaloisField.card 2 2 two_ne_zero).trans (by norm_num)

@[expose] noncomputable def mapMkEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*}
    [Field K] (H : Subgroup (GL ι K)) :
    H.map (ProjGenLinGroup.mk : GL ι K →* PGL(ι, K)) ≃*
      H ⧸ (Subgroup.center (GL ι K)).subgroupOf H :=
  (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype])).trans
    ((QuotientGroup.quotientKerEquivRange
      ((ProjGenLinGroup.mk : GL ι K →* PGL(ι, K)).comp H.subtype)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (by
        ext g
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ProjGenLinGroup.mk_eq_one,
          Subgroup.mem_subgroupOf, Subgroup.coe_subtype])))

theorem timmesfeldPSU_eq_map (n : ℕ) :
    timmesfeldPSU n = (unitarySU 2 1 (GaloisField 2 2) n).map ProjGenLinGroup.mk := by
  have hset : {A : GL (Fin n) (GaloisField 2 2) |
      (Matrix.of fun i j => (A : Matrix (Fin n) (Fin n) (GaloisField 2 2)) j i ^ 2) *
          (A : Matrix (Fin n) (Fin n) (GaloisField 2 2)) = 1 ∧
        GeneralLinearGroup.det A = 1} = (unitarySU 2 1 (GaloisField 2 2) n : Set _) := by
    ext A
    have hbar : ((A : Matrix (Fin n) (Fin n) (GaloisField 2 2)).map
        unitaryFieldData_two_one.bar)ᵀ =
          Matrix.of fun i j => (A : Matrix (Fin n) (Fin n) (GaloisField 2 2)) j i ^ 2 := by
      ext i j
      rw [transpose_apply, map_apply, UnitaryFieldData.bar_apply, pow_one, of_apply]
    rw [SetLike.mem_coe, mem_unitarySU_iff unitaryFieldData_two_one, Set.mem_ofPred_eq, hbar,
      Units.ext_iff, GeneralLinearGroup.val_det_apply, Units.val_one, and_comm]
  rw [timmesfeldPSU, hset, Subgroup.closure_eq]

@[expose] noncomputable def timmesfeldPSUEquiv {n : ℕ} (hn : 1 ≤ n) :
    timmesfeldPSU n ≃* unitaryPSU unitaryFieldData_two_one n :=
  (MulEquiv.subgroupCongr (timmesfeldPSU_eq_map n)).trans
    ((mapMkEquiv (unitarySU 2 1 (GaloisField 2 2) n)).trans
      (QuotientGroup.quotientMulEquivOfEq (by
        rw [unitaryScalars_eq unitaryFieldData_two_one hn,
          CFSG.Assembly.LowTwoRank.StatedScalars,
          GeneralLinearGroup.center_eq_range_scalar])))

end CFSG.LargeExtraspecial.S14
