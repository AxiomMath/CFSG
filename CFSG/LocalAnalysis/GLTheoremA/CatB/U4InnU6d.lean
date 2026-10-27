module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnU6c
import CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Fischer CFSG.StandardType CFSG.Assembly
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

namespace U4InnU6

theorem pPrimeCore_CenD_cube_one (B : primeFormUnitary hF4 (idGram F4 6)) (hB3 : B ^ 3 = 1)
    (hns : ¬ ∃ c : F4ˣ, (B : GL (Fin 6) F4) = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    (hL : ∃ L : Subgroup M6, L ≤ CenD (B : GL (Fin 6) F4) ∧ Group.IsPerfect ↥L ∧
      25920 ∣ Nat.card L) :
    CFSG.pPrimeCore 3 ↥(CenD (B : GL (Fin 6) F4)) = ⊥ := by
  obtain ⟨P, d, hd⟩ := exists_diag6 B hB3
  set D : GL (Fin 6) F4 :=
    ((P⁻¹ * B * P : primeFormUnitary hF4 (idGram F4 6)) : GL (Fin 6) F4) with hDdef
  have hDeq : D = (P : GL (Fin 6) F4)⁻¹ * (B : GL (Fin 6) F4) * (P : GL (Fin 6) F4) := rfl
  have hDd : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d := hd
  have hmap := map_CenD_conj P⁻¹ (B : GL (Fin 6) F4)
  have hCen : ((P⁻¹ : primeFormUnitary hF4 (idGram F4 6)) : GL (Fin 6) F4) *
      (B : GL (Fin 6) F4) * ((P⁻¹ : primeFormUnitary hF4 (idGram F4 6)) : GL (Fin 6) F4)⁻¹ = D := by
    rw [hDeq]
    simp
  rw [hCen] at hmap
  obtain ⟨L, hLC, hLp, hLd⟩ := hL
  let φ := (conjM6 P⁻¹).toMonoidHom
  have hLC' : L.map φ ≤ CenD D := by
    rw [← hmap]
    exact Subgroup.map_mono hLC
  have hLp' : Group.IsPerfect ↥(L.map φ) := by
    rw [Subgroup.isPerfect_iff, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.1 hLp]
  have hLd' : 25920 ∣ Nat.card ↥(L.map φ) := by
    rwa [Subgroup.card_map_of_injective (conjM6 P⁻¹).injective]
  suffices h : CFSG.pPrimeCore 3 ↥(CenD D) = ⊥ by
    have e : ↥(CenD (B : GL (Fin 6) F4)) ≃* ↥(CenD D) :=
      (Subgroup.equivMapOfInjective _ φ (conjM6 P⁻¹).injective).trans
        (MulEquiv.subgroupCongr hmap)
    exact pPrimeCore_eq_bot_of_mulEquiv e h
  have hnc : ¬ ∀ i, d i = d 0 := by
    intro hconst
    apply hns
    have hd0 : d 0 ≠ 0 := by
      intro h0
      have h1 := congrFun (congrFun (D.val_inv) 0) 0
      rw [hDd, Matrix.diagonal_mul, h0, zero_mul] at h1
      exact zero_ne_one h1
    refine ⟨Units.mk0 (d 0) hd0, ?_⟩
    have hDs : D = Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 (d 0) hd0) := by
      apply Units.ext
      rw [hDd, Matrix.GeneralLinearGroup.coe_scalar]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hconst i]
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    have hB : (B : GL (Fin 6) F4) = (P : GL (Fin 6) F4) * D * (P : GL (Fin 6) F4)⁻¹ := by
      rw [hDeq]
      group
    rw [hB, hDs, (commute_scalar (Units.mk0 (d 0) hd0) (P : GL (Fin 6) F4)).eq, mul_inv_cancel_right]
  by_cases hbig : ∃ c : F4, 4 ≤ Fintype.card (Blk d c)
  · obtain ⟨c, hc4⟩ := hbig
    have hc5 := card_blk_le_five d hnc c
    have hsmall : ∀ c' : F4, c' ≠ c → Fintype.card (Blk d c') ≤ 2 := fun c' hc' => by
      have := card_blk_add_le d (c := c) (c' := c') (Ne.symm hc')
      omega
    exact pPrimeCore_CenD_of_K1 hDd
      (pPrimeCore_K1_big hDd c hc4 hc5 hsmall ⟨L.map φ, hLC', hLp', hLd'⟩)
  · push Not at hbig
    exfalso
    have hbot := eq_bot_of_perfect_of_small hDd (fun c => by have := hbig c; omega) hLC'
      (Subgroup.isPerfect_iff.1 hLp')
    rw [hbot, Subgroup.card_bot] at hLd'
    exact absurd (Nat.le_of_dvd one_pos hLd') (by norm_num)

end U4InnU6

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
