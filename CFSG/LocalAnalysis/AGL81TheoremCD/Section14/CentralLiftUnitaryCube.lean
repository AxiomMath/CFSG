module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLiftDefs
public import CFSG.RankThree.PartTwo.KFacts.AutPSU

import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLiftKlein
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUnitaryAut
import CFSG.RankThree.PartOne.KF.UnitaryDiag

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.RankThree.PartOne.KFU
open Matrix

variable {p f : ℕ} {F : Type} [Field F]

private theorem fixesKleinFour_suConj_of_pow_three_eq_one (h : UnitaryFieldData p f F)
    (h2 : (2 : F) ≠ 0) (h3 : 3 ∣ p ^ f + 1) {S : unitaryIsom3 h} (hS3 : S ^ 3 = 1) :
    FixesKleinFour (suConj h S) := by
  have memU : ∀ {A : GL (Fin 3) F}, A ∈ primeFormUnitary h (idGram F 3) → A ∈ unitaryIsom3 h := by
    intro A hA
    have hA' : ((A : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (idGram F 3) *
        (A : Matrix (Fin 3) (Fin 3) F) = idGram F 3 := hA
    rw [show idGram F 3 = 1 from rfl, Matrix.mul_one] at hA'
    exact hA'
  let S' : primeFormUnitary h (idGram F 3) := ⟨S, mem_primeFormUnitary_one S.2⟩
  have hS'3 : S' ^ 3 = 1 := by
    apply Subtype.ext
    exact congrArg (fun x : unitaryIsom3 h => (x : GL (Fin 3) F)) hS3
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag h Nat.prime_three h3 (Subgroup.zpowers S')
    (fun a ha b hb => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_zpow_self S' m n).eq)
    (fun a ha => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hS'3,
        _root_.one_zpow])
  have hDdiag : ((((P⁻¹ * S' * P : primeFormUnitary h (idGram F 3)) : GL (Fin 3) F)) :
      Matrix (Fin 3) (Fin 3) F).IsDiag := hP S' (Subgroup.mem_zpowers S')
  let Pu : unitaryIsom3 h := ⟨P, memU P.2⟩
  let D : unitaryIsom3 h :=
    ⟨(P⁻¹ * S' * P : primeFormUnitary h (idGram F 3)), memU (P⁻¹ * S' * P).2⟩
  have hDdiagD : (((D : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F).IsDiag := hDdiag
  have hS_eq : S = Pu * D * Pu⁻¹ := by
    apply Subtype.ext
    change (S : GL (Fin 3) F) = (P : GL (Fin 3) F) *
      (((P⁻¹ * S' * P : primeFormUnitary h (idGram F 3)) : GL (Fin 3) F)) *
      (P : GL (Fin 3) F)⁻¹
    have hcoe : (((P⁻¹ * S' * P : primeFormUnitary h (idGram F 3)) : GL (Fin 3) F)) =
        (P : GL (Fin 3) F)⁻¹ * (S' : GL (Fin 3) F) * (P : GL (Fin 3) F) := rfl
    rw [hcoe, show ((S' : primeFormUnitary h (idGram F 3)) : GL (Fin 3) F) =
      (S : GL (Fin 3) F) from rfl]
    group
  rw [hS_eq, map_mul, map_mul, map_inv]
  exact (fixesKleinFour_suConj_of_isDiag h h2 hDdiagD).conj (suConj h Pu)

theorem fixesKleinFour_of_pow_three_eq_cube (h : UnitaryFieldData p f F) (hp2 : p ≠ 2)
    (h3 : 3 ∣ p ^ f + 1) (B : unitaryIsom3 h) {μ : Fˣ}
    (hB : (B : GL (Fin 3) F) ^ 3 =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (μ ^ 3)) :
    FixesKleinFour (suConj h B) := by
  have h2 : (2 : F) ≠ 0 := by
    have := h.charP
    exact Ring.two_ne_zero (by rw [ringChar.eq F p]; exact hp2)
  have hμ : h.norm (μ : F) = 1 := by
    have hmem : Matrix.GeneralLinearGroup.scalar (Fin 3) (μ ^ 3) ∈ unitaryIsom3 h := by
      rw [← hB]
      exact pow_mem B.2 3
    have hnorm3 : h.norm ((μ ^ 3 : Fˣ) : F) = 1 := by
      have h1 := congrFun (congrFun (mem_unitaryIsom3.1 hmem) 0) 0
      rw [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_map (map_zero h.bar),
        diagonal_transpose, diagonal_mul_diagonal, diagonal_apply_eq, one_apply_eq] at h1
      rw [UnitaryFieldData.norm, mul_comm]
      exact h1
    exact norm_eq_one_of_pow_three h h3 μ hnorm3
  have hcN : h.norm ((μ⁻¹ : Fˣ) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hμ, inv_one]
  let S : unitaryIsom3 h :=
    ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) (μ⁻¹), scalar_mem_unitaryIsom3 h hcN⟩ * B
  have hS3 : S ^ 3 = 1 := by
    apply Subtype.ext
    change ((Matrix.GeneralLinearGroup.scalar (Fin 3) (μ⁻¹) : GL (Fin 3) F) *
      (B : GL (Fin 3) F)) ^ 3 = (1 : GL (Fin 3) F)
    have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin 3) (μ⁻¹))
        (B : GL (Fin 3) F) :=
      (commute_scalar (μ⁻¹) (B : GL (Fin 3) F)).symm
    rw [hcomm.mul_pow, hB, ← MonoidHom.map_pow, ← MonoidHom.map_mul, inv_pow,
      inv_mul_cancel, MonoidHom.map_one]
  have hBS : suConj h B = suConj h S := by
    rw [show S = ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) (μ⁻¹),
      scalar_mem_unitaryIsom3 h hcN⟩ * B from rfl, map_mul, suConj_scalar h hcN, one_mul]
  rw [hBS]
  exact fixesKleinFour_suConj_of_pow_three_eq_one h h2 h3 hS3

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift
