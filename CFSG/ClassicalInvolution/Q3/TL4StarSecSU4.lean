module

public import CFSG.ClassicalInvolution.Q3.TL4StarSecPair
public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LSU01
public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LSU02
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.Q3.Q3PP (F9 card_F9 two_ne_zero_F9)
open CFSG.ClassicalInvolution.Q3.Q3AM (pair01 pair02 pair12 zMat_pair01 zMat_pair02 zMat_pair12
  uElt suMat_uElt uElt_mul_self uElt_comm uElt_mem_LcU zEltU_pair02_mul_pair01 LcU_center)

section Swap

@[expose] noncomputable def xMat : Matrix (Fin 4) (Fin 4) F9 :=
  !![0, 0, 1, 0; 0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1]

theorem det_xMat : xMat.det = 1 := by
  have h : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 := rfl
  rw [Matrix.det_succ_row_zero]
  simp [xMat, Fin.sum_univ_succ, Matrix.det_fin_three, h]

theorem conjTr_xMat_mul : conjTr (unitaryInvolution F9 3 1) xMat * xMat = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [xMat, conjTr, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply,
      Matrix.map_apply]

@[expose] noncomputable def xElt : Su F9 3 1 4 :=
  Models.mkSU F9 3 1 xMat det_xMat conjTr_xMat_mul

theorem suMat_xElt : suMat xElt = xMat := rfl

theorem xElt_mul_self : xElt * xElt = zEltU F9 3 1 pair02 := by
  apply suMat_injective
  rw [suMat_mul, suMat_xElt, suMat_zEltU, zMat_pair02]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [xMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem xElt_mem_LcU : xElt ∈ LcU F9 3 1 pair02 := by
  show xElt ∈ longRootGroupSU F9 3 1 (zMat F9 4 pair02.1)
  rw [mem_longRootGroupSU, suMat_xElt, zMat_pair02]
  constructor
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [xMat, Matrix.mul_apply, Fin.sum_univ_four]
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [xMat, Matrix.mul_apply, Fin.sum_univ_four]

variable {i : F9}

theorem uElt_mul_xElt_mul_uElt (hi : i * i = -1) (hσi : unitaryInvolution F9 3 1 i = -i) :
    uElt hi hσi * xElt * uElt hi hσi = xElt := by
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_uElt, suMat_xElt]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [xMat, Matrix.mul_apply, Matrix.diagonal_apply, hi]

theorem xElt_mul_zEltU : xElt * zEltU F9 3 1 pair01 = zEltU F9 3 1 pair12 * xElt := by
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_xElt, suMat_zEltU, suMat_zEltU, zMat_pair01, zMat_pair12]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [xMat, Matrix.mul_apply, Matrix.diagonal_apply]

end Swap

section Kind

theorem zEltU_not_mem_center (T : Pair 4) : zEltU F9 3 1 T ∉ Subgroup.center (Su F9 3 1 4) :=
  fun hc => zEltU_ne_one two_ne_zero_F9 T (LcU_center T
    (isUniqueInvolution_LcU card_F9 (by norm_num) (by norm_num) T).mem hc)

theorem orderOf_eq_four_of_mul_self {y : Su F9 3 1 4} {T : Pair 4}
    (hy : y * y = zEltU F9 3 1 T) : orderOf y = 4 := by
  have h1 : ¬ y ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two, hy]
    exact zEltU_ne_one two_ne_zero_F9 T
  have h2 : y ^ 2 ^ (1 + 1) = 1 := by
    rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, pow_two y, hy, pow_two, zEltU_mul_self]
  simpa using orderOf_eq_prime_pow h1 h2


variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem starNbr_of_su4 (hR : TypeRFam 3 Φ) (htr : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L')
    (h : SecIdQ8Shape (CompData.model .PSU 4) Φ) :
    ∀ L ∈ Φ, ∃ L' ∈ Φ, L' ∈ omegaStarNbr Φ L ∧ L' ∉ omegaNbr Φ L := by
  obtain ⟨φ, -, hk, hfund⟩ := h
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  obtain ⟨e, he⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) (by norm_num) hadm
  set ψ : Su F9 3 1 4 →* X := φ.comp e.symm.toMonoidHom with hψ
  have hker : ψ.ker ≤ Subgroup.center (Su F9 3 1 4) := by
    intro x hx
    have h1 : e.symm x ∈ φ.ker := hx
    have h2 := Subgroup.mem_map_of_mem (e : (CompData.model .PSU 4).G →* Su F9 3 1 4) (hk h1)
    rw [Subgroup.map_center_eq e] at h2
    simpa using h2
  have hfund' : ∀ L ∈ Φ, ∃ R ∈ longRootSetU (K := F9) (p := 3) (f := 1) (show 2 ≤ 4 by norm_num),
      IsSylow2In L (R.map ψ) := by
    intro L hL
    obtain ⟨R, hR', hLR⟩ := hfund L hL
    refine ⟨R.map e.toMonoidHom, (he R).mp hR', ?_⟩
    have hmap : (R.map e.toMonoidHom).map ψ = R.map φ := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [hψ]
    rw [hmap]
    exact hLR
  obtain ⟨i, hi, hσi⟩ := Q3MFOU4.exists_iota
  have hU := isUniqueInvolution_LcU (p := 3) (f := 1) card_F9 (by norm_num) (by norm_num) pair01
  have hxu : xElt * uElt hi hσi * xElt⁻¹ = (uElt hi hσi)⁻¹ := by
    calc xElt * uElt hi hσi * xElt⁻¹ =
        (uElt hi hσi)⁻¹ * (uElt hi hσi * xElt * uElt hi hσi) * xElt⁻¹ := by group
      _ = (uElt hi hσi)⁻¹ := by rw [uElt_mul_xElt_mul_uElt]; group
  have hxa : xElt * zEltU F9 3 1 pair01 * xElt⁻¹ * (zEltU F9 3 1 pair01)⁻¹ =
      zEltU F9 3 1 pair02 := by
    have hinv : (zEltU F9 3 1 pair01)⁻¹ = zEltU F9 3 1 pair01 :=
      inv_eq_of_mul_eq_one_right (zEltU_mul_self pair01)
    have h01 := zEltU_mul_self (K := F9) (p := 3) (f := 1) pair01
    calc xElt * zEltU F9 3 1 pair01 * xElt⁻¹ * (zEltU F9 3 1 pair01)⁻¹
        = zEltU F9 3 1 pair12 * xElt * xElt⁻¹ * zEltU F9 3 1 pair01 := by
          rw [xElt_mul_zEltU, hinv]
      _ = zEltU F9 3 1 pair02 * (zEltU F9 3 1 pair01 * zEltU F9 3 1 pair01) := by
          rw [mul_inv_cancel_right, ← zEltU_pair02_mul_pair01, mul_assoc]
      _ = zEltU F9 3 1 pair02 := by rw [h01, mul_one (zEltU F9 3 1 pair02)]
  refine starNbr_of_pair hker hfund' (fun R hR' R' hR'' => Q3AM.exists_conj_map_longRoot ψ hR' hR'')
    (LcU_mem_longRootSetU two_ne_zero_F9 _ pair01) (LcU_mem_longRootSetU two_ne_zero_F9 _ pair02)
    hU.mem (fun y hy => hU.commute_of_mem hy) (zEltU_mul_self pair01)
    (zEltU_not_mem_center pair01) (uElt_mem_LcU hi hσi) xElt_mem_LcU
    (orderOf_eq_four_of_mul_self (uElt_mul_self hi hσi)) (orderOf_eq_four_of_mul_self xElt_mul_self)
    (by rw [uElt_mul_self]; exact zEltU_not_mem_center pair02) hxu (uElt_comm hi hσi)
    (by rw [hxa]; exact zEltU_not_mem_center pair02) hR htr

end Kind

end CFSG.ClassicalInvolution.Q3.TL4
