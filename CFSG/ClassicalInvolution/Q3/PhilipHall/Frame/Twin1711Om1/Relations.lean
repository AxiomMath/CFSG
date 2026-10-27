module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om1.Basic
public import Certificates.Certificate197001

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check

set_option linter.unusedSectionVars false

private theorem coe_zW : ((zW : WP) : Equiv.Perm (Fin 240)) = zPerm := rfl

theorem zW_comm (x : WP) : x * zW = zW * x := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_zW]
  exact zPerm_comm _ (wPlus_le x.2)

theorem zW_mul_self : zW * zW = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_one, coe_zW]
  exact zPerm_mul_self

theorem i0_mul_self : i0 * i0 = t0 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_i0, coe_t0]
  exact Certificates.certificate197001.1.2.1

theorem g1_conj_t0 : g1 * t0 * g1⁻¹ = t0 * zW := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_g1, coe_t0,
    coe_zW_eq_z]
  exact Certificates.certificate197001.1.2.2.2.2.1

theorem wordOK_of_sub {ws : List (List ℕ)} (h : ∀ w ∈ ws, w ∈ allWords) : ∀ w ∈ ws, wordOK w = true :=
  fun w hw => wordOK_of_allWords (h w hw)

theorem wT_sub : ∀ w ∈ wT, w ∈ allWords := by
  intro w hw
  simp only [wT, List.mem_append] at hw
  simp only [allWords, List.mem_append]
  tauto

theorem wCa_sub : ∀ w ∈ wCa, w ∈ allWords := by
  intro w hw
  simp only [wCa, List.mem_append] at hw
  simp only [allWords, List.mem_append]
  tauto

theorem wCc_sub : ∀ w ∈ wCc, w ∈ allWords := by
  intro w hw
  simp only [wCc, List.mem_append] at hw
  simp only [allWords, List.mem_append]
  tauto

theorem wX_sub : ∀ w ∈ wX, w ∈ allWords := by
  intro w hw
  simp only [allWords, List.mem_append]
  tauto

theorem wS0_sub : ∀ w ∈ wS0, w ∈ allWords := by
  intro w hw
  simp only [allWords, List.mem_append]
  tauto

theorem wP3_sub : ∀ w ∈ wP3, w ∈ allWords := by
  intro w hw
  simp only [allWords, List.mem_append]
  tauto

theorem wSa_sub : ∀ w ∈ wSa, w ∈ allWords := by
  intro w hw
  simp only [allWords, List.mem_append]
  tauto

theorem wSc_sub : ∀ w ∈ wSc, w ∈ allWords := by
  intro w hw
  simp only [allWords, List.mem_append]
  tauto

theorem wPa3_sub : ∀ w ∈ wPa3, w ∈ allWords := by
  intro w hw
  simp only [allWords, List.mem_append]
  tauto

theorem wPa5_sub : ∀ w ∈ wPa5, w ∈ allWords := by
  intro w hw
  simp only [allWords, List.mem_append]
  tauto

theorem wPc_sub : ∀ w ∈ wPc, w ∈ allWords := by
  intro w hw
  simp only [allWords, List.mem_append]
  tauto

theorem comm_t0_of_mem {w : List ℕ} (hw : w ∈ wT ++ [wS1]) : wpE w * t0 = t0 * wpE w := by
  have hA : w ∈ allWords := by
    rcases List.mem_append.1 hw with h | h
    · exact wT_sub w h
    · rw [List.mem_singleton.1 h]
      simp [allWords]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_wpE_eq_E (wordOK_of_allWords hA), coe_t0]
  exact (Certificates.certificate197001.1.2.2.2.2.2.1 w hw).eq

theorem comm_ta_of_mem {w : List ℕ} (hw : w ∈ wCa) : wpE w * ta = ta * wpE w := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_wpE_eq_E (wordOK_of_allWords (wCa_sub w hw)), coe_ta]
  exact (Certificates.certificate197001.1.2.2.2.2.2.2.1 w hw).eq

theorem comm_tc_of_mem {w : List ℕ} (hw : w ∈ wCc) : wpE w * tc = tc * wpE w := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_wpE_eq_E (wordOK_of_allWords (wCc_sub w hw)), coe_tc]
  exact (Certificates.certificate197001.1.2.2.2.2.2.2.2.1 w hw).eq

theorem tb_eq : tb = zW * ta := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_zW_eq_z, coe_ta, coe_tb]
  exact Certificates.certificate197001.1.2.2.2.2.2.2.2.2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1
