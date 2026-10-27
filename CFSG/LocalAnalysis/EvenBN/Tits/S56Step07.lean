module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Steps
public import CFSG.LocalAnalysis.EvenBN.Tits.S56P11
public import CFSG.LocalAnalysis.EvenBN.Tits.S56N5
public import CFSG.LocalAnalysis.EvenBN.Tits.S56N6

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped Pointwise commutatorElement

section Step07


theorem step07_holds : Step07 := by
  intro G _ _ d h49 hd
  obtain ⟨hyNC, hyL, hy3, hy1, hy10, -, -⟩ := hd.s56_Y_facts
  have hyN : d.s56Y ∈ d.N := (mem_inf.1 hyNC).1
  have hzB : ∀ b ∈ d.B, d.z * b = b * d.z :=
    (hd.s56_E_cent_B_iff hd.s56_z_mem_E).2 hd.s56_z_mem_F
  have htr : ∀ e ∈ d.E, e ∉ d.F → ∀ b ∈ d.B,
      (e * b * e⁻¹ = b ∨ e * b * e⁻¹ = b * d.z) ∧ (e * b * e⁻¹ = b ↔ b ∈ d.A) := by
    intro e he heF b hb
    have hax := hd.s56_E_axis_B he heF hb
    have hiff : e * b * e⁻¹ = b ↔ b ∈ d.A := by
      rw [← hax]
      constructor
      · intro h
        calc e * b = (e * b * e⁻¹) * e := by group
          _ = b * e := by rw [h]
      · intro h
        calc e * b * e⁻¹ = (b * e) * e⁻¹ := by rw [h]
          _ = b := by group
    refine ⟨?_, hiff⟩
    rcases hd.s56_mem_zpowers_z (hd.s56_E_comm_B_mem he hb) with h | h
    · left
      calc e * b * e⁻¹ = (e * b * e⁻¹ * b⁻¹) * b := by group
        _ = b := by rw [h, one_mul]
    · right
      calc e * b * e⁻¹ = (e * b * e⁻¹ * b⁻¹) * b := by group
        _ = d.z * b := by rw [h]
        _ = b * d.z := hzB b hb
  refine ⟨⟨d.s56Y, mem_inf.2 ⟨hyN, hyL⟩, ?_, hy10⟩, ?_, (hd.s56_CF_P0_eq h49).symm,
    (hd.s56_CN_U11_eq h49).symm, fun n hn u hu => hd.s56_N_conj_U10 h49 hn hu, ?_,
    hd.s56_N_quot_P10_equiv h49, ?_, ?_, ?_, fun p => hd.s56_P0_inf_M_iff h49,
    hd.s56_P0_inf_M_relIndex h49⟩
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hy3 hy1
  ·
    rintro y ⟨hyNL, hyo, -⟩
    have hyN' : y ∈ d.N := (mem_inf.1 hyNL).1
    have hy3' : y ^ 3 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
    have hy1' : y ≠ 1 := by
      rintro rfl
      simp at hyo
    obtain ⟨ha, -, -, -, hcases⟩ := hd.s56_y_orbit h49 hyN' hy3' hy1'
    apply le_antisymm
    · exact sup_le (zpowers_le.2 d.s56_z_mem_U11) (zpowers_le.2 ha)
    · intro x hx
      rcases hcases x hx with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact mem_sup_left (mem_zpowers _)
      · exact mem_sup_right (mem_zpowers _)
      · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))
  ·
    ext n
    constructor
    · rintro ⟨q, hq, c, hc, rfl⟩
      exact mul_mem (d.s56_P10_le_N hq) (mem_inf.1 hc).1
    · intro hn
      obtain ⟨q, hq, c, hc, rfl⟩ := hd.s56_N_decomp_P10 h49 hn
      exact ⟨q, hq, c, hc, rfl⟩
  ·
    exact Subgroup.commutator_le.2 fun p hp f hf => hd.s56_P0_comm_F_le_U10 h49 hp hf
  ·
    exact Subgroup.commutator_le.2 fun c hc b hb =>
      hd.s56_comm_P10_CNt_B h49 (mem_inf.1 hc).1 (mem_inf.1 hc).2 hb
  ·
    have h8F : d.pv 8 ∉ d.F := hd.s56_pv8_not_mem_F
    have h8E : d.pv 8 ∈ d.E := d.s56_pv8_mem_E
    have h7B : d.pv 7 ∈ d.B := d.s56_F_le_B hd.s56_pv7_mem_F
    refine ⟨d.pv 8, h8E, ⟨inf_le_right, ?_, ?_, fun b hb => ?_⟩, fun e' he' => ?_⟩
    · exact mem_inf.2 ⟨d.s56_E_le_A hd.s56_z_mem_E, d.s56_F_le_B hd.s56_z_mem_F⟩
    · refine ⟨d.pv 7, h7B, fun h => ?_⟩
      have hA := (hd.s56_E_axis_B h8E h8F h7B).2 (mem_inf.1 h).1
      apply hd.s56_z_ne_one
      rw [← hd.s56_pv8_comm_pv7, hA]
      group
    · obtain ⟨h1, h2⟩ := htr _ h8E h8F b hb
      exact ⟨h1, fun h => mem_inf.2 ⟨h2.1 h, hb⟩, fun h => h2.2 (mem_inf.1 h).1⟩
    · by_cases he'F : e' ∈ d.F
      · left
        exact mem_centralizer_iff.2 fun b hb => ((hd.s56_E_cent_B_iff he').2 he'F b hb).symm
      · right
        intro b hb
        obtain ⟨h1, h2⟩ := htr _ he' he'F b hb
        obtain ⟨h1', h2'⟩ := htr _ h8E h8F b hb
        by_cases hbA : b ∈ d.A
        · rw [h2.2 hbA, h2'.2 hbA]
        · rw [h1.resolve_left (mt h2.1 hbA), h1'.resolve_left (mt h2'.1 hbA)]

end Step07

end CFSG.LocalAnalysis.EvenBN.Tits.N
