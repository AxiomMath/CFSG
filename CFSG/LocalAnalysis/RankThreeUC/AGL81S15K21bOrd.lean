module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21bPts
import CFSG.Quasithin.Vol2.Ch11SecBL2UKp

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21bOrdProof

open Matrix K21bUniProof K21bPtsProof

variable {F : Type} [Field F]

theorem card_eq_two_pow [Finite F] [CharP F 2] : ∃ n : ℕ, 1 ≤ n ∧ Nat.card F = 2 ^ n := by
  haveI := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card]; exact hn⟩

theorem center_inf_U0 {z : SpecialLinearGroup (Fin 3) F}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F)) (hU : z ∈ U0 F) : z = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have h00 := ((mem_U0_iff z).mp hU).2.2.2.1
  have hr0 : r = (z : Matrix (Fin 3) (Fin 3) F) 0 0 := by
    rw [← hr]
    simp
  have hr1 : r = 1 := by rw [hr0, h00]
  refine Subtype.ext ?_
  rw [← hr, hr1]
  simp

theorem injOn_mk_U0 :
    Set.InjOn (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 3) F)))
      (U0 F : Set (SpecialLinearGroup (Fin 3) F)) := by
  intro g hg h hh hgh
  have hc : g⁻¹ * h ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F) :=
    QuotientGroup.eq.mp hgh
  have hU : g⁻¹ * h ∈ U0 F := (U0 F).mul_mem ((U0 F).inv_mem hg) hh
  exact (inv_mul_eq_one.mp (center_inf_U0 hc hU))

theorem card_U0P : Nat.card (U0P F) = Nat.card F ^ 3 := by
  have h1 : ((U0P F : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)) :
      Set (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)) =
      (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 3) F))) ''
        ((U0 F : Subgroup (SpecialLinearGroup (Fin 3) F)) : Set (SpecialLinearGroup (Fin 3) F)) :=
    Subgroup.coe_map _ _
  calc Nat.card (U0P F)
      = ((U0P F : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)) :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)).ncard := Nat.card_coe_set_eq _
    _ = ((QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 3) F))) ''
        ((U0 F : Subgroup (SpecialLinearGroup (Fin 3) F)) :
          Set (SpecialLinearGroup (Fin 3) F))).ncard := by rw [h1]
    _ = ((U0 F : Subgroup (SpecialLinearGroup (Fin 3) F)) :
          Set (SpecialLinearGroup (Fin 3) F)).ncard := injOn_mk_U0.ncard_image
    _ = Nat.card (U0 F) := (Nat.card_coe_set_eq _).symm
    _ = Nat.card F ^ 3 := card_U0

theorem card_psl_three [Finite F] [CharP F 2] :
    ∃ m : ℕ, ¬ 2 ∣ m ∧
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) = Nat.card F ^ 3 * m := by
  obtain ⟨n, hn1, hq⟩ := card_eq_two_pow (F := F)
  have hpsl := CFSG.Quasithin.Vol2.Ch11.SecB.card_psl_eq_ordA (K := F) (n := 3) (by norm_num)
  have hI : Finset.Icc 2 (2 + 1) = {2, 3} := by decide
  have hord : CFSG.Open.ordA (3 - 1) (Nat.card F) =
      Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) /
        Nat.gcd 3 (Nat.card F - 1) := by
    unfold CFSG.Open.ordA
    rw [show 3 - 1 = 2 by norm_num, hI, Finset.prod_pair (show (2 : ℕ) ≠ 3 by norm_num)]
  rw [hord] at hpsl
  generalize Nat.card F = q at hq hpsl
  have hqe : 2 ∣ q := by
    rw [hq]
    exact dvd_pow_self 2 (by omega)
  have hq1 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
  have h2sq : 2 ∣ q ^ 2 := dvd_pow hqe (by norm_num)
  have h2cu : 2 ∣ q ^ 3 := dvd_pow hqe (by norm_num)
  have hpos2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hpos3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hN : ¬ 2 ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := by
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h <;> omega
  have hgN : Nat.gcd 3 (q - 1) ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := by
    have h1 : Nat.gcd 3 (q - 1) ∣ q - 1 := Nat.gcd_dvd_right 3 (q - 1)
    have h2 : q - 1 ∣ q ^ 2 - 1 := Nat.sub_one_dvd_pow_sub_one q 2
    exact (h1.trans h2).trans (dvd_mul_right _ _)
  have hg3 : Nat.gcd 3 (q - 1) ∣ 3 := Nat.gcd_dvd_left 3 (q - 1)
  have hgpos : 0 < Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  obtain ⟨m, hm⟩ := hgN
  refine ⟨m, ?_, ?_⟩
  · intro h2m
    exact hN (by rw [hm]; exact Dvd.dvd.mul_left h2m _)
  · rw [hpsl, hm]
    calc q ^ 3 * (Nat.gcd 3 (q - 1) * m) / Nat.gcd 3 (q - 1)
        = Nat.gcd 3 (q - 1) * (q ^ 3 * m) / Nat.gcd 3 (q - 1) := by rw [mul_left_comm]
      _ = q ^ 3 * m := Nat.mul_div_cancel_left _ hgpos

theorem isSylowOf_U0P [Finite F] [CharP F 2] : CFSG.ABGLocalTools.IsSylowOf 2 (U0P F) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, ?_, ?_⟩
  · obtain ⟨n, -, hq⟩ := card_eq_two_pow (F := F)
    have h1 : IsPGroup 2 (U0 F) :=
      IsPGroup.of_card (n := n * 3) (by rw [card_U0, hq, ← pow_mul])
    exact h1.map _
  · rw [Subgroup.relIndex_top_right]
    obtain ⟨m, hm, hcard⟩ := card_psl_three (F := F)
    have h1 := Subgroup.card_mul_index (U0P F)
    rw [card_U0P, hcard] at h1
    have hq0 : 0 < Nat.card F ^ 3 := pow_pos Nat.card_pos 3
    rw [Nat.eq_of_mul_eq_mul_left hq0 h1]
    exact hm

end K21bOrdProof

end CFSG.LocalAnalysis.RankThreeUC.S15
