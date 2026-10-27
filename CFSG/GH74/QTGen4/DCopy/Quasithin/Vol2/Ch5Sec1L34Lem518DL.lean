module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518DL
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Inputs518DL
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem518
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem522Y

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

section Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem eq_B_of_inner_F4 (hF : L2TorusFact) (h510 : Stmt5_1_10_F4) (h516 : Stmt5_1_16_F4)
    {D₃ : Subgroup G} (hD₃ : D₃ ≤ D) (h3 : Nat.card D₃ = 3)
    (hD₃M : D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    (hin : ∀ d ∈ D₃, ∃ k ∈ oTwoUpper H, d * k⁻¹ ∈ centralizerModO2 (oTwoUpper H)) :
    D₃ = B := by
  have hh := h.hyp.toHyp5_0_1
  have hC3 : ¬ 3 ∣ Nat.card ↥(centralizerModO2 (oTwoUpper H)) :=
    (h516 G T M L V H B D n h.hyp h.notation59 h.module h.l34).1

  have hD₃K : D₃ ≤ oTwoUpper H := by
    intro d hd
    obtain ⟨k, hk, hc⟩ := hin d hd
    have hd3 : d ^ 3 = 1 := by
      have h' := pow_card_eq_one' (G := ↥D₃) (x := ⟨d, hd⟩)
      rw [h3] at h'
      exact congrArg Subtype.val h'
    exact mem_of_mul_inv_mem_of_pow_three (centralizerModO2_le_normalizer (oTwoUpper H)) hC3
      (hD₃M hd) hd3 hk hc

  have hD₃MH : D₃ ≤ M ⊓ H :=
    le_inf (hD₃.trans (h.notation59.2.1.1.trans (inf_le_left.trans hh.L_le)))
      (hD₃K.trans (oTwoUpper_le H))

  have hB3 : Nat.card B = 3 := h.card_B_eq_three_F4 h510
  have hP3 : IsPGroup 3 ↥(B ⊔ D₃) := by
    have hB : IsPGroup 3 ↥B := IsPGroup.of_card (n := 1) (by rw [hB3, pow_one])
    have hD : IsPGroup 3 ↥D₃ := IsPGroup.of_card (n := 1) (by rw [h3, pow_one])
    exact hB.to_sup_of_normal_right' hD (h.B_le_normalizer_of_le_D hF hD₃)
  have hsupMH : B ⊔ D₃ ≤ M ⊓ H := sup_le h.notation59.1.1 hD₃MH
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP3
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hh.sylow.1
  have hdvd : 3 ^ a ∣ 2 ^ m * 3 := by
    rw [← ha, ← hm, ← hB3, ← h.hyp.card_inf_eq h.notation59]
    exact Subgroup.card_dvd_of_le hsupMH
  have ha1 : 3 ^ a ∣ 3 :=
    (Nat.Coprime.pow a m (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_left hdvd
  have hle : Nat.card ↥(B ⊔ D₃) ≤ Nat.card B := by
    rw [ha, hB3]
    exact Nat.le_of_dvd (by norm_num) ha1
  have hBeq : B = B ⊔ D₃ := Subgroup.eq_of_le_of_card_ge le_sup_left hle
  have hD₃B : D₃ ≤ B := by
    rw [hBeq]
    exact le_sup_right
  exact Subgroup.eq_of_le_of_card_ge hD₃B (by rw [hB3, h3])

end Hyp5_1_14

end Setting

theorem stmt5_1_18_DL_of_F4 (hF : L2TorusFact) (h510 : Stmt5_1_10_F4) (h516 : Stmt5_1_16_F4)
    (hOut : Stmt5_1_18_DL_outer_F4) : Stmt5_1_18_DL_F4 := by
  intro G _ _ T M L V H B D n h hev D₃ hD₃ h3 hD₃M hne
  by_cases hin : ∀ d ∈ D₃, ∃ k ∈ oTwoUpper H, d * k⁻¹ ∈ centralizerModO2 (oTwoUpper H)
  · exact absurd (h.eq_B_of_inner_F4 hF h510 h516 hD₃ h3 hD₃M hin) hne
  · push Not at hin
    exact hOut G T M L V H B D n h hev D₃ hD₃ h3 hD₃M hin

theorem stmt5_1_18_of_reduced_F4 (hF : L2TorusFact) (h510 : Stmt5_1_10_F4) (h515 : Stmt5_1_15_F4)
    (h516 : Stmt5_1_16_F4) (h5114 : Stmt5_1_14_first_F4) (h517 : Stmt5_1_17_F4)
    (hOut : Stmt5_1_18_DL_outer_F4) (hD5 : Stmt5_1_18_D5_F4) : Stmt5_1_18_F4 :=
  stmt5_1_18_of_inputs_F4 hF h515 h5114 h517 (stmt5_1_18_DL_of_F4 hF h510 h516 hOut) hD5

end CFSG.Quasithin.H13
