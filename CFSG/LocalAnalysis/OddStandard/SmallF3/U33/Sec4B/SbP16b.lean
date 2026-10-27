module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP16a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

namespace Setting16

variable {G : Type} [Group G] [Finite G] {Q Y : Subgroup G} {τ ω : G}

theorem exists_not_mem_Y (h : Setting16 Q Y τ ω) : ∃ q ∈ Q, q ∉ Y := by
  by_contra hc
  push Not at hc
  have hQY : Q ≤ Y := fun q hq => hc q hq
  have hcard := Subgroup.card_le_of_le hQY
  rw [h.card_Q, h.card_Y] at hcard
  omega

theorem exists_om_noninv (h : Setting16 Q Y τ ω) : ∃ q ∈ Q, (ω * q) ^ 2 ≠ 1 := by
  by_contra hc
  push Not at hc
  obtain ⟨q, hq, hqY⟩ := exists_not_mem_Y h
  exact hqY (h.invol_om q hq (hc q hq))

theorem exists_omtau_noninv (h : Setting16 Q Y τ ω) : ∃ q ∈ Q, (ω * τ * q) ^ 2 ≠ 1 := by
  by_contra hc
  push Not at hc
  obtain ⟨q, hq, hqY⟩ := exists_not_mem_Y h
  exact hqY (h.invol_omtau q hq (hc q hq))

private theorem commute_of_mem_Y (h : Setting16 Q Y τ ω) {y : G} (hy : y ∈ Y) :
    ∀ g : G, g * y = y * g := by
  have hyQ : y ∈ Q := h.Y_le_Q hy
  have hy2 : y ^ 2 = 1 := ((h.mem_Y y).mp hy).2
  have hyinv : y⁻¹ = y := by
    apply inv_eq_of_mul_eq_one_right
    rwa [pow_two] at hy2
  have hyτ : Commute y τ := by
    rw [Commute]
    have h1 : τ * y * τ⁻¹ = y := by rw [h.tau_inv y hyQ, hyinv]
    calc y * τ = (τ * y * τ⁻¹) * τ := by rw [h1]
      _ = τ * y := by group
  have hyω : Commute y ω := (h.om_cent_Y y hy).symm
  have hyq : ∀ q ∈ Q, Commute y q := fun q hq => h.comm y hyQ q hq
  intro g
  obtain ⟨q, hq, hcases⟩ := h.cosets g
  rcases hcases with hg | hg | hg | hg
  · rw [hg]
    exact h.comm q hq y hyQ
  · rw [hg]
    exact ((hyq q hq).mul_right hyτ).eq.symm
  · rw [hg]
    exact ((hyq q hq).mul_right hyω).eq.symm
  · rw [hg]
    exact ((hyq q hq).mul_right (hyτ.mul_right hyω)).eq.symm

theorem Y_le_center (h : Setting16 Q Y τ ω) : Y ≤ center G := by
  intro y hy
  exact Subgroup.mem_center_iff.mpr (commute_of_mem_Y h hy)

theorem not_central_tau (h : Setting16 Q Y τ ω) {q : G} (hq : q ∈ Q)
    (hz : ∀ a ∈ Q, (q * τ) * a = a * (q * τ)) : False := by
  obtain ⟨a, ha, ha2⟩ := h.exists_sq
  apply ha2
  have h1 : q * (a⁻¹ * τ) = q * (a * τ) := by
    calc q * (a⁻¹ * τ) = q * (τ * a) := by rw [h.tau_mul ha]
      _ = (q * τ) * a := by group
      _ = a * (q * τ) := hz a ha
      _ = (a * q) * τ := by group
      _ = (q * a) * τ := by rw [h.comm a ha q hq]
      _ = q * (a * τ) := by group
  have h2 : a⁻¹ * τ = a * τ := mul_left_cancel h1
  have h3 : a⁻¹ = a := mul_right_cancel h2
  rw [pow_two]
  nth_rewrite 1 [← h3]
  rw [inv_mul_cancel]

theorem not_central_om (h : Setting16 Q Y τ ω) {q : G} (hq : q ∈ Q)
    (hzτ : (q * ω) * τ = τ * (q * ω)) (hzQ : ∀ a ∈ Q, (q * ω) * a = a * (q * ω)) : False := by
  obtain ⟨a, ha, ha2⟩ := h.exists_sq
  apply ha2
  have h1 : q * (ω * a) = q * (a * ω) := by
    calc q * (ω * a) = (q * ω) * a := by group
      _ = a * (q * ω) := hzQ a ha
      _ = (a * q) * ω := by group
      _ = (q * a) * ω := by rw [h.comm a ha q hq]
      _ = q * (a * ω) := by group
  have h2 : ω * a = a * ω := mul_left_cancel h1
  exact ((h.mem_Y a).mp (h.cent_om a ha h2)).2

theorem not_central_tau_om (h : Setting16 Q Y τ ω) {q : G} (hq : q ∈ Q)
    (hzQ : ∀ a ∈ Q, (q * (τ * ω)) * a = a * (q * (τ * ω))) : False := by
  have hconj : ∀ a ∈ Q, ω * a * ω⁻¹ = a⁻¹ := by
    intro a ha
    have ha' : ω * a * ω⁻¹ ∈ Q := h.normal.conj_mem a ha ω
    have key : q * ((ω * a * ω⁻¹)⁻¹ * (τ * ω)) = q * (a * (τ * ω)) := by
      calc q * ((ω * a * ω⁻¹)⁻¹ * (τ * ω))
          = q * (τ * (ω * a * ω⁻¹) * ω) := by rw [h.tau_mul ha']; group
        _ = q * (τ * (ω * a)) := by group
        _ = (q * (τ * ω)) * a := by group
        _ = a * (q * (τ * ω)) := hzQ a ha
        _ = (a * q) * (τ * ω) := by group
        _ = (q * a) * (τ * ω) := by rw [h.comm a ha q hq]
        _ = q * (a * (τ * ω)) := by group
    have h1 : (ω * a * ω⁻¹)⁻¹ * (τ * ω) = a * (τ * ω) := mul_left_cancel key
    have h2 : (ω * a * ω⁻¹)⁻¹ = a := mul_right_cancel h1
    have hinv := congrArg Inv.inv h2
    simpa using hinv
  obtain ⟨a, ha, ha2⟩ := h.exists_sq
  apply ha2
  have hsq : (ω * a) ^ 2 = 1 := by
    have hstep : (ω * a) ^ 2 = (ω * a * ω⁻¹) * a := by
      rw [pow_two]
      nth_rewrite 2 [← h.om_inv_eq]
      group
    rw [hstep, hconj a ha, inv_mul_cancel]
  exact ((h.mem_Y a).mp (h.invol_om a ha hsq)).2

theorem center_le_Y (h : Setting16 Q Y τ ω) : center G ≤ Y := by
  intro z hz
  obtain ⟨q, hq, hcases⟩ := h.cosets z
  rcases hcases with hzq | hzqτ | hzqω | hzqτω
  · rw [hzq] at hz ⊢
    exact h.cent_om q hq (Subgroup.mem_center_iff.mp hz ω)
  · exfalso
    rw [hzqτ] at hz
    exact h.not_central_tau hq (fun a ha => (Subgroup.mem_center_iff.mp hz a).symm)
  · exfalso
    rw [hzqω] at hz
    exact h.not_central_om hq ((Subgroup.mem_center_iff.mp hz τ).symm)
      (fun a ha => (Subgroup.mem_center_iff.mp hz a).symm)
  · exfalso
    rw [hzqτω] at hz
    exact h.not_central_tau_om hq (fun a ha => (Subgroup.mem_center_iff.mp hz a).symm)

theorem center_eq (h : Setting16 Q Y τ ω) : center G = Y :=
  le_antisymm (center_le_Y h) (Y_le_center h)

theorem char_Y (h : Setting16 Q Y τ ω) : Y.Characteristic := by
  rw [← center_eq h]
  exact Subgroup.centerCharacteristic

end Setting16

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
