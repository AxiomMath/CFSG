module

public import CFSG.ClassicalInvolution.Asc77.AscT7F2Cnt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7G2

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


section Struct

open T7F2

variable (h : Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')

include h

theorem conj_mem_RR {x : G} (hx : x ∈ (S : Subgroup G)) {ρ : G} (hρ : ρ ∈ R ⊔ R') :
    x * ρ * x⁻¹ ∈ R ⊔ R' := by
  obtain ⟨r, hr, r', hr', rfl⟩ := Out.exists_mul_of_mem_sup_of_commute h.hcomm hρ
  have e : x * (r * r') * x⁻¹ = (x * r * x⁻¹) * (x * r' * x⁻¹) := by group
  rw [e]
  refine (R ⊔ R').mul_mem ?_ ?_
  · have h1 := conj_mem_conjSub (n := x) hr
    rcases h.perm_R hx with h2 | h2
    · rw [h2] at h1; exact (le_sup_left : R ≤ R ⊔ R') h1
    · rw [h2] at h1; exact (le_sup_right : R' ≤ R ⊔ R') h1
  · have h1 := conj_mem_conjSub (n := x) hr'
    rcases h.perm_R' hx with h2 | h2
    · rw [h2] at h1; exact (le_sup_left : R ≤ R ⊔ R') h1
    · rw [h2] at h1; exact (le_sup_right : R' ≤ R ⊔ R') h1

variable (h11 : C25_11 p f) (h16 : C25_16 p f)

include h11 h16

theorem struct (h4 : Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R')) :
    Csub S R' = R ∧ Csub S R = R' ∧ Hyp25T.Psub S R' = R ⊔ R' ∧ Hyp25T.Psub S R = R ⊔ R' ∧
      (R ⊔ R').relIndex (Nsub S R) = 2 := by
  have hSN := T7ER.card_eq_two_mul_normalizer h.hyp
  have hNc : Nat.card ↥(Nsub S R) = 2 * Nat.card ↥(R ⊔ R') := by
    have : Nat.card ↥(S : Subgroup G) = 2 * Nat.card ↥(Nsub S R) := hSN
    omega
  have hi := h.relIndex_P'_le h16
  have hc := h.card_C_le h11 h16
  have hq := h.card_P' h11
  have hρ := h.card_RR
  have hn := h.card_N
  have hrr : Nat.card R = Nat.card R' := h.card_R_eq
  have hdvd : Nat.card R ∣ Nat.card ↥(Csub S R') := Subgroup.card_dvd_of_le h.R_le_C'
  rw [hrr] at hdvd hρ
  obtain ⟨k, hk⟩ := hdvd
  have hr : 0 < Nat.card R' := Nat.card_pos
  have hρpos : 0 < Nat.card ↥(R ⊔ R') := Nat.card_pos
  have hcpos : 0 < Nat.card ↥(Csub S R') := Nat.card_pos
  set r := Nat.card R' with hrdef
  set ρ := Nat.card ↥(R ⊔ R') with hρdef
  set c := Nat.card ↥(Csub S R') with hcdef
  set q := Nat.card ↥(Hyp25T.Psub S R') with hqdef
  set n := Nat.card ↥(Nsub S R) with hndef
  set i := (Hyp25T.Psub S R').relIndex (Nsub S R) with hidef
  have hk2 : k ≤ 2 := by
    have : r * k ≤ r * 2 := by rw [← hk]; linarith
    exact Nat.le_of_mul_le_mul_left this hr
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  have hqk : q = ρ * k := by
    have h2 : q * 2 = (ρ * k) * 2 := by
      calc q * 2 = r * c := hq
        _ = r * (r * k) := by rw [hk]
        _ = (r * r) * k := by ring
        _ = (ρ * 2) * k := by rw [← hρ]
        _ = (ρ * k) * 2 := by ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  have hi0 : i ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hn
    omega
  have hik : i * k = 2 := by
    have h1 : i * (ρ * k) = 2 * ρ := by rw [← hqk, hn, hNc]
    have h2 : ρ * (i * k) = ρ * 2 := by nlinarith
    exact Nat.eq_of_mul_eq_mul_left hρpos h2
  have hcard : Nat.card ↥(Hyp25T.Psub S R) = Nat.card ↥(Hyp25T.Psub S R') := by
    rw [← h.conj_P', AscL62.natCard_conjSub]
  have hk1 : k = 1 := by
    by_contra hk1
    have hk2' : k = 2 := by omega
    have hi1 : i = 1 := by rw [hk2'] at hik; omega
    have hNP' : Nsub S R ≤ Hyp25T.Psub S R' := Subgroup.relIndex_eq_one.mp hi1
    have hNeq : Hyp25T.Psub S R' = Nsub S R := le_antisymm h.P'_le_N hNP'
    have hPN : Hyp25T.Psub S R = Nsub S R := by
      refine Subgroup.eq_of_le_of_card_ge h.P_le_N ?_
      rw [hcard, hNeq]
    have hCR : Csub S R' ≤ R := by
      intro x hx
      have hxN : x ∈ Nsub S R := h.C'_le_N hx
      have hxP : x ∈ Hyp25T.Psub S R := by rw [hPN]; exact hxN
      obtain ⟨ρ₁, hρ₁, m, hm, hxm⟩ := T7F2.Out.exists_mul_of_mem_sup_of_commute
        (A := R) (B := Csub S R) (fun x hx y hy => (mem_Csub.mp hy).2 x hx) hxP
      obtain ⟨hmS, hmR⟩ := mem_Csub.mp hm
      obtain ⟨hxS, hxR'⟩ := mem_Csub.mp hx
      have hρ₁S : ρ₁ ∈ (S : Subgroup G) := h.hRS hρ₁
      have hmR' : m ∈ Csub S R' := by
        refine mem_Csub.mpr ⟨hmS, fun y hy => ?_⟩
        have e : m = ρ₁⁻¹ * x := by rw [hxm]; group
        have h1 := h.hcomm ρ₁ hρ₁ y hy
        have h2 := hxR' y hy
        have h3 : y * ρ₁⁻¹ = ρ₁⁻¹ * y := by
          calc y * ρ₁⁻¹ = ρ₁⁻¹ * (ρ₁ * y) * ρ₁⁻¹ := by group
            _ = ρ₁⁻¹ * (y * ρ₁) * ρ₁⁻¹ := by rw [h1]
            _ = ρ₁⁻¹ * y := by group
        rw [e]
        calc y * (ρ₁⁻¹ * x) = (y * ρ₁⁻¹) * x := by group
          _ = (ρ₁⁻¹ * y) * x := by rw [h3]
          _ = ρ₁⁻¹ * (y * x) := by group
          _ = ρ₁⁻¹ * (x * y) := by rw [h2]
          _ = (ρ₁⁻¹ * x) * y := by group
      have hmz : m ∈ Subgroup.zpowers z := h.Csub_inf_Csub_le h11 ⟨hm, hmR'⟩
      have hzR : Subgroup.zpowers z ≤ R := Subgroup.zpowers_le.mpr h.hzR.mem
      rw [hxm]
      exact R.mul_mem hρ₁ (hzR hmz)
    have hle := Subgroup.card_le_of_le hCR
    rw [hk2'] at hk
    rw [hrr, ← hcdef] at hle
    omega
  have hi2 : i = 2 := by rw [hk1] at hik; omega
  have hC' : Csub S R' = R := by
    symm
    refine Subgroup.eq_of_le_of_card_ge h.R_le_C' ?_
    have e : Nat.card ↥(Csub S R') = r * k := hk
    rw [hrr, e, hk1, mul_one]
  have hP' : Hyp25T.Psub S R' = R ⊔ R' := by
    symm
    refine Subgroup.eq_of_le_of_card_ge h.RR_le_P' ?_
    have e : Nat.card ↥(Hyp25T.Psub S R') = ρ * k := hqk
    rw [e, hk1, mul_one]
  have hP : Hyp25T.Psub S R = R ⊔ R' := by
    symm
    refine Subgroup.eq_of_le_of_card_ge h.RR_le_P ?_
    have e : Nat.card ↥(Hyp25T.Psub S R') = ρ * k := hqk
    rw [hcard, e, hk1, mul_one]
  have hC : Csub S R = R' := by
    symm
    refine Subgroup.eq_of_le_of_card_ge h.R'_le_C ?_
    have e : Nat.card ↥(Csub S R') = r * k := hk
    rw [h.card_C_eq, e, hk1, mul_one]
  refine ⟨hC', hC, hP', hP, ?_⟩
  have h2 := Subgroup.relIndex_mul_card (R ⊔ R') (Nsub S R)
  rw [inf_eq_left.mpr (sup_le h.R_le_N h.R'_le_N)] at h2
  have hρ0 : 0 < ρ := hρpos
  have : (R ⊔ R').relIndex (Nsub S R) * ρ = 2 * ρ := by rw [h2]; exact hNc
  exact Nat.eq_of_mul_eq_mul_right hρ0 this

end Struct

end T7G2

end CFSG.ClassicalInvolution.Asc77
