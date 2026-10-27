module

public import CFSG.ClassicalInvolution.Asc77.AscT7F2Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7T

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}

theorem exists_hyp25T (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) :
    ∃ t' : G, T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t' := by
  obtain ⟨t', ht'S, ⟨g, hg⟩, hconj⟩ := c25_2_t_proved p f G Ω K K' W S R R' z t u₁ u₂ hyp
  have hzz : z * z = 1 := hyp.std.setting.hz.sq
  have ht'2 : t' * t' = 1 := by
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  exact ⟨t', hyp, ht'S, ht'2, hconj⟩

theorem Csub_eq_of_11_16 (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    (h11 : C25_11 p f) (h16 : C25_16 p f) (hN : C25_17_norm p f) :
    T7F2.Csub S R' = R := by
  have hRC : R ≤ T7F2.Csub S R' := h.R_le_C'
  have hcN : Nat.card ↥(T7F2.Nsub S R) ≤ 2 * Nat.card ↥(R ⊔ R') :=
    hN G Ω K K' W S R R' z t u₁ u₂ h.hyp
  have hRR' : Nat.card R' = Nat.card R := h.card_R'_eq
  have hC : Nat.card ↥(T7F2.Csub S R') ≤ 2 * Nat.card R := by
    rw [← hRR']
    exact h.card_C_le h11 h16
  have hP' := h.card_P' h11
  have hRR := h.card_RR
  have hR0 : 0 < Nat.card R := Nat.card_pos
  have hC0 : 0 < Nat.card ↥(T7F2.Csub S R') := Nat.card_pos
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hRC
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hm
      omega
    · exact h0
  have hm2 : m ≤ 2 := by
    by_contra hm2
    push Not at hm2
    have h3 : Nat.card R * 3 ≤ Nat.card R * m := Nat.mul_le_mul_left _ hm2
    rw [← hm] at h3
    omega
  interval_cases m
  · exact (Subgroup.eq_of_le_of_card_ge hRC (by omega)).symm
  · exfalso
    have hq : Nat.card ↥(T7F2.Hyp25T.Psub S R') = Nat.card R * Nat.card R := by
      have h2 : Nat.card ↥(T7F2.Hyp25T.Psub S R') * 2 = (Nat.card R * Nat.card R) * 2 := by
        calc _ = Nat.card R' * Nat.card ↥(T7F2.Csub S R') := hP'
          _ = Nat.card R * (Nat.card R * 2) := by rw [hRR', hm]
          _ = (Nat.card R * Nat.card R) * 2 := by ring
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
    have hρ : Nat.card ↥(R ⊔ R') * 2 = Nat.card R * Nat.card R := by rw [hRR, hRR']
    have hPN : T7F2.Hyp25T.Psub S R' = T7F2.Nsub S R :=
      Subgroup.eq_of_le_of_card_ge h.P'_le_N (by omega)
    have hcardP : Nat.card ↥(T7F2.Hyp25T.Psub S R) = Nat.card ↥(T7F2.Hyp25T.Psub S R') := by
      rw [← h.conj_P', AscL62.natCard_conjSub]
    have hPN2 : T7F2.Hyp25T.Psub S R = T7F2.Nsub S R :=
      Subgroup.eq_of_le_of_card_ge h.P_le_N (by omega)
    have hle : T7F2.Csub S R' ≤ R := by
      intro c hc
      have hcN' : c ∈ T7F2.Hyp25T.Psub S R := hPN2 ▸ h.C'_le_N hc
      obtain ⟨ρ, hρR, y, hy, hcy⟩ := T7F2.Out.exists_mul_of_mem_sup_of_commute
        (A := R) (B := T7F2.Csub S R)
        (fun x hx y hy => (T7F2.mem_Csub.mp hy).2 x hx) hcN'
      have hyS : y ∈ (S : Subgroup G) := (T7F2.mem_Csub.mp hy).1
      have hy' : y ∈ T7F2.Csub S R' := by
        refine T7F2.mem_Csub.mpr ⟨hyS, fun r hr => ?_⟩
        have h1 : r * c = c * r := (T7F2.mem_Csub.mp hc).2 r hr
        have h2 : r * ρ = ρ * r := (h.hcomm ρ hρR r hr).symm
        rw [hcy] at h1
        have h3 : ρ * (r * y) = ρ * (y * r) := by
          calc ρ * (r * y) = (ρ * r) * y := by group
            _ = (r * ρ) * y := by rw [h2]
            _ = r * (ρ * y) := by group
            _ = (ρ * y) * r := h1
            _ = ρ * (y * r) := by group
        exact mul_left_cancel h3
      have hyz : y ∈ Subgroup.zpowers z := h.Csub_inf_Csub_le h11 ⟨hy, hy'⟩
      have hzR : Subgroup.zpowers z ≤ R := Subgroup.zpowers_le.mpr h.hzR.mem
      rw [hcy]
      exact R.mul_mem hρR (hzR hyz)
    have := Subgroup.card_le_of_le hle
    omega

theorem c25_15_of_11_16 (h11 : C25_11 p f) (h16 : C25_16 p f) : C25_15 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  obtain ⟨t', h⟩ := exists_hyp25T hyp
  exact Or.inl (Csub_eq_of_11_16 h h11 h16 (c25_17_norm_of_11_16 p f h11 h16))

end T7T

end CFSG.ClassicalInvolution.Asc77
