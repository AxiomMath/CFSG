module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P2bP1
public import CFSG.LocalAnalysis.EvenBN.Tits.N.Steps

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Open
open CFSG.LocalAnalysis.EvenBN.Tits CFSG.LocalAnalysis.EvenBN.Tits.Data
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem P2b.N_inf_C_F_le_P (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (h07 : Node07 d) (h08 : Node08 d z₀) (h11 : Node11 d z₀) {x : G} (hxN : x ∈ d.N)
    (hxF : ∀ f ∈ d.F, f * x = x * f) : x ∈ d.s56P := by
  have h1 := P2b.conj_t_mem_tF h49 hd hxN
  rw [← P2b.orbit_t_P1 h49 hd hz h07 h08 h11] at h1
  obtain ⟨p, hp, hpt⟩ := h1
  have hpF : ∀ f ∈ d.F, f * p = p * f := (P2b.mem_P_iff.1 (P2b.P1_le_P hp)).2
  have hqt : p⁻¹ * x * d.t = d.t * (p⁻¹ * x) := by
    have e1 : x * d.t * x⁻¹ = p * d.t * p⁻¹ := hpt.symm
    have e2 : x * d.t = p * d.t * p⁻¹ * x := by
      calc x * d.t = (x * d.t * x⁻¹) * x := by group
        _ = p * d.t * p⁻¹ * x := by rw [e1]
    calc p⁻¹ * x * d.t = p⁻¹ * (x * d.t) := by group
      _ = p⁻¹ * (p * d.t * p⁻¹ * x) := by rw [e2]
      _ = d.t * (p⁻¹ * x) := by group
  have hqf : ∀ f ∈ d.F, f * (p⁻¹ * x) = (p⁻¹ * x) * f := by
    intro f hf
    have hfp : f * p⁻¹ = p⁻¹ * f := (Commute.inv_right (show Commute f p from hpF f hf)).eq
    calc f * (p⁻¹ * x) = (f * p⁻¹) * x := by group
      _ = (p⁻¹ * f) * x := by rw [hfp]
      _ = p⁻¹ * (f * x) := by group
      _ = p⁻¹ * (x * f) := by rw [hxF f hf]
      _ = (p⁻¹ * x) * f := by group
  have hle : d.B ≤ centralizer ({p⁻¹ * x} : Set G) :=
    sup_le (fun f hf => mem_centralizer_singleton_iff.2 (hqf f hf))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 hqt.symm))
  have hqC : p⁻¹ * x ∈ centralizer (d.B : Set G) :=
    mem_centralizer_iff.2 fun b hb => mem_centralizer_singleton_iff.1 (hle hb)
  rw [hd.centralizer_B] at hqC
  have hxe : x = p * (p⁻¹ * x) := by group
  rw [hxe]
  exact mul_mem (P2b.P1_le_P hp) (hd.s56_B_le_P hqC)

theorem P2b.maxElemAbelian2_N_or (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (h07 : Node07 d) (h08 : Node08 d z₀) (h11 : Node11 d z₀) :
    CFSG.Open.pRank 2 d.N < 10 ∨
      (IsElemAbelian 2 (P1 d) ∧ Nat.card (P1 d) = 2 ^ 10 ∧ maxElemAbelian2 d.N = {P1 d}) := by
  have hrank : ∀ K : Subgroup G, K ≤ centralizer ({d.t} : Set G) → IsElemAbelian 2 K →
      Nat.card K ≤ 2 ^ 6 := fun K hK hKa => hd.card_le_of_isElemAbelian hK hKa
  have hoff : ∀ D : Subgroup G, D ≤ d.N → IsElemAbelian 2 D →
      Nat.card D ≤ 2 ^ 10 ∧ (2 ^ 10 ≤ Nat.card D → d.t ∉ D ∧
        Nat.card (D ⊓ centralizer ({d.t} : Set G) : Subgroup G) = 2 ^ 5 ∧
        {y | ∃ k ∈ D, k * d.t * k⁻¹ = y} = (fun f => d.t * f) '' (d.F : Set G) ∧
        ∀ r ∈ D, r * d.t = d.t * r → ∀ x ∈ (fun f => d.t * f) '' (d.F : Set G),
          r * x = x * r) :=
    fun D hDN hDe => P2b.offender hd.t_mul_self (P2b.ncard_tF hd) hrank hDe
      (fun k hk => P2b.conj_t_mem_tF h49 hd (hDN hk))
  have hB : ∀ D : Subgroup G, D ≤ d.N → IsElemAbelian 2 D → 2 ^ 10 ≤ Nat.card D →
      D = P1 d := by
    intro D hDN hDe hge
    obtain ⟨htD, hR, hO, hcent⟩ := (hoff D hDN hDe).2 hge
    have hRF : (D ⊓ centralizer ({d.t} : Set G) : Subgroup G) ≤ d.F := by
      intro r hr
      obtain ⟨hrD, hrC⟩ := mem_inf.1 hr
      have hrt : r * d.t = d.t * r := mem_centralizer_singleton_iff.1 hrC
      have hrF : ∀ f ∈ d.F, f * r = r * f := by
        intro f hf
        have h1 := hcent r hrD hrt (d.t * f) ⟨f, hf, rfl⟩
        have h2 : d.t * (r * f) = d.t * (f * r) :=
          calc d.t * (r * f) = (d.t * r) * f := by group
            _ = (r * d.t) * f := by rw [hrt]
            _ = r * (d.t * f) := by group
            _ = d.t * f * r := h1
            _ = d.t * (f * r) := by group
        exact (mul_left_cancel h2).symm
      have hle : d.B ≤ centralizer ({r} : Set G) :=
        sup_le (fun f hf => mem_centralizer_singleton_iff.2 (hrF f hf))
          (zpowers_le.2 (mem_centralizer_singleton_iff.2 hrt.symm))
      have hrB : r ∈ d.B := by
        have hrC' : r ∈ centralizer (d.B : Set G) :=
          mem_centralizer_iff.2 fun b hb => mem_centralizer_singleton_iff.1 (hle hb)
        rwa [hd.centralizer_B] at hrC'
      rcases ((hd.tSup_facts (d.liftSub_le _ : d.F ≤ d.L)).1 r).1 hrB with h | h
      · exact h
      · exfalso
        obtain ⟨f, hf, hfr⟩ : ∃ f ∈ d.F, r = d.t * f :=
          ⟨d.t * r, h, by rw [← mul_assoc, hd.t_mul_self, one_mul]⟩
        have hrD' : d.t * f ∈ D := hfr ▸ hrD
        have hte : d.t * f ∈ (fun f => d.t * f) '' (d.F : Set G) := ⟨f, hf, rfl⟩
        rw [← hO] at hte
        obtain ⟨k, hk, hkt⟩ := hte
        have hf1 : f = 1 := P2b.eq_one_of_mem hDe hrD' hk hkt
        apply htD
        have e2 : d.t = d.t * f := by rw [hf1, mul_one]
        rw [e2]
        exact hrD'
    have hFeq : (D ⊓ centralizer ({d.t} : Set G) : Subgroup G) = d.F := by
      refine Subgroup.eq_of_le_of_card_ge hRF ?_
      rw [hR, hd.B_facts.1]
      norm_num
    have hFD : d.F ≤ D := by
      rw [← hFeq]
      exact inf_le_left
    have hDP : D ≤ d.s56P := fun a ha =>
      P2b.N_inf_C_F_le_P h49 hd hz h07 h08 h11 (hDN ha)
        (fun f hf => P2b.elemAb_comm hDe (hFD hf) ha)
    have hDP1 : D ≤ P1 d := by
      intro a ha
      by_contra haP1
      obtain ⟨f, hf, rfl⟩ := P2b.inv_P_not_P1 h49 hd hz h07 h08 h11 a (hDP ha) haP1
        (P2b.elemAb_mul_self hDe ha)
      apply htD
      have e2 : d.t = d.t * f * f⁻¹ := by group
      rw [e2]
      exact mul_mem ha (inv_mem (hFD hf))
    exact Subgroup.eq_of_le_of_card_ge hDP1 (by rw [P2b.card_P1 h11]; exact hge)
  by_cases hex : ∃ D : Subgroup G, D ≤ d.N ∧ IsElemAbelian 2 D ∧ 2 ^ 10 ≤ Nat.card D
  · right
    obtain ⟨D, hDN, hDe, hDge⟩ := hex
    have hDeq : D = P1 d := hB D hDN hDe hDge
    have hP1e : IsElemAbelian 2 (P1 d) := hDeq ▸ hDe
    have hP1N : P1 d ≤ d.N := P2b.P1_le_P.trans P2b.P_le_N
    refine ⟨hP1e, P2b.card_P1 h11, ?_⟩
    ext D'
    rw [Set.mem_singleton_iff]
    constructor
    · rintro ⟨hD'N, hD'e, hD'max⟩
      refine hB D' hD'N hD'e ?_
      have h := hD'max (P1 d) hP1N hP1e
      rw [P2b.card_P1 h11] at h
      exact h
    · rintro rfl
      exact ⟨hP1N, hP1e, fun D'' hD''N hD''e => by
        rw [P2b.card_P1 h11]
        exact (hoff D'' hD''N hD''e).1⟩
  · left
    have hlt : ∀ D : Subgroup G, D ≤ d.N → IsElemAbelian 2 D → Nat.card D < 2 ^ 10 := by
      intro D hDN hDe
      by_contra h
      exact hex ⟨D, hDN, hDe, not_lt.1 h⟩
    have hbot : (⊥ : Subgroup G) ≤ d.N := bot_le
    have hbota : IsElemAbelian 2 (⊥ : Subgroup G) :=
      P2b.elemAb_of (fun a ha b hb => by
          rw [Subgroup.mem_bot] at ha hb
          rw [ha, hb])
        (fun a ha => by
          rw [Subgroup.mem_bot] at ha
          rw [ha, mul_one])
    have hne : {k | ∃ E : Subgroup G, E ≤ d.N ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k}.Nonempty :=
      ⟨0, ⊥, hbot, hbota, by simp⟩
    have hbdd : BddAbove {k | ∃ E : Subgroup G, E ≤ d.N ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} := by
      refine ⟨9, ?_⟩
      rintro k ⟨E, hE, hEa, hc⟩
      have h := hlt E hE hEa
      rw [hc] at h
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h
      omega
    obtain ⟨E, hE, hEa, hc⟩ := Nat.sSup_mem hne hbdd
    have h := hlt E hE hEa
    rw [hc] at h
    unfold CFSG.Open.pRank
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h

theorem step13_holds : Step13 := by
  intro G _ _ d z₀ h49 hd hz h07 h08 _h10 h11 _h12
  exact ⟨⟨P2b.inv_P_not_P1 h49 hd hz h07 h08 h11, P2b.orbit_t_P1 h49 hd hz h07 h08 h11⟩,
    P2b.maxElemAbelian2_N_or h49 hd hz h07 h08 h11⟩

end CFSG.LocalAnalysis.EvenBN.Tits.N
