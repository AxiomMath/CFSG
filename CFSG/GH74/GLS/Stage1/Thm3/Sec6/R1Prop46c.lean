module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Prop46b

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec4.M CFSG.GH74.GLS CFSG.GH74

variable {G : Type} [Group G] [Finite G] {z : G} {S P Q F : Subgroup G} {FA : G → Prop}

omit [Finite G] in
theorem isCyclic_of_le {F Q : Subgroup G} (hQF : Q ≤ F) (hF : IsCyclic ↥F) : IsCyclic ↥Q := by
  have : IsCyclic ↥(Q.subgroupOf F) := inferInstance
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hQF).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hQF).surjective

namespace Cfg1

theorem exists_x_Q (h : Cfg1 G z S P Q F FA) (hF : IsCyclic ↥F) (hQ8 : 8 ≤ Nat.card ↥Q) {y u₂ : G}
    (hyS : y ∈ S) (hu₂ : u₂ ∈ Q) (h2 : u₂ * u₂ = z) (hinv : y * u₂ * y⁻¹ = u₂⁻¹) :
    ∃ x ∈ Q, x * y * x⁻¹ = u₂ * y := by
  have hQc : IsCyclic ↥Q := isCyclic_of_le h.Q_le_F hF
  have hF2 : IsPGroup 2 ↥F := h.S_pgroup.to_le h.F_le
  have hQ2 : IsPGroup 2 ↥Q := h.S_pgroup.to_le h.Q_le
  obtain ⟨c, hcQ, hgen⟩ := exists_gen_of_cyclic hQc
  have hQgen : Q = zpowers c := le_antisymm (fun v hv => hgen v hv) (zpowers_le.2 hcQ)
  have hNord : orderOf c = Nat.card ↥Q := by
    have : Nat.card ↥Q = orderOf c := by rw [hQgen]; exact Nat.card_zpowers c
    exact this.symm
  obtain ⟨k0, hk0⟩ := (IsPGroup.iff_card).1 hQ2
  have h2dvd : 2 ∣ orderOf c := by
    rw [hNord, hk0]
    have : k0 ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk0
      omega
    exact dvd_pow_self 2 this
  have hordsq : orderOf (c * c) = orderOf c / 2 := by
    rw [← sq]; exact orderOf_pow_of_dvd (by norm_num) h2dvd
  have hcc : c * c ∈ F := mul_mem (h.Q_le_F hcQ) (h.Q_le_F hcQ)
  have hu₂4 : u₂ ^ 4 = 1 := by
    have e : u₂ ^ 4 = (u₂ * u₂) * (u₂ * u₂) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e, h2]; exact h.z_sq
  have hu₂le : orderOf u₂ ≤ Nat.card ↥(zpowers (c * c)) := by
    rw [Nat.card_zpowers, hordsq]
    have h1 : orderOf u₂ ≤ 4 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hu₂4)
    have h3 : 8 ≤ orderOf c := by rw [hNord]; exact hQ8
    omega
  have hu₂mem : u₂ ∈ zpowers (c * c) :=
    B.mem_of_orderOf_le hF (zpowers_le.2 hcc) hF2 (h.Q_le_F hu₂) hu₂le
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hu₂mem
  have hrQ : c ^ k ∈ Q := Q.zpow_mem hcQ k
  have hrr : c ^ k * c ^ k = u₂ := by
    rw [← hk]
    exact ((Commute.refl c).mul_zpow k).symm
  generalize c ^ k = r at hrQ hrr
  have hrS : r ∈ S := h.Q_le hrQ
  have hr'Q : y * r * y⁻¹ ∈ Q := h.Q_norm y hyS r hrQ
  have hrF : r ∈ F := h.Q_le_F hrQ
  have hr'F : y * r * y⁻¹ ∈ F := h.Q_le_F hr'Q
  have hsq1 : (y * r * y⁻¹ * r) * (y * r * y⁻¹ * r) = 1 := by
    have hc : r * (y * r * y⁻¹) = (y * r * y⁻¹) * r := comm_of_cyclic hF hrF hr'F
    calc (y * r * y⁻¹ * r) * (y * r * y⁻¹ * r)
        = (y * r * y⁻¹) * (r * (y * r * y⁻¹)) * r := by group
      _ = (y * r * y⁻¹) * ((y * r * y⁻¹) * r) * r := by rw [hc]
      _ = (y * (r * r) * y⁻¹) * (r * r) := by group
      _ = (y * u₂ * y⁻¹) * u₂ := by rw [hrr]
      _ = u₂⁻¹ * u₂ := by rw [hinv]
      _ = 1 := inv_mul_cancel u₂
  rcases h.invol_F hF (mul_mem hr'F hrF) hsq1 with e | e
  · refine ⟨r, hrQ, ?_⟩
    have hr'e : y * r * y⁻¹ = r⁻¹ := eq_inv_of_mul_eq_one_left e
    calc r * y * r⁻¹ = r * (y * r * y⁻¹)⁻¹ * y := by group
      _ = r * (r⁻¹)⁻¹ * y := by rw [hr'e]
      _ = (r * r) * y := by group
      _ = u₂ * y := by rw [hrr]
  · refine ⟨r⁻¹, Q.inv_mem hrQ, ?_⟩
    have hr'e : y * r * y⁻¹ = z * r⁻¹ := eq_mul_inv_of_mul_eq e
    have hzr : z * r⁻¹ = r⁻¹ * z := h.z_cent r⁻¹ (S.inv_mem hrS)
    have hinvr : r⁻¹ * r⁻¹ = u₂ * z := by
      rw [← mul_inv_rev, hrr]; exact h.inv_eq_mul_z h2
    calc r⁻¹ * y * r⁻¹⁻¹ = r⁻¹ * (y * r * y⁻¹) * y := by group
      _ = r⁻¹ * (z * r⁻¹) * y := by rw [hr'e]
      _ = r⁻¹ * (r⁻¹ * z) * y := by rw [hzr]
      _ = (r⁻¹ * r⁻¹) * z * y := by group
      _ = (u₂ * z) * z * y := by rw [hinvr]
      _ = u₂ * (z * z) * y := by group
      _ = u₂ * y := by rw [h.z_sq]; group

end Cfg1

namespace Cfg1K

theorem exists_conj_yu (h : Cfg1K G z S P Q F FA) (hF : IsCyclic ↥F)
    (hSR : ∀ a ∈ S, ∀ b ∈ S, a * b * a⁻¹ * b⁻¹ ∈ P ⊔ Q) (hTr : HTransfer G S)
    {y : G} (hy : Is47b S P F y) (hzy : IsConj z y) {u u₁ u₂ : G} (hu₁P : u₁ ∈ P) (hu₂Q : u₂ ∈ Q)
    (hu : u = u₁ * u₂) (hu₁sq : u₁ * u₁ = z) (hu₂sq : u₂ * u₂ = z) (hu1 : u ≠ 1)
    (hyu : y * u = u * y) (hinv₂ : y * u₂ * y⁻¹ = u₂⁻¹) (hnotz : ¬ IsConj z u) :
    ∃ s ∈ S, s * y * s⁻¹ = y * u := by
  obtain ⟨hyS, hy2, hyPF, -⟩ := hy
  have hy' : Is47b S P F y := h.toCfg1.is47b_of hyS hy2 hyPF
  have hz1 := h.z_ne
  have hz2 := h.z_sq
  have huS : u ∈ S := by rw [hu]; exact mul_mem (h.P_le hu₁P) (h.Q_le hu₂Q)
  have huR : u ∈ P ⊔ Q := by rw [hu]; exact mul_mem (mem_sup_left hu₁P) (mem_sup_right hu₂Q)
  have hu2 : u * u = 1 := by
    have hc : u₂ * u₁ = u₁ * u₂ := (h.PQ_comm u₁ hu₁P u₂ hu₂Q).symm
    rw [hu]
    calc u₁ * u₂ * (u₁ * u₂) = u₁ * (u₂ * u₁) * u₂ := by group
      _ = u₁ * (u₁ * u₂) * u₂ := by rw [hc]
      _ = (u₁ * u₁) * (u₂ * u₂) := by group
      _ = 1 := by rw [hu₁sq, hu₂sq]; exact hz2
  have hyu2 : (y * u) * (y * u) = 1 := by
    calc (y * u) * (y * u) = y * (u * y) * u := by group
      _ = y * (y * u) * u := by rw [hyu]
      _ = (y * y) * (u * u) := by group
      _ = 1 := by rw [hy2, hu2]; group
  have hyuS : y * u ∈ S := mul_mem hyS huS
  have hyuPF : y * u ∉ P ⊔ F := by
    intro hmem
    apply hyPF
    have : (y * u) * u⁻¹ ∈ P ⊔ F := mul_mem hmem (inv_mem (h.toCfg1.R_le_PF huR))
    simpa using this
  have hyu' : Is47b S P F (y * u) := h.toCfg1.is47b_of hyuS hyu2 hyuPF
  have hu₂1 : u₂ ≠ 1 := by
    intro e; rw [e, one_mul] at hu₂sq; exact hz1 hu₂sq.symm
  have hu₂z : u₂ ≠ z := by
    intro e; rw [e, hz2] at hu₂sq; exact hz1 hu₂sq.symm
  have h4 := h.toCfg1.four_le_card_Q hF hu₂Q hu₂1 hu₂z
  have hy₂2 : (u₂ * y) * (u₂ * y) = 1 := by
    calc (u₂ * y) * (u₂ * y) = u₂ * (y * u₂ * y⁻¹) * (y * y) := by group
      _ = u₂ * u₂⁻¹ * 1 := by rw [hinv₂, hy2]
      _ = 1 := by group
  have hy₂S : u₂ * y ∈ S := mul_mem (h.Q_le hu₂Q) hyS
  have hy₂PF : u₂ * y ∉ P ⊔ F := by
    intro hmem
    apply hyPF
    have : u₂⁻¹ * (u₂ * y) ∈ P ⊔ F :=
      mul_mem (inv_mem (mem_sup_right (h.Q_le_F hu₂Q))) hmem
    simpa using this
  have hy₂ : Is47b S P F (u₂ * y) := h.toCfg1.is47b_of hy₂S hy₂2 hy₂PF
  have hconj_u₂ : ∃ p ∈ P, p⁻¹ * (u₂ * y) * p = y * u := by
    refine h.conj_in_Py hy₂ hyu2 ?_
    have hyu0 : y * u * y⁻¹ = u := by rw [hyu]; group
    have e : (y * u) * (u₂ * y)⁻¹ = u₁ := by
      calc (y * u) * (u₂ * y)⁻¹ = (y * u * y⁻¹) * u₂⁻¹ := by group
        _ = u * u₂⁻¹ := by rw [hyu0]
        _ = u₁ := by rw [hu]; group
    rw [e]; exact hu₁P
  obtain ⟨k0, hk0⟩ := (IsPGroup.iff_card).1 (h.S_pgroup.to_le h.Q_le)
  have hcases : Nat.card ↥Q = 4 ∨ 8 ≤ Nat.card ↥Q := by
    by_cases h8 : 8 ≤ Nat.card ↥Q
    · exact Or.inr h8
    · left
      have hk3 : k0 < 3 := by
        by_contra hge
        push Not at hge
        have h8' : (8 : ℕ) ≤ 2 ^ k0 := by
          calc (8 : ℕ) = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ k0 := Nat.pow_le_pow_right (by norm_num) hge
        omega
      have hk2 : 2 ≤ k0 := by
        by_contra hlt
        push Not at hlt
        have h4' : 2 ^ k0 ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have : k0 = 2 := by omega
      rw [hk0, this]; norm_num
  rcases hcases with hQ4 | hQ8
  · obtain ⟨s, hsS, hs⟩ := h.exists_not_norm hF hTr hy' hzy huS hu2 hu1 hnotz
    obtain ⟨v, hv, q, hq, hvq⟩ :=
      mem_sup_of_commute (fun a ha b hb => h.PQ_comm a ha b hb) (hSR s hsS y hyS)
    have hy'' : s * y * s⁻¹ = v * q * y := by
      calc s * y * s⁻¹ = (s * y * s⁻¹ * y⁻¹) * y := by group
        _ = v * q * y := by rw [hvq]
    have hyuinv : y * u⁻¹ * y⁻¹ = u⁻¹ := by
      calc y * u⁻¹ * y⁻¹ = (y * u * y⁻¹)⁻¹ := by group
        _ = u⁻¹ := by rw [show y * u * y⁻¹ = u by rw [hyu]; group]
    have hzu₂ : u₂ * z * u₂⁻¹ = z := by
      calc u₂ * z * u₂⁻¹ = z * u₂ * u₂⁻¹ := by rw [← h.z_cent u₂ (h.Q_le hu₂Q)]
        _ = z := by group
    have hwP : (s * y * s⁻¹) * (y * u)⁻¹ ∈ P := by
      have e0 : (s * y * s⁻¹) * (y * u)⁻¹ = v * q * u⁻¹ := by
        calc (s * y * s⁻¹) * (y * u)⁻¹ = (v * q * y) * (y * u)⁻¹ := by rw [hy'']
          _ = v * q * (y * u⁻¹ * y⁻¹) := by group
          _ = v * q * u⁻¹ := by rw [hyuinv]
      rw [e0]
      rcases h.toCfg1.mem_Q_four hF hQ4 hu₂Q hu₂sq hq with e | e | e | e
      · exfalso
        apply hs
        rw [hy'', e, mul_one]
        exact mul_mem (mem_sup_left hv) (mem_sup_right (mem_zpowers y))
      · exfalso
        apply hs
        rw [hy'', e]
        exact mul_mem (mul_mem (mem_sup_left hv) (mem_sup_left h.z_P))
          (mem_sup_right (mem_zpowers y))
      · rw [e, hu]
        have e1 : v * u₂ * (u₁ * u₂)⁻¹ = v * u₁⁻¹ := by group
        rw [e1]; exact mul_mem hv (inv_mem hu₁P)
      · rw [e, hu]
        have e1 : v * (u₂ * z) * (u₁ * u₂)⁻¹ = v * (u₂ * z * u₂⁻¹) * u₁⁻¹ := by group
        rw [e1, hzu₂]
        exact mul_mem (mul_mem hv h.z_P) (inv_mem hu₁P)
    have hw2 : (s * y * s⁻¹) * (s * y * s⁻¹) = 1 := by
      calc (s * y * s⁻¹) * (s * y * s⁻¹) = s * (y * y) * s⁻¹ := by group
        _ = 1 := by rw [hy2]; group
    obtain ⟨p, hp, hpy⟩ := h.conj_in_Py hyu' hw2 hwP
    refine ⟨p * s, mul_mem (h.P_le hp) hsS, ?_⟩
    calc p * s * y * (p * s)⁻¹ = p * (s * y * s⁻¹) * p⁻¹ := by group
      _ = p * (p⁻¹ * (y * u) * p) * p⁻¹ := by rw [hpy]
      _ = y * u := by group
  · obtain ⟨x, hxQ, hx⟩ := h.toCfg1.exists_x_Q hF hQ8 hyS hu₂Q hu₂sq hinv₂
    obtain ⟨p, hp, hpy⟩ := hconj_u₂
    refine ⟨p⁻¹ * x, mul_mem (h.P_le (inv_mem hp)) (h.Q_le hxQ), ?_⟩
    calc p⁻¹ * x * y * (p⁻¹ * x)⁻¹ = p⁻¹ * (x * y * x⁻¹) * p := by group
      _ = p⁻¹ * (u₂ * y) * p := by rw [hx]
      _ = y * u := hpy

end Cfg1K

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1
