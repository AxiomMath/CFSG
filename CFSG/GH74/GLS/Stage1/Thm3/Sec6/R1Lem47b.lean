module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Lem47
public import CFSG.GH74.GLS.Bg.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec4.M CFSG.GH74.GLS CFSG.GH74

variable {G : Type} [Group G] [Finite G] {z : G} {S P Q F : Subgroup G} {FA : G → Prop}

omit [Finite G] in
theorem comm_of_cyclic (hF : IsCyclic ↥F) {a b : G} (ha : a ∈ F) (hb : b ∈ F) : a * b = b * a := by
  have := (hF.isMulCommutative).is_comm.comm (⟨a, ha⟩ : ↥F) ⟨b, hb⟩
  exact congrArg Subtype.val this

namespace Cfg1

theorem Q_comm_R (h : Cfg1 G z S P Q F FA) (hF : IsCyclic ↥F) {q : G} (hq : q ∈ Q) {v : G}
    (hv : v ∈ P ⊔ Q) : v * q = q * v := by
  have hle : P ⊔ Q ≤ centralizer ({q} : Set G) := by
    refine sup_le ?_ ?_
    · intro p hp
      exact Subgroup.mem_centralizer_singleton_iff.2 (h.PQ_comm p hp q hq)
    · intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.2 (comm_of_cyclic hF (h.Q_le_F hb) (h.Q_le_F hq))
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hv)

theorem Q_conj_inv (h : Cfg1 G z S P Q F FA) {s : G} (hs : s ∈ S) {q : G} (hq : q ∈ Q) :
    s⁻¹ * q * s ∈ Q := by
  have := h.Q_norm s⁻¹ (S.inv_mem hs) q hq
  simpa using this

theorem S_le_normalizer_Q (h : Cfg1 G z S P Q F FA) : S ≤ normalizer (Q : Set G) := fun s hs =>
  mem_normalizer_of_both (fun x hx => h.Q_norm s hs x hx) (fun _ hx => h.Q_conj_inv hs hx)

theorem inv_eq_mul_z (h : Cfg1 G z S P Q F FA) {w : G} (hw : w * w = z) : w⁻¹ = w * z := by
  have : w * (w * z) = 1 := by rw [← mul_assoc, hw]; exact h.z_sq
  exact (mul_eq_one_iff_inv_eq.1 this)

theorem card_Qy (h : Cfg1 G z S P Q F FA) {y : G} (hyS : y ∈ S) (hy2 : y * y = 1) (hyQ : y ∉ Q)
    (hy1 : y ≠ 1) : Nat.card ↥(Q ⊔ zpowers y) = 2 * Nat.card ↥Q := by
  have hnorm : zpowers y ≤ normalizer (Q : Set G) := zpowers_le.2 (h.S_le_normalizer_Q hyS)
  have hc := card_sup_mul_card_inf (A := Q) (B := zpowers y) hnorm
  have hinf : Q ⊓ zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rcases (mem_zpowers_of_sq hy2).1 ha.2 with h1 | h1
    · rw [h1]; exact Subgroup.one_mem _
    · exact absurd (h1 ▸ ha.1) hyQ
  have hord : Nat.card ↥(zpowers y) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_two_of_sq_one hy2 hy1
  rw [hinf, Subgroup.card_bot, hord] at hc
  omega

theorem mem_Qy (h : Cfg1 G z S P Q F FA) {y : G} (hyS : y ∈ S) (hy2 : y * y = 1) {x : G}
    (hx : x ∈ Q ⊔ zpowers y) : x ∈ Q ∨ ∃ b ∈ Q, x = y * b := by
  have hnorm : zpowers y ≤ normalizer (Q : Set G) := zpowers_le.2 (h.S_le_normalizer_Q hyS)
  rw [sup_comm] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_le_normalizer hnorm hx
  rcases (mem_zpowers_of_sq hy2).1 ha with h1 | h1
  · left; rw [h1, one_mul]; exact hb
  · right; exact ⟨b, hb, by rw [h1]⟩

end Cfg1

namespace Cfg1

theorem maxClass_Qy (h : Cfg1 G z S P Q F FA) (hF : IsCyclic ↥F)
    (h1024 : Bg.B_maximalClass_of_small_centralizer) {y w : G} (hy : Is47b S P F y) (hwQ : w ∈ Q)
    (hw2 : w * w = z) (hyw : y * w * y⁻¹ = w⁻¹) :
    IsNonabelianMaximalClassTwoGroup ↥(Q ⊔ zpowers y) := by
  obtain ⟨hyS, hy2, hyPF, -⟩ := hy
  have hz1 := h.z_ne
  have hy1 : y ≠ 1 := fun e => hyPF (e ▸ one_mem _)
  have hw1 : w ≠ 1 := by
    intro e; rw [e, one_mul] at hw2; exact hz1 hw2.symm
  have hwz : w ≠ z := by
    intro e; rw [e, h.z_sq] at hw2; exact hz1 hw2.symm
  have h4 := h.four_le_card_Q hF hwQ hw1 hwz
  have hyQ : y ∉ Q := fun hmem => hyPF (mem_sup_right (h.Q_le_F hmem))
  have hcard := h.card_Qy hyS hy2 hyQ hy1
  have hF2 : IsPGroup 2 ↥F := h.S_pgroup.to_le h.F_le
  have hX2 : IsPGroup 2 ↥(Q ⊔ zpowers y) := h.S_pgroup.to_le (sup_le h.Q_le (zpowers_le.2 hyS))
  have hwy : ¬ (y * w = w * y) := by
    intro hc
    have e1 : y * w * y⁻¹ = w := by rw [hc]; group
    rw [e1] at hyw
    have e2 : w * w = 1 := by
      calc w * w = w * w⁻¹ := by rw [← hyw]
        _ = 1 := mul_inv_cancel w
    rw [hw2] at e2
    exact hz1 e2
  have hyX : y ∈ Q ⊔ zpowers y := mem_sup_right (mem_zpowers y)
  have hnab : ¬ IsMulCommutative ↥(Q ⊔ zpowers y) := by
    intro hc
    apply hwy
    have hwX : w ∈ Q ⊔ zpowers y := mem_sup_left hwQ
    exact congrArg Subtype.val (hc.is_comm.comm (⟨y, hyX⟩ : ↥(Q ⊔ zpowers y)) ⟨w, hwX⟩)
  have hcQ : ∀ b ∈ Q, y * b = b * y → b = 1 ∨ b = z := by
    intro b hb hcom
    have hbF : b ∈ F := h.Q_le_F hb
    by_cases hb2 : b * b = 1
    · exact h.invol_F hF hbF hb2
    · exfalso
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hF2) ⟨b, hbF⟩
      have hk' : orderOf b = 2 ^ k := by simpa using hk
      have hk0 : k ≠ 0 := by
        rintro rfl
        apply hb2
        have : b = 1 := orderOf_eq_one_iff.1 (by simpa using hk')
        rw [this, one_mul]
      have hk1 : k ≠ 1 := by
        rintro rfl
        exact hb2 (sq_one_of_orderOf_two (by simpa using hk'))
      have hb4 : 4 ≤ orderOf b := by
        rw [hk']
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hw4 : w ^ 4 = 1 := by
        have e : w ^ 4 = (w * w) * (w * w) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        rw [e, hw2]; exact h.z_sq
      have hwle : orderOf w ≤ Nat.card ↥(zpowers b) := by
        rw [Nat.card_zpowers]
        exact (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hw4)).trans hb4
      have hwb : w ∈ zpowers b :=
        B.mem_of_orderOf_le hF (zpowers_le.2 hbF) hF2 (h.Q_le_F hwQ) hwle
      have hbc : zpowers b ≤ centralizer ({y} : Set G) :=
        zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hcom.symm)
      have hwc : w * y = y * w := Subgroup.mem_centralizer_singleton_iff.1 (hbc hwb)
      exact hwy hwc.symm
  have hcent : Nat.card ↥(centralizer ({(⟨y, hyX⟩ : ↥(Q ⊔ zpowers y))} : Set ↥(Q ⊔ zpowers y))) ≤
      2 ^ 2 := by
    classical
    set C : Subgroup ↥(Q ⊔ zpowers y) :=
      centralizer ({(⟨y, hyX⟩ : ↥(Q ⊔ zpowers y))} : Set ↥(Q ⊔ zpowers y)) with hC
    have hmap : Nat.card ↥(C.map (Q ⊔ zpowers y).subtype) = Nat.card ↥C :=
      Subgroup.card_map_of_injective Subtype.val_injective
    have hmem : ∀ e ∈ C.map (Q ⊔ zpowers y).subtype, e ∈ ({1, z, y, y * z} : Finset G) := by
      rintro e ⟨c, hc, rfl⟩
      have hcomm : (c : G) * y = y * (c : G) :=
        congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hc)
      simp only [Subgroup.coe_subtype, Finset.mem_insert, Finset.mem_singleton]
      rcases h.mem_Qy hyS hy2 c.2 with hcQ' | ⟨b, hb, hcb⟩
      · rcases hcQ _ hcQ' hcomm.symm with e1 | e1
        · exact Or.inl e1
        · exact Or.inr (Or.inl e1)
      · have hbc : y * b = b * y := by
          rw [hcb] at hcomm
          have : y * b * y = y * (y * b) := hcomm
          calc y * b = y⁻¹ * (y * (y * b)) := by group
            _ = y⁻¹ * (y * b * y) := by rw [this]
            _ = b * y := by group
        rcases hcQ _ hb hbc with e1 | e1
        · right; right; left; rw [hcb, e1, mul_one]
        · right; right; right; rw [hcb, e1]
    have h1 := B.card_subgroup_le_finset (C.map (Q ⊔ zpowers y).subtype) _ hmem
    have h2 : ({1, z, y, y * z} : Finset G).card ≤ 4 := Finset.card_le_four
    omega
  have hcard3 : 2 ^ 3 ≤ Nat.card ↥(Q ⊔ zpowers y) := by rw [hcard]; omega
  obtain ⟨m, hm, hl⟩ := h1024 2 Nat.prime_two ↥(Q ⊔ zpowers y) hX2 hcard3 ⟨y, hyX⟩ hcent
  exact B.maxClass_of_lcs ↥(Q ⊔ zpowers y) hX2 hnab m hm hl

end Cfg1

namespace Cfg1

theorem decomp_four (h : Cfg1 G z S P Q F FA) (hF : IsCyclic ↥F) {u : G} (huR : u ∈ P ⊔ Q)
    (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ z) :
    ∃ u₁ ∈ P, ∃ u₂ ∈ Q, u = u₁ * u₂ ∧ u₁ * u₁ = z ∧ u₂ * u₂ = z := by
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup_of_commute (fun a ha b hb => h.PQ_comm a ha b hb) huR
  have hcomm : q * p = p * q := (h.PQ_comm p hp q hq).symm
  have hpq : (p * p) * (q * q) = 1 := by
    calc (p * p) * (q * q) = p * (p * q) * q := by group
      _ = p * (q * p) * q := by rw [← hcomm]
      _ = (p * q) * (p * q) := by group
      _ = 1 := hu2
  have hqq : q * q = (p * p)⁻¹ := eq_inv_of_mul_eq_one_right hpq
  have hppP : p * p ∈ P := mul_mem hp hp
  have hppQ : p * p ∈ Q := by
    have : (q * q)⁻¹ ∈ Q := inv_mem (mul_mem hq hq)
    have e : p * p = (q * q)⁻¹ := by rw [hqq, inv_inv]
    rw [e]; exact this
  rcases h.PQ_inf _ hppP hppQ with e | e
  · exfalso
    have hq2 : q * q = 1 := by rw [hqq, e]; group
    rcases h.P_inv p hp e with h1 | h1 <;> rcases h.invol_F hF (h.Q_le_F hq) hq2 with h2 | h2
    · exact hu1 (by rw [h1, h2]; group)
    · exact huz (by rw [h1, h2]; group)
    · exact huz (by rw [h1, h2]; group)
    · exact hu1 (by rw [h1, h2]; exact h.z_sq)
  · refine ⟨p, hp, q, hq, rfl, e, ?_⟩
    rw [hqq, e]
    exact inv_eq_of_mul_eq_one_right h.z_sq

end Cfg1

namespace Cfg1K

theorem inverts_u₂ (h : Cfg1K G z S P Q F FA) {y u₁ u₂ : G} (hy : Is47b S P F y) (hu₁ : u₁ ∈ P)
    (hu₂ : u₂ ∈ Q) (h1 : u₁ * u₁ = z) (h2 : u₂ * u₂ = z)
    (hc : y * (u₁ * u₂) = (u₁ * u₂) * y) : y * u₂ * y⁻¹ = u₂⁻¹ := by
  obtain ⟨hyS, hy2, hyPF, -⟩ := hy
  have hyP : y ∉ P := fun hm => hyPF (mem_sup_left hm)
  have hSD := h.sd y hyS hy2 (h.toCfg1.not_R_of_not_PF hyPF)
    (h.toCfg1.not_FA_of_not_PF hyS hy2 hyPF)
  have hnormP : ∀ p ∈ P, y * p * y⁻¹ ∈ P := fun p hp => h.P_norm y hyS p hp
  obtain ⟨hs1, -, -⟩ := h.sdf y hy2 hyP hnormP hSD
  have ha : y * u₁ * y⁻¹ ∈ P := h.P_norm y hyS u₁ hu₁
  have hb : y * u₂ * y⁻¹ ∈ Q := h.Q_norm y hyS u₂ hu₂
  have hab : (y * u₁ * y⁻¹) * (y * u₂ * y⁻¹) = u₁ * u₂ := by
    calc (y * u₁ * y⁻¹) * (y * u₂ * y⁻¹) = y * (u₁ * u₂) * y⁻¹ := by group
      _ = u₁ * u₂ := by rw [hc]; group
  have hkey : u₁⁻¹ * (y * u₁ * y⁻¹) = u₂ * (y * u₂ * y⁻¹)⁻¹ := by
    calc u₁⁻¹ * (y * u₁ * y⁻¹) = u₁⁻¹ * ((y * u₁ * y⁻¹) * (y * u₂ * y⁻¹)) * (y * u₂ * y⁻¹)⁻¹ := by
          group
      _ = u₁⁻¹ * (u₁ * u₂) * (y * u₂ * y⁻¹)⁻¹ := by rw [hab]
      _ = u₂ * (y * u₂ * y⁻¹)⁻¹ := by group
  have hP : u₁⁻¹ * (y * u₁ * y⁻¹) ∈ P := mul_mem (inv_mem hu₁) ha
  have hQ : u₁⁻¹ * (y * u₁ * y⁻¹) ∈ Q := by rw [hkey]; exact mul_mem hu₂ (inv_mem hb)
  have hz1 := h.z_ne
  rcases h.PQ_inf _ hP hQ with e | e
  · exfalso
    have e' : u₁ = y * u₁ * y⁻¹ := inv_mul_eq_one.1 e
    have hcom : y * u₁ = u₁ * y := by
      calc y * u₁ = y * u₁ * y⁻¹ * y := by group
        _ = u₁ * y := by rw [← e']
    rcases hs1 u₁ hu₁ hcom with e1 | e1
    · rw [e1, one_mul] at h1; exact hz1 h1.symm
    · rw [e1, h.z_sq] at h1; exact hz1 h1.symm
  · have hq : u₂ * (y * u₂ * y⁻¹)⁻¹ = z := by rw [← hkey]; exact e
    have hb' : (y * u₂ * y⁻¹)⁻¹ = u₂⁻¹ * z := by
      calc (y * u₂ * y⁻¹)⁻¹ = u₂⁻¹ * (u₂ * (y * u₂ * y⁻¹)⁻¹) := by group
        _ = u₂⁻¹ * z := by rw [hq]
    have hb2 : y * u₂ * y⁻¹ = z * u₂ := by
      calc y * u₂ * y⁻¹ = ((y * u₂ * y⁻¹)⁻¹)⁻¹ := by group
        _ = (u₂⁻¹ * z)⁻¹ := by rw [hb']
        _ = z⁻¹ * u₂ := by group
        _ = z * u₂ := by rw [inv_eq_of_mul_eq_one_right h.z_sq]
    rw [hb2, h.z_cent u₂ (h.Q_le hu₂), h.inv_eq_mul_z h2]

theorem lemma_C (h : Cfg1K G z S P Q F FA) {y y₁ : G} (hy : Is47b S P F y) (hy₁ : Is47b S P F y₁) :
    ∃ p ∈ P, ∃ q ∈ Q, y₁ = p⁻¹ * (q * y) * p ∧ (q * y) * (q * y) = 1 := by
  obtain ⟨hyS, hy2, hyPF, -⟩ := hy
  obtain ⟨hy₁S, hy₁2, hy₁PF, -⟩ := hy₁
  have hdiag := h.diag' hy₁S hyS hy₁2 hy2 hy₁PF hyPF
  obtain ⟨v, hv, q, hq, hvq⟩ := mem_sup_of_commute (fun a ha b hb => h.PQ_comm a ha b hb) hdiag
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hyP : y ∉ P := fun hm => hyPF (mem_sup_left hm)
  have hSD := h.sd y hyS hy2 (h.toCfg1.not_R_of_not_PF hyPF)
    (h.toCfg1.not_FA_of_not_PF hyS hy2 hyPF)
  have hnormP : ∀ p ∈ P, y * p * y⁻¹ ∈ P := fun p hp => h.P_norm y hyS p hp
  obtain ⟨-, hs2, hs3⟩ := h.sdf y hy2 hyP hnormP hSD
  have hy₁eq : y₁ = v * q * y := by
    calc y₁ = y₁ * y⁻¹ * y := by group
      _ = v * q * y := by rw [hvq]
  have hv' : y * v * y ∈ P := by
    have := h.P_norm y hyS v hv; rwa [hyinv] at this
  have hq' : y * q * y ∈ Q := by
    have := h.Q_norm y hyS q hq; rwa [hyinv] at this
  have hsq : (v * (y * v * y)) * (q * (y * q * y)) = 1 := by
    have e1 : y₁ * y₁ = (v * (y * v * y)) * (q * (y * q * y)) := by
      have hc : (y * v * y) * q = q * (y * v * y) := h.PQ_comm _ hv' q hq
      calc y₁ * y₁ = v * q * y * (v * q * y) := by rw [hy₁eq]
        _ = v * q * ((y * v * y) * (y * q * y)) := by
          rw [show (y * v * y) * (y * q * y) = y * v * (y * y) * q * y by group, hy2]; group
        _ = v * ((q * (y * v * y)) * (y * q * y)) := by group
        _ = v * (((y * v * y) * q) * (y * q * y)) := by rw [hc]
        _ = (v * (y * v * y)) * (q * (y * q * y)) := by group
    rw [← e1]; exact hy₁2
  have hvvP : v * (y * v * y) ∈ P := mul_mem hv hv'
  have hqqQ : q * (y * q * y) ∈ Q := mul_mem hq hq'
  have hvvQ : v * (y * v * y) ∈ Q := by
    have e : v * (y * v * y) = (q * (y * q * y))⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [e]; exact inv_mem hqqQ
  have hvy : (v * y) * (v * y) = v * (y * v * y) := by group
  have hv1 : (v * y) * (v * y) = 1 := by
    rcases h.PQ_inf _ hvvP hvvQ with e | e
    · rw [hvy]; exact e
    · exact absurd (hvy.trans e) (hs3 v hv)
  have hvv1 : v * (y * v * y) = 1 := hvy ▸ hv1
  have hqq1 : q * (y * q * y) = 1 := by rw [hvv1, one_mul] at hsq; exact hsq
  obtain ⟨p, hp, hpy⟩ := hs2 v hv hv1
  refine ⟨p, hp, q, hq, ?_, ?_⟩
  · have hcomm : p⁻¹ * q = q * p⁻¹ := h.PQ_comm _ (inv_mem hp) q hq
    calc y₁ = v * q * y := hy₁eq
      _ = q * (v * y) := by rw [h.PQ_comm v hv q hq]; group
      _ = q * (p⁻¹ * y * p) := by rw [hpy]
      _ = (q * p⁻¹) * y * p := by group
      _ = (p⁻¹ * q) * y * p := by rw [hcomm]
      _ = p⁻¹ * (q * y) * p := by group
  · calc (q * y) * (q * y) = q * (y * q * y) := by group
      _ = 1 := hqq1

end Cfg1K

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1
