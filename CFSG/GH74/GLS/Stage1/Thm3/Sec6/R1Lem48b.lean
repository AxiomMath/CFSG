module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Lem48

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec4.M CFSG.GH74.GLS CFSG.GH74

variable {G : Type} [Group G] [Finite G] {z : G} {S P Q F : Subgroup G} {FA : G → Prop}

namespace Cfg1K

theorem lemma48 (h : Cfg1K G z S P Q F FA) (hF : IsCyclic ↥F)
    (h119 : ∀ s ∈ P ⊔ F, s ∉ P ⊔ Q → ∀ V : Subgroup G, V ≤ P → IsCyclic ↥V →
      V.relIndex P = 2 → ∃ v ∈ V, s * v ≠ v * s)
    (hT : HThompson G z S) {y : G} (hy : Is47b S P F y) {U : Subgroup G} (hUR : U ≤ P ⊔ Q)
    (hU4 : Four U) (hUn : ∀ s ∈ S, ∀ v ∈ U, s * v * s⁻¹ ∈ U) (hUy : ∀ v ∈ U, y * v = v * y)
    {u : G} (huU : u ∈ U) (hu1 : u ≠ 1) (huz : u ≠ z) : ¬ IsConj z u := by
  intro hconj
  have hy' := hy
  obtain ⟨hyS, hy2, hyPF, -⟩ := hy'
  have hz2 := h.z_sq
  have hz1 := h.z_ne
  have hUS : U ≤ S := hUR.trans (sup_le h.P_le h.Q_le)
  have hzU : z ∈ U := h.toCfg1.z_mem_four hU4 hUS hUn
  obtain ⟨u₁, hu₁P, u₂, hu₂Q, hu, hu₁sq, hu₂sq⟩ :=
    h.decomp_four hF (hUR huU) (hU4.1 u huU) hu1 huz
  have hmemU : ∀ {v : G}, v ∈ U → v = 1 ∨ v = z ∨ v = u ∨ v = u * z := fun hv =>
    h.toCfg1.mem_four hU4 hzU huU hu1 huz hv
  have hzS : ∀ {s : G}, s ∈ S → z * s = s * z := fun {s} hs => h.z_cent s hs
  have hεQ : ∀ ε : G, (ε = 1 ∨ ε = z) → ε ∈ Q := by
    rintro ε (rfl | rfl)
    · exact Q.one_mem
    · exact h.z_Q
  have hnorm_u₁ : ∀ s ∈ S, s * u₁ * s⁻¹ = u₁ ∨ s * u₁ * s⁻¹ = u₁ * z := by
    intro s hs
    have hsu : s * u * s⁻¹ ∈ U := hUn s hs u huU
    have hsu1 : s * u * s⁻¹ ≠ 1 := by
      intro e
      apply hu1
      calc u = s⁻¹ * (s * u * s⁻¹) * s := by group
        _ = 1 := by rw [e]; group
    have hsuz : s * u * s⁻¹ ≠ z := by
      intro e
      apply huz
      calc u = s⁻¹ * (s * u * s⁻¹) * s := by group
        _ = s⁻¹ * z * s := by rw [e]
        _ = s⁻¹ * (z * s) := by group
        _ = s⁻¹ * (s * z) := by rw [hzS hs]
        _ = z := by group
    obtain ⟨ε, hε, hsu'⟩ : ∃ ε : G, (ε = 1 ∨ ε = z) ∧ s * u * s⁻¹ = u * ε := by
      rcases hmemU hsu with e | e | e | e
      · exact absurd e hsu1
      · exact absurd e hsuz
      · exact ⟨1, Or.inl rfl, by rw [e, mul_one]⟩
      · exact ⟨z, Or.inr rfl, e⟩
    have ha : s * u₁ * s⁻¹ ∈ P := h.P_norm s hs u₁ hu₁P
    have hb : s * u₂ * s⁻¹ ∈ Q := h.Q_norm s hs u₂ hu₂Q
    have hab : (s * u₁ * s⁻¹) * (s * u₂ * s⁻¹) = u₁ * u₂ * ε := by
      calc (s * u₁ * s⁻¹) * (s * u₂ * s⁻¹) = s * (u₁ * u₂) * s⁻¹ := by group
        _ = s * u * s⁻¹ := by rw [hu]
        _ = u₁ * u₂ * ε := by rw [hsu', hu]
    have hkey : u₁⁻¹ * (s * u₁ * s⁻¹) = u₂ * ε * (s * u₂ * s⁻¹)⁻¹ := by
      calc u₁⁻¹ * (s * u₁ * s⁻¹)
          = u₁⁻¹ * ((s * u₁ * s⁻¹) * (s * u₂ * s⁻¹)) * (s * u₂ * s⁻¹)⁻¹ := by group
        _ = u₁⁻¹ * (u₁ * u₂ * ε) * (s * u₂ * s⁻¹)⁻¹ := by rw [hab]
        _ = u₂ * ε * (s * u₂ * s⁻¹)⁻¹ := by group
    have hP : u₁⁻¹ * (s * u₁ * s⁻¹) ∈ P := mul_mem (inv_mem hu₁P) ha
    have hQ : u₁⁻¹ * (s * u₁ * s⁻¹) ∈ Q := by
      rw [hkey]; exact mul_mem (mul_mem hu₂Q (hεQ ε hε)) (inv_mem hb)
    rcases h.PQ_inf _ hP hQ with e | e
    · left
      have := inv_mul_eq_one.1 e
      exact this.symm
    · right
      calc s * u₁ * s⁻¹ = u₁ * (u₁⁻¹ * (s * u₁ * s⁻¹)) := by group
        _ = u₁ * z := by rw [e]
  obtain ⟨V, hVdef, hVcyc, hVidx⟩ := h.P_centr u₁ hu₁P hu₁sq hnorm_u₁
  have hmemV : ∀ {v : G}, v ∈ V ↔ v ∈ P ∧ v * u₁ = u₁ * v := by
    intro v
    rw [hVdef, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have hVP : V ≤ P := fun v hv => (hmemV.1 hv).1
  have hVS : V ≤ S := hVP.trans h.P_le
  have hu₁V : u₁ ∈ V := hmemV.2 ⟨hu₁P, rfl⟩
  have hzV : z ∈ V := hmemV.2 ⟨h.z_P, by rw [hzS (h.P_le hu₁P)]⟩
  have hV2 : IsPGroup 2 ↥V := h.S_pgroup.to_le hVS
  have hVU : ∀ v ∈ V, ∀ w ∈ U, v * w = w * v := by
    intro v hv w hw
    obtain ⟨hvP, hvu₁⟩ := hmemV.1 hv
    have hvz : v * z = z * v := (hzS (h.P_le hvP)).symm
    have hvu₂ : v * u₂ = u₂ * v := h.PQ_comm v hvP u₂ hu₂Q
    have hvu : v * u = u * v := by
      rw [hu]
      calc v * (u₁ * u₂) = (v * u₁) * u₂ := by group
        _ = (u₁ * v) * u₂ := by rw [hvu₁]
        _ = u₁ * (v * u₂) := by group
        _ = u₁ * (u₂ * v) := by rw [hvu₂]
        _ = (u₁ * u₂) * v := by group
    rcases hmemU hw with e | e | e | e
    · rw [e]; group
    · rw [e]; exact hvz
    · rw [e]; exact hvu
    · rw [e]
      calc v * (u * z) = (v * u) * z := by group
        _ = (u * v) * z := by rw [hvu]
        _ = u * (v * z) := by group
        _ = u * (z * v) := by rw [hvz]
        _ = (u * z) * v := by group
  have hVnorm : ∀ s ∈ S, ∀ v ∈ V, s * v * s⁻¹ ∈ V := by
    intro s hs v hv
    obtain ⟨hvP, hvu₁⟩ := hmemV.1 hv
    refine hmemV.2 ⟨h.P_norm s hs v hvP, ?_⟩
    have ha' : s⁻¹ * u₁ * s = u₁ ∨ s⁻¹ * u₁ * s = u₁ * z := by
      have := hnorm_u₁ s⁻¹ (S.inv_mem hs)
      simpa using this
    have hvz : v * z = z * v := (hzS (h.P_le hvP)).symm
    have hva : v * (s⁻¹ * u₁ * s) = (s⁻¹ * u₁ * s) * v := by
      rcases ha' with e | e
      · rw [e]; exact hvu₁
      · rw [e]
        calc v * (u₁ * z) = (v * u₁) * z := by group
          _ = (u₁ * v) * z := by rw [hvu₁]
          _ = u₁ * (v * z) := by group
          _ = u₁ * (z * v) := by rw [hvz]
          _ = (u₁ * z) * v := by group
    calc s * v * s⁻¹ * u₁ = s * (v * (s⁻¹ * u₁ * s)) * s⁻¹ := by group
      _ = s * ((s⁻¹ * u₁ * s) * v) * s⁻¹ := by rw [hva]
      _ = u₁ * (s * v * s⁻¹) := by group
  set W : Subgroup G := S ⊓ centralizer (U : Set G) with hWdef
  have hmemW : ∀ {w : G}, w ∈ W ↔ w ∈ S ∧ ∀ v ∈ U, v * w = w * v := by
    intro w
    constructor
    · intro hw
      exact ⟨hw.1, fun v hv => Subgroup.mem_centralizer_iff.1 hw.2 v hv⟩
    · rintro ⟨hwS, hwc⟩
      exact ⟨hwS, Subgroup.mem_centralizer_iff.2 (fun v hv => hwc v hv)⟩
  have hVW : V ≤ W := fun v hv => hmemW.2 ⟨hVS hv, fun w hw => (hVU v hv w hw).symm⟩
  obtain ⟨x, hxW, hxz⟩ := hT U hUS hU4 hUn u huU hu1 huz hconj
  have hxmem : ∀ w : G, w ∈ W ↔ x * w * x⁻¹ ∈ W := Subgroup.mem_normalizer_iff.1 hxW
  have hxinvW : ∀ w ∈ W, x⁻¹ * w * x ∈ W := by
    intro w hw
    refine (hxmem _).2 ?_
    have e : x * (x⁻¹ * w * x) * x⁻¹ = w := by group
    rw [e]; exact hw
  have hxz2 : (x * z * x⁻¹) * (x * z * x⁻¹) = 1 := by
    calc (x * z * x⁻¹) * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hxz1 : x * z * x⁻¹ ≠ 1 := by
    intro e
    apply hz1
    calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
      _ = 1 := by rw [e]; group
  obtain ⟨g, hgV, hgen⟩ := exists_gen_of_cyclic hVcyc
  set hh : G := x * g * x⁻¹ with hhdef
  have hgW : g ∈ W := hVW hgV
  have hhW : hh ∈ W := (hxmem g).1 hgW
  have hhS : hh ∈ S := (hmemW.1 hhW).1
  have hg'W : x⁻¹ * g * x ∈ W := hxinvW g hgW
  have hVgen : V = zpowers g := le_antisymm (fun v hv => hgen v hv) (zpowers_le.2 hgV)
  have hcV : g * hh * g⁻¹ * hh⁻¹ ∈ V := by
    have h1 : hh * g⁻¹ * hh⁻¹ ∈ V := hVnorm hh hhS g⁻¹ (inv_mem hgV)
    have e : g * hh * g⁻¹ * hh⁻¹ = g * (hh * g⁻¹ * hh⁻¹) := by group
    rw [e]; exact mul_mem hgV h1
  have hghg : g * hh * g⁻¹ ∈ zpowers hh := by
    have h1 : (x⁻¹ * g * x) * g * (x⁻¹ * g * x)⁻¹ ∈ V :=
      hVnorm _ (hmemW.1 hg'W).1 g hgV
    obtain ⟨k, hk⟩ := (mem_zpowers_iff).1 (hgen _ h1)
    refine (mem_zpowers_iff).2 ⟨k, ?_⟩
    have e : g * hh * g⁻¹ = x * ((x⁻¹ * g * x) * g * (x⁻¹ * g * x)⁻¹) * x⁻¹ := by
      simp only [hhdef]; group
    rw [e, ← hk]
    exact conj_zpow
  have hcH : g * hh * g⁻¹ * hh⁻¹ ∈ zpowers hh := mul_mem hghg (inv_mem (mem_zpowers hh))
  have hc1 : g * hh * g⁻¹ * hh⁻¹ = 1 := by
    by_contra hne
    have hzc : z ∈ zpowers (g * hh * g⁻¹ * hh⁻¹) :=
      invol_mem_zpowers hVcyc hV2 hcV hne hzV hz2 hz1
    have hzH : z ∈ zpowers hh := (zpowers_le.2 hcH) hzc
    obtain ⟨i, hi⟩ := (mem_zpowers_iff).1 (hgen z hzV)
    have hxzH : x * z * x⁻¹ ∈ zpowers hh := by
      refine (mem_zpowers_iff).2 ⟨i, ?_⟩
      rw [← hi]; exact conj_zpow
    have := B.cyclic_invol_unique (F := zpowers hh) inferInstance hzH hxzH hz2 hxz2 hz1 hxz1
    exact hxz this.symm
  have hgh : g * hh = hh * g := by
    calc g * hh = (g * hh * g⁻¹ * hh⁻¹) * (hh * g) := by group
      _ = hh * g := by rw [hc1, one_mul]
  have hcomm : ∀ v ∈ V, hh * v = v * hh := by
    intro v hv
    obtain ⟨k, hk⟩ := (mem_zpowers_iff).1 (hgen v hv)
    rw [← hk]
    exact (Commute.zpow_left (show Commute g hh from hgh) k).eq.symm
  have hNcard : Nat.card ↥P = 2 * Nat.card ↥V := by
    have := relIndex_mul_card V P
    rw [hVidx, inf_of_le_left hVP] at this
    exact this.symm
  have hNord : orderOf g = Nat.card ↥V := by
    have : Nat.card ↥V = orderOf g := by rw [hVgen]; exact Nat.card_zpowers g
    exact this.symm
  have hN2 : 2 ∣ Nat.card ↥V := by
    have h1 := Subgroup.card_dvd_of_le (zpowers_le.2 hzV)
    rwa [Nat.card_zpowers, orderOf_two_of_sq_one hz2 hz1] at h1
  obtain ⟨M, hM⟩ := hN2
  have hNpos : 0 < Nat.card ↥V := Nat.card_pos
  have hM0 : M ≠ 0 := by omega
  have hgN : g ^ Nat.card ↥V = 1 := by rw [← hNord]; exact pow_orderOf_eq_one g
  have hgM2 : g ^ M * g ^ M = 1 := by
    rw [← pow_add, show M + M = Nat.card ↥V by omega]; exact hgN
  have hgM1 : g ^ M ≠ 1 := pow_ne_one_of_lt_orderOf hM0 (by omega)
  have htz : g ^ M = z :=
    B.cyclic_invol_unique hVcyc (V.pow_mem hgV M) hzV hgM2 hz2 hgM1 hz1
  have hhR : hh ∉ P ⊔ Q := by
    intro hmem
    obtain ⟨p, hp, q, hq, hpq⟩ := mem_sup_of_commute (fun a ha b hb => h.PQ_comm a ha b hb) hmem
    have hcpq : Commute p q := h.PQ_comm p hp q hq
    have hhM : hh ^ M = x * z * x⁻¹ := by
      rw [hhdef, conj_pow, htz]
    have hhN : hh ^ Nat.card ↥V = 1 := by
      rw [hhdef, conj_pow, hgN]; group
    have hpN : p ^ Nat.card ↥V = 1 := by
      have := h.P_exp p hp
      rwa [hNcard, Nat.mul_div_cancel_left _ (by norm_num)] at this
    have hqN : q ^ Nat.card ↥V = 1 := by
      rw [hpq, hcpq.mul_pow, hpN, one_mul] at hhN
      exact hhN
    have hpM : p ^ M = 1 ∨ p ^ M = z := by
      refine h.P_inv _ (P.pow_mem hp M) ?_
      rw [← pow_add, show M + M = Nat.card ↥V by omega]; exact hpN
    have hqM : q ^ M = 1 ∨ q ^ M = z := by
      refine h.invol_F hF (F.pow_mem (h.Q_le_F hq) M) ?_
      rw [← pow_add, show M + M = Nat.card ↥V by omega]; exact hqN
    rw [hpq, hcpq.mul_pow] at hhM
    rcases hpM with e1 | e1 <;> rcases hqM with e2 | e2 <;> rw [e1, e2] at hhM
    · exact hxz1 (by rw [← hhM]; group)
    · exact hxz (by rw [← hhM]; group)
    · exact hxz (by rw [← hhM]; group)
    · exact hxz1 (by rw [← hhM]; exact hz2)
  have hinv₂ : y * u₂ * y⁻¹ = u₂⁻¹ :=
    h.inverts_u₂ hy hu₁P hu₂Q hu₁sq hu₂sq (by rw [← hu]; exact hUy u huU)
  have hhu : hh * u = u * hh := ((hmemW.1 hhW).2 u huU).symm
  have hhu₁ : hh * u₁ = u₁ * hh := hcomm u₁ hu₁V
  have hhu₂ : hh * u₂ = u₂ * hh := by
    have : u₁ * (hh * u₂) = u₁ * (u₂ * hh) := by
      calc u₁ * (hh * u₂) = (u₁ * hh) * u₂ := by group
        _ = (hh * u₁) * u₂ := by rw [hhu₁]
        _ = hh * (u₁ * u₂) := by group
        _ = hh * u := by rw [hu]
        _ = u * hh := hhu
        _ = (u₁ * u₂) * hh := by rw [hu]
        _ = u₁ * (u₂ * hh) := by group
    exact mul_left_cancel this
  have hhPF : hh ∈ P ⊔ F := h.mem_PF_of_centralizes hF hy hu₂Q hu₂sq hinv₂ hhS hhu₂
  obtain ⟨v, hvV, hne⟩ := h119 hh hhPF hhR V hVP hVcyc hVidx
  exact hne (hcomm v hvV)

end Cfg1K

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1
