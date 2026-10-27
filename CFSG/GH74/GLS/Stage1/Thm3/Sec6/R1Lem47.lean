module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Ctx

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec4.M

variable {G : Type} [Group G] [Finite G] {z : G} {S P Q F : Subgroup G} {FA : G → Prop}

omit [Finite G] in
theorem sq_one_of_orderOf_two {x : G} (h : orderOf x = 2) : x * x = 1 := by
  have := pow_orderOf_eq_one x
  rw [h] at this
  simpa [sq] using this

omit [Finite G] in
theorem orderOf_two_of_sq_one {x : G} (hx : x * x = 1) (hx1 : x ≠ 1) : orderOf x = 2 :=
  orderOf_eq_prime (by simpa [sq] using hx) hx1

namespace Cfg1

theorem z_mem_F (h : Cfg1 G z S P Q F FA) : z ∈ F := h.Q_le_F h.z_Q

theorem invol_F (h : Cfg1 G z S P Q F FA) (hF : IsCyclic ↥F) {f : G} (hf : f ∈ F) (hf2 : f * f = 1) :
    f = 1 ∨ f = z := by
  by_cases hf1 : f = 1
  · exact Or.inl hf1
  · exact Or.inr (B.cyclic_invol_unique hF hf h.z_mem_F hf2 h.z_sq hf1 h.z_ne)

theorem P_inf_F (h : Cfg1 G z S P Q F FA) {x : G} (hxP : x ∈ P) (hxF : x ∈ F) : x = 1 ∨ x = z := by
  have hxQ : x ∈ Q := by
    have : x ∈ F ⊓ (P ⊔ Q) := ⟨hxF, mem_sup_left hxP⟩
    rwa [← h.Q_eq] at this
  exact h.PQ_inf x hxP hxQ

theorem exists_outside (h : Cfg1 G z S P Q F FA) (hF : IsCyclic ↥F) :
    ∃ y ∈ S, y * y = 1 ∧ y ∉ P ⊔ F := by
  obtain ⟨E, hES, hEx, hE8⟩ := h.rank3
  by_contra hcon
  push Not at hcon
  have hEPF : E ≤ P ⊔ F := fun e he => hcon e (hES he) (hEx e he)
  have := h.card_PF_le hF hEPF hEx
  omega

theorem is47b_of (h : Cfg1 G z S P Q F FA) {y : G} (hyS : y ∈ S) (hy2 : y * y = 1)
    (hyPF : y ∉ P ⊔ F) : Is47b S P F y :=
  ⟨hyS, hy2, hyPF, B.eq_sup_zpowers_of_relIndex_le_two h.PF_le h.idx hyS hyPF⟩

theorem not_FA_of_not_PF (h : Cfg1 G z S P Q F FA) {y : G} (hyS : y ∈ S) (hy2 : y * y = 1)
    (hyPF : y ∉ P ⊔ F) : ¬ FA y := fun hfa => hyPF (h.inv_fa y hyS hy2 hfa)

theorem not_R_of_not_PF (h : Cfg1 G z S P Q F FA) {y : G} (hy : y ∉ P ⊔ F) : y ∉ P ⊔ Q :=
  fun hR => hy (h.R_le_PF hR)

theorem S_pgroup (h : Cfg1 G z S P Q F FA) : IsPGroup 2 ↥S := h.S_syl.2.1

theorem four_le_card_Q (h : Cfg1 G z S P Q F FA) (hF : IsCyclic ↥F) {q : G} (hq : q ∈ Q)
    (hq1 : q ≠ 1) (hqz : q ≠ z) : 4 ≤ Nat.card ↥Q := by
  have hQ2 : IsPGroup 2 ↥Q := h.S_pgroup.to_le h.Q_le
  have hqF : q ∈ F := h.Q_le_F hq
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ2) ⟨q, hq⟩
  have hk' : orderOf q = 2 ^ k := by simpa using hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hq1 (orderOf_eq_one_iff.1 (by simpa using hk'))
  have hk1 : k ≠ 1 := by
    rintro rfl
    have hsq : q * q = 1 := sq_one_of_orderOf_two (by simpa using hk')
    rcases h.invol_F hF hqF hsq with h1 | h1
    · exact hq1 h1
    · exact hqz h1
  have h4 : 4 ≤ orderOf q := by
    rw [hk']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := Subgroup.card_le_of_le (zpowers_le.2 hq)
  rw [Nat.card_zpowers] at this
  omega

theorem invol_PF_in_R (h : Cfg1 G z S P Q F FA) (hF : IsCyclic ↥F)
    (hq : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ z) {s : G} (hs : s ∈ P ⊔ F) (hs2 : s * s = 1) : s ∈ P ⊔ Q := by
  obtain ⟨p, hp, f, hf, rfl⟩ := h.mem_PF hs
  obtain ⟨q, hqQ, hq1, hqz⟩ := hq
  have h4 := h.four_le_card_Q hF hqQ hq1 hqz
  have hF2 : IsPGroup 2 ↥F := h.S_pgroup.to_le h.F_le
  have e0 : p⁻¹ = f * p * f := by
    have : p * (f * p * f) = 1 := by rw [← hs2]; group
    exact mul_eq_one_iff_inv_eq.1 this
  have hf2P : f * f ∈ P := by
    have e1 : f * f = (f * p * f⁻¹)⁻¹ * p⁻¹ := by
      calc f * f = (f * p * f⁻¹)⁻¹ * (f * p * f) := by group
        _ = (f * p * f⁻¹)⁻¹ * p⁻¹ := by rw [← e0]
    rw [e1]
    exact mul_mem (inv_mem (h.P_norm f (h.F_le hf) p hp)) (inv_mem hp)
  have hf2F : f * f ∈ F := mul_mem hf hf
  have hf4 : f ^ 4 = 1 := by
    have e2 : f ^ 4 = (f * f) * (f * f) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e2]
    rcases h.P_inf_F hf2P hf2F with h1 | h1
    · rw [h1]; group
    · rw [h1]; exact h.z_sq
  have hle : orderOf f ≤ Nat.card ↥Q :=
    (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hf4)).trans h4
  have hfQ : f ∈ Q := B.mem_of_orderOf_le hF h.Q_le_F hF2 hf hle
  exact mul_mem (mem_sup_left hp) (mem_sup_right hfQ)

theorem z_mem_four (h : Cfg1 G z S P Q F FA) {U : Subgroup G} (hU : Four U) (hUS : U ≤ S)
    (hUn : ∀ s ∈ S, ∀ v ∈ U, s * v * s⁻¹ ∈ U) : z ∈ U := by
  have : Group.IsNilpotent ↥S := h.S_pgroup.isNilpotent
  set H : Subgroup ↥S := U.subgroupOf S with hH
  have : H.Normal := ⟨fun n hn g => by
    rw [hH, Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hUn (g : G) g.2 (n : G) hn⟩
  have hUbot : U ≠ ⊥ := by
    intro hbot
    have := hU.2
    rw [hbot, Subgroup.card_bot] at this
    omega
  have hHbot : H ≠ ⊥ := by
    obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hUbot
    intro hbot
    have hmem : (⟨u, hUS hu⟩ : ↥S) ∈ H := by
      rw [hH, Subgroup.mem_subgroupOf]; exact hu
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hu1
    apply Subtype.ext
    simpa using congrArg Subtype.val hmem
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hHbot
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hxH : x ∈ H := hx.1
  have hxc : x ∈ Subgroup.center ↥S := hx.2
  have hxU : (x : G) ∈ U := by
    rw [hH, Subgroup.mem_subgroupOf] at hxH; exact hxH
  have hxne : (x : G) ≠ 1 := by
    intro e
    apply hx1
    apply Subtype.ext
    apply Subtype.ext
    simpa using e
  have hcent : ∀ s ∈ S, (x : G) * s = s * (x : G) := by
    intro s hs
    have := Subgroup.mem_center_iff.1 hxc ⟨s, hs⟩
    have h2 := congrArg Subtype.val this
    simpa using h2.symm
  rcases h.Z_inv x x.2 hcent (hU.1 x hxU) with h1 | h1
  · exact absurd h1 hxne
  · rw [← h1]; exact hxU

end Cfg1

namespace Cfg1K

theorem diag' (h : Cfg1K G z S P Q F FA) {s y : G} (hs : s ∈ S) (hy : y ∈ S) (hs2 : s * s = 1)
    (hy2 : y * y = 1) (hsPF : s ∉ P ⊔ F) (hyPF : y ∉ P ⊔ F) : s * y⁻¹ ∈ P ⊔ Q :=
  h.diag s hs y hy hs2 hy2 (h.toCfg1.not_R_of_not_PF hsPF) (h.toCfg1.not_R_of_not_PF hyPF)
    (h.toCfg1.not_FA_of_not_PF hs hs2 hsPF) (h.toCfg1.not_FA_of_not_PF hy hy2 hyPF)

theorem exists_q (h : Cfg1K G z S P Q F FA) (hF : IsCyclic ↥F) : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ z := by
  classical
  by_contra hno
  push Not at hno
  have hQP : ∀ q ∈ Q, q ∈ P := by
    intro q hq
    by_cases hq1 : q = 1
    · rw [hq1]; exact P.one_mem
    · rw [hno q hq hq1]; exact h.z_P
  have hRP : P ⊔ Q ≤ P := sup_le le_rfl hQP
  obtain ⟨y, hyS, hy2, hyPF⟩ := h.toCfg1.exists_outside hF
  obtain ⟨E, hES, hEx, hE8⟩ := h.rank3
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => B.comm_of_forall_sq hEx ha hb
  have hcov : ∀ e ∈ E, e ∈ P ⊔ F ∨ e * y⁻¹ ∈ P ⊔ F := fun e he =>
    B.mem_or_mul_inv_mem h.idx hyS hyPF (hES he)
  obtain ⟨e₀, he₀E, he₀PF⟩ : ∃ e₀ ∈ E, e₀ ∉ P ⊔ F := by
    by_contra hcon
    push Not at hcon
    have := h.card_PF_le hF (fun e he => hcon e he) hEx
    omega
  have he₀y : e₀ * y⁻¹ ∈ P ⊔ F := (hcov e₀ he₀E).resolve_left he₀PF
  have key : ∀ w ∈ E, w ∈ P ⊔ F → w = 1 ∨ w = z := by
    intro w hwE hwPF
    have hew : e₀ * w ∈ E := E.mul_mem he₀E hwE
    have hewPF : e₀ * w ∉ P ⊔ F := by
      intro hmem
      apply he₀PF
      have := mul_mem hmem (inv_mem hwPF)
      simpa using this
    have h1 : e₀ * y⁻¹ ∈ P := hRP (h.diag' (hES he₀E) hyS (hEx e₀ he₀E) hy2 he₀PF hyPF)
    have h2 : e₀ * w * y⁻¹ ∈ P := hRP (h.diag' (hES hew) hyS (hEx _ hew) hy2 hewPF hyPF)
    have hwP : w ∈ P := by
      have hc : e₀ * w = w * e₀ := hEc _ he₀E _ hwE
      have e1 : w = (e₀ * w * y⁻¹) * (e₀ * y⁻¹)⁻¹ := by
        calc w = w * e₀ * e₀⁻¹ := by group
          _ = e₀ * w * e₀⁻¹ := by rw [hc]
          _ = (e₀ * w * y⁻¹) * (e₀ * y⁻¹)⁻¹ := by group
      rw [e1]
      exact mul_mem h2 (inv_mem h1)
    exact h.P_inv w hwP (hEx w hwE)
  have hsub : ∀ e ∈ E, e ∈ ({1, z, e₀, z * e₀} : Finset G) := by
    intro e heE
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hePF : e ∈ P ⊔ F
    · rcases key e heE hePF with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
    · have hey : e * y⁻¹ ∈ P ⊔ F := (hcov e heE).resolve_left hePF
      have hw : e * e₀⁻¹ ∈ P ⊔ F := by
        have := mul_mem hey (inv_mem he₀y)
        have e1 : e * y⁻¹ * (e₀ * y⁻¹)⁻¹ = e * e₀⁻¹ := by group
        rwa [e1] at this
      have hwE : e * e₀⁻¹ ∈ E := E.mul_mem heE (E.inv_mem he₀E)
      have e2 : e = e * e₀⁻¹ * e₀ := by group
      rcases key _ hwE hw with h1 | h1
      · right; right; left
        rw [e2, h1, one_mul]
      · right; right; right
        rw [e2, h1]
  have hcard := B.card_subgroup_le_finset E _ hsub
  have h4 : ({1, z, e₀, z * e₀} : Finset G).card ≤ 4 := Finset.card_le_four
  omega

end Cfg1K

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1
