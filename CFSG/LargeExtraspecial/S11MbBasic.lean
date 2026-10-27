module

public import CFSG.LargeExtraspecial.S11EightD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u_G

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G}

theorem exists_conj_inf_le {j k : G} (hx : j * S.z * j⁻¹ ∈ S.Qa k)
    (hne : j * S.z * j⁻¹ ≠ k * S.z * k⁻¹) :
    ∃ q ∈ S.Qa k, q * (j * S.z * j⁻¹) * q⁻¹ = j * S.z * j⁻¹ * (k * S.z * k⁻¹) ∧
      ∀ c ∈ S.Qa j ⊓ S.Qa k, c ∈ S.Qa (q * j) := by
  have hkj : k * S.z * k⁻¹ ∈ S.Qa j := S.mem_Qa_symm hne hx
  obtain ⟨q, hq, hqx⟩ := (S.conjBy k).exists_conj_eq_mul_z hx (conj_z_ne_one S j) hne
  refine ⟨q, hq, hqx, fun c hc => ?_⟩
  have hqc : q * c * q⁻¹ ∈ S.Qa (q * j) := conj_mem_Qa_mul S hc.1
  have hw : k * S.z * k⁻¹ ∈ S.Qa (q * j) := by
    have h1 : q * (k * S.z * k⁻¹) * q⁻¹ = k * S.z * k⁻¹ := by
      rw [commute_of_mem_Qa' hq, mul_inv_cancel_right]
    have := conj_mem_Qa_mul S (h := q) hkj
    rwa [h1] at this
  rcases (S.conjBy k).commutator_eq_one_or_z hq hc.2 with h | h
  · have e : c = q * c * q⁻¹ := by
      calc c = (q * c * q⁻¹ * c⁻¹)⁻¹ * (q * c * q⁻¹) := by group
        _ = q * c * q⁻¹ := by rw [h, inv_one, one_mul]
    rw [e]
    exact hqc
  · have h' : q * c * q⁻¹ * c⁻¹ = k * S.z * k⁻¹ := h
    have e : c = (k * S.z * k⁻¹)⁻¹ * (q * c * q⁻¹) := by
      rw [← h']
      group
    rw [e]
    exact mul_mem (inv_mem hw) hqc

variable (S g t τ u) in
structure YData (kb σ u₁ : G) : Prop where
  conj_eq : σ = u₁ * S.z * u₁⁻¹
  mem_M : σ ∈ S.M
  not_mem_QG : σ ∉ S.QG
  comm : ∀ e ∈ S.QG ⊓ S.Qa u, σ * e = e * σ
  comm_tau : σ * τ = τ * σ
  a_mem : g * S.z * g⁻¹ ∈ S.Qa u₁
  b_not_mem : kb * S.z * kb⁻¹ ∉ S.Qa u₁
  tau_b_mem : (τ : G) * (kb * S.z * kb⁻¹) ∈ S.Qa u₁
  mul_tau_not_mem : σ * τ ∉ S.QG
  apply_sub_mem : ∀ w ∈ Wt S g t,
    (S.ρ ⟨σ, mem_M⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t

variable (hy : Hyp S g) (K : Conf S g t τ u)
include hy K

theorem Conf.mem_V_cases {v : G} (hv : v ∈ V S g t) :
    v ∈ S.QG ⊓ S.Qa u ∨ v * S.z ∈ S.QG ⊓ S.Qa u := by
  obtain ⟨hvQ, hvV⟩ := S.mem_clPre.mp hv
  rw [← K.timmesfeld_11_3 hy] at hvV
  obtain ⟨e, he, heQ, hee⟩ := S.mem_clSub_iff.mp hvV
  rcases (S.cl_eq_cl_iff heQ hvQ).mp hee with rfl | rfl
  · exact Or.inl he
  · right
    rwa [mul_assoc, S.z_mul_z, mul_one]

theorem Conf.a_mem_E : g * S.z * g⁻¹ ∈ S.QG ⊓ S.Qa u := ⟨hy.hyp4.conj_mem, K.mem_Qa⟩

variable (hm : finrank (ZMod 2) (Vt S g t) = 2) {kb : G}
  (hb : kb * S.z * kb⁻¹ ∈ S.QG ⊓ S.Qa u)
  (hbs : S.cl (kb * S.z * kb⁻¹) ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹))
include hm hb hbs

theorem Conf.Vt_eq_span_pair :
    Vt S g t = Submodule.span (ZMod 2) {S.cl (g * S.z * g⁻¹), S.cl (kb * S.z * kb⁻¹)} := by
  have ha0 : S.cl (g * S.z * g⁻¹) ≠ 0 := cl_conj_z_ne_zero S hy.hyp4.conj_mem hy.hyp4.conj_ne
  have hli : LinearIndependent (ZMod 2)
      ![S.cl (g * S.z * g⁻¹), S.cl (kb * S.z * kb⁻¹)] := by
    rw [linearIndependent_pair_iff]
    refine ⟨ha0, fun h => hbs (h ▸ zero_mem _), fun h => hbs ?_⟩
    rw [← h]
    exact Submodule.mem_span_singleton_self _
  have hle : Submodule.span (ZMod 2) {S.cl (g * S.z * g⁻¹), S.cl (kb * S.z * kb⁻¹)} ≤
      Vt S g t := by
    rw [Submodule.span_le]
    rintro v (rfl | rfl)
    · exact cl_a_mem_Vt K.mem_Lbar
    · rw [← K.timmesfeld_11_3 hy]
      exact S.cl_mem_clSub hb hb.1
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_pair hli, hm])).symm

theorem Conf.mem_E_cases {e : G} (he : e ∈ S.QG ⊓ S.Qa u) :
    e = 1 ∨ e = g * S.z * g⁻¹ ∨ e = kb * S.z * kb⁻¹ ∨
      e = g * S.z * g⁻¹ * (kb * S.z * kb⁻¹) := by
  have hev : S.cl e ∈ Vt S g t := by
    rw [← K.timmesfeld_11_3 hy]
    exact S.cl_mem_clSub he he.1
  rw [K.Vt_eq_span_pair hy hm hb hbs, Submodule.mem_span_pair] at hev
  obtain ⟨r, s, hrs⟩ := hev
  have haE := K.a_mem_E hy
  have key : ∀ x ∈ S.QG ⊓ S.Qa u, S.cl x = S.cl e → e = x := fun x hx hxe => by
    rcases (S.cl_eq_cl_iff (mem_inf.mp hx).1 he.1).mp hxe with h | h
    · exact h
    · exfalso
      apply K.z_not_mem
      have h2 : x * S.z ∈ S.Qa u := h ▸ he.2
      have := mul_mem (inv_mem (mem_inf.mp hx).2) h2
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  rcases zmod2_eq_zero_or_eq_one r with rfl | rfl <;>
    rcases zmod2_eq_zero_or_eq_one s with rfl | rfl
  · exact Or.inl (key 1 (one_mem _) (by rw [S.cl_one, ← hrs]; simp))
  · exact Or.inr (Or.inr (Or.inl (key _ hb (by rw [← hrs]; simp))))
  · exact Or.inr (Or.inl (key _ haE (by rw [← hrs]; simp)))
  · exact Or.inr (Or.inr (Or.inr (key _ (mul_mem haE hb)
      (by rw [S.cl_mul haE.1 hb.1, ← hrs]; simp))))

omit hm hbs in
theorem YData.ne_conj_mul (hCE : CentralExtInput.{u_G}) (hn : 7 ≤ S.width) {σ u₁ kd : G}
    (Y : YData S g t τ u kb σ u₁) (hkd : kd * S.z * kd⁻¹ = (τ : G) * (kb * S.z * kb⁻¹))
    {β : G} (hβ : β ∈ S.QG ⊓ S.Qa u) (hβσ : β ∉ S.Qa u₁) (x : G) :
    x * σ * x⁻¹ ≠ σ * β := by
  intro hx
  have hβ1 : β ≠ 1 := fun h => hβσ (h ▸ one_mem _)
  obtain ⟨kβ, hkβ⟩ := K.exists_conj hy hβ hβ1
  have hτQ : (τ : G) ∉ S.QG := K.not_mem_QG
  have haE := K.a_mem_E hy
  have hσQa : σ ∈ S.Qa g := by
    have hne : g * S.z * g⁻¹ ≠ u₁ * S.z * u₁⁻¹ := fun h =>
      Y.not_mem_QG (by rw [Y.conj_eq, ← h]; exact hy.hyp4.conj_mem)
    rw [Y.conj_eq]
    exact S.mem_Qa_symm hne Y.a_mem
  have hkβE : kβ * S.z * kβ⁻¹ ∈ S.QG ⊓ S.Qa u := hkβ ▸ hβ
  have hτβ : (τ : G) ∈ S.Qa kβ := by
    have hne : kβ * S.z * kβ⁻¹ ≠ u * S.z * u⁻¹ := fun h =>
      hτQ (by rw [K.conj_eq, ← h]; exact (mem_inf.mp hkβE).1)
    rw [K.conj_eq]
    exact S.mem_Qa_symm hne (mem_inf.mp hkβE).2
  have hbβ : kb * S.z * kb⁻¹ ∈ S.Qa kβ := K.mem_Qa_of_mem_E hy hkβE hb
  have haβ : g * S.z * g⁻¹ ∈ S.Qa kβ := K.mem_Qa_of_mem_E hy hkβE haE
  have hdQ : (τ : G) * (kb * S.z * kb⁻¹) ∉ S.QG := fun h => hτQ (by
    have := S.QG.mul_mem h (S.QG.inv_mem (mem_inf.mp hb).1)
    rwa [mul_inv_cancel_right] at this)
  have hσd : σ ∈ S.Qa kd := by
    have hne : kd * S.z * kd⁻¹ ≠ u₁ * S.z * u₁⁻¹ := by
      rw [hkd, ← Y.conj_eq]
      intro h
      apply Y.mul_tau_not_mem
      rw [← h]
      have hτb : (τ : G) * (kb * S.z * kb⁻¹) = kb * S.z * kb⁻¹ * τ :=
        (K.commute_of_mem_Qa (mem_inf.mp hb).2).symm
      rw [hτb, mul_assoc, K.tau_mul_self, mul_one]
      exact (mem_inf.mp hb).1
    rw [Y.conj_eq]
    exact S.mem_Qa_symm hne (hkd ▸ Y.tau_b_mem)
  have h6 := hy.width_eq_six_of_conj hCE (by omega) (w := kβ) (σ := σ) (g₁ := g) (u₁ := u₁)
    (d₁ := kd) (x := x) (by rw [hkβ]; exact Y.comm β hβ)
    (fun h => hβσ (by
      have hne : u₁ * S.z * u₁⁻¹ ≠ kβ * S.z * kβ⁻¹ := fun e =>
        Y.not_mem_QG (by rw [Y.conj_eq, e]; exact (mem_inf.mp hkβE).1)
      rw [← hkβ]
      exact S.mem_Qa_symm hne (Y.conj_eq ▸ h)))
    Y.conj_eq haβ (fun h => hβσ (by rw [← hkβ, ← h]; exact Y.a_mem)) hσQa
    (by rw [hkd]; exact mul_mem hτβ hbβ)
    (by rw [hkd]; intro h; exact hdQ (h ▸ hy.hyp4.conj_mem))
    (by rw [hkd]; intro h; exact hdQ (h ▸ S.QG.mul_mem hy.hyp4.conj_mem (mem_inf.mp hkβE).1))
    hσd (by rw [hkβ]; exact hx)
  omega

end CFSG.LargeExtraspecial.S11
