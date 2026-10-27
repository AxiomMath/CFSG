module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldUnitBasic
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2Img
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2Open
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSetupZStar

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

omit [Finite G] in
theorem isConj_of_cj_eq {a b s : G} (h : cj a s = b) : IsConj a b :=
  isConj_iff.2 ⟨s⁻¹, by rw [← h]; unfold cj; group⟩

theorem Datum.q_mul_self (d : Datum A) : d.q * d.q = 1 := by
  rw [← pow_two]
  exact orderOf_dvd_iff_pow_eq_one.1 (by simp [d.q_ord])

theorem Chart4.isConj_q_pi_unitary
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hS2 : chSec2OK = true) (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4)
    (hk : c.kinds = {Kind.unitary}) : IsConj d.q c.pi := by
  obtain ⟨-, -, y, hy⟩ := c.rep_of_kinds_unitary hk
  obtain ⟨hyX, hyQS, hyact⟩ := c.rep_mem Kind.unitary y hy
  have hqq := d.q_mul_self
  have hqS : d.q ∈ d.S := d.q_mem_S h
  have hqQ : d.q ∈ d.Q := d.q_mem_Q h
  have hpi2 : c.pi * c.pi = 1 := by simpa [pow_two] using c.frame.pi2
  have hpiS : c.pi ∈ d.S := c.mem.1
  have hpiq : c.pi * d.q = d.q * c.pi := d.comm_Q_S hqQ hpiS
  have hSQS : d.S ≤ d.QS := le_sup_right
  have hconjpi : ∀ {j : G}, j ∈ d.S → j * j = 1 → j ≠ 1 → j ≠ d.q → IsConj j c.pi :=
    fun hj hj2 hj1 hjq => c.involution_QS_conj_pi hα h hP hQ hc (hSQS hj) hj2 hj1 hjq
  obtain ⟨g₀, hg₀X, hg₀ne⟩ := d.exists_conj_ne h
  have hzq : IsConj d.q (g₀⁻¹ * d.q * g₀) := isConj_iff.2 ⟨g₀⁻¹, by simp⟩
  have hz2 : (g₀⁻¹ * d.q * g₀) * (g₀⁻¹ * d.q * g₀) = 1 := by
    calc (g₀⁻¹ * d.q * g₀) * (g₀⁻¹ * d.q * g₀) = g₀⁻¹ * (d.q * d.q) * g₀ := by group
      _ = 1 := by rw [hqq]; group
  have hz1 : g₀⁻¹ * d.q * g₀ ≠ 1 := fun h1 => by
    have hq1 : d.q = 1 := by
      have h2 : g₀⁻¹ * d.q * g₀ = g₀⁻¹ * 1 * g₀ := by rw [h1]; group
      exact mul_left_cancel (mul_right_cancel h2)
    have := d.q_ord
    rw [hq1, orderOf_one] at this
    omega
  by_cases hzQS : g₀⁻¹ * d.q * g₀ ∈ d.QS
  · exact hzq.trans (c.involution_QS_conj_pi hα h hP hQ hc hzQS hz2 hz1 hg₀ne)
  obtain ⟨u, hu, hzy⟩ := c.cover_unitary hk hy hg₀X hzQS
  obtain ⟨s, hs, x, hx, hcj⟩ := c.act_of_involution hα h hP hQ hS2 hc Kind.unitary hyX hyact hz2
    ⟨u, hu, hzy⟩
  have hz'eq : y * x = s⁻¹ * (g₀⁻¹ * d.q * g₀) * s := by unfold cj at hcj; exact hcj.symm
  have hz'X : y * x ∈ d.X := d.X.mul_mem hyX (d.Q_le_X hx)
  have hz'2 : (y * x) * (y * x) = 1 := by
    rw [hz'eq]
    calc s⁻¹ * (g₀⁻¹ * d.q * g₀) * s * (s⁻¹ * (g₀⁻¹ * d.q * g₀) * s)
        = s⁻¹ * ((g₀⁻¹ * d.q * g₀) * (g₀⁻¹ * d.q * g₀)) * s := by group
      _ = 1 := by rw [hz2]; group
  have hz'q : IsConj d.q (y * x) := hzq.trans (isConj_of_cj_eq hcj)
  have hz'QS : y * x ∉ d.QS := fun hmem => hyQS (by
    have := d.QS.mul_mem hmem (d.QS.inv_mem (mem_sup_left hx : x ∈ d.QS))
    simpa using this)
  have hz'act := c.act_mul_Q Kind.unitary hx hyact
  obtain ⟨g, hgq, hgX⟩ := d.exists_conj_config h hz'q
  obtain ⟨s₁, hs₁S, hs₁fix, hs₁sq⟩ := c.unitary_sq_witness hα h hP hQ hS2 hz'X hz'act
  have hs₁comm : s₁ * (y * x) = (y * x) * s₁ := by
    have : (y * x)⁻¹ * s₁ * (y * x) = s₁ := hs₁fix
    calc s₁ * (y * x) = (y * x) * ((y * x)⁻¹ * s₁ * (y * x)) := by group
      _ = (y * x) * s₁ := by rw [this]
  have hes₁X : g * s₁ * g⁻¹ ∈ d.X := hgX s₁ (d.S_le_X hs₁S) hs₁comm
  set i : G := s₁ * s₁ with hi
  have hiS : i ∈ d.S := mul_mem hs₁S hs₁S
  have hi2 : i * i = 1 := by
    rcases hs₁sq with h1 | h1
    · rw [h1, hpi2]
    · rw [h1]
      calc c.pi * d.q * (c.pi * d.q) = c.pi * (d.q * c.pi) * d.q := by group
        _ = c.pi * (c.pi * d.q) * d.q := by rw [hpiq]
        _ = (c.pi * c.pi) * (d.q * d.q) := by group
        _ = 1 := by rw [hpi2, hqq, one_mul]
  have hi1 : i ≠ 1 := by
    rcases hs₁sq with h1 | h1
    · rw [h1]; exact c.pi_ne_one
    · rw [h1]
      intro h2
      apply c.pi_ne_q hα h hP hQ
      have : c.pi = d.q⁻¹ := eq_inv_of_mul_eq_one_left h2
      rw [this]
      exact inv_eq_of_mul_eq_one_right hqq
  have hiz : i ≠ y * x := fun h1 => hz'QS (h1 ▸ hSQS hiS)
  have hicomm : i * (y * x) = (y * x) * i := by
    rw [hi]
    calc s₁ * s₁ * (y * x) = s₁ * ((y * x) * s₁) := by rw [mul_assoc, hs₁comm]
      _ = (s₁ * (y * x)) * s₁ := by group
      _ = ((y * x) * s₁) * s₁ := by rw [hs₁comm]
      _ = (y * x) * (s₁ * s₁) := by group
  have hi₁ : g * i * g⁻¹ = (g * s₁ * g⁻¹) * (g * s₁ * g⁻¹) := by rw [hi]; group
  have hi₁QS : g * i * g⁻¹ ∈ d.QS := by
    rw [hi₁]; exact c.sq_mem_QS hα h hP hQ hes₁X
  have hi₁2 : (g * i * g⁻¹) * (g * i * g⁻¹) = 1 := by
    calc (g * i * g⁻¹) * (g * i * g⁻¹) = g * (i * i) * g⁻¹ := by group
      _ = 1 := by rw [hi2]; group
  have hi₁S : g * i * g⁻¹ ∈ d.S := c.involutions_in_S' hα h hP hQ hc hi₁QS hi₁2
  have hi₁1 : g * i * g⁻¹ ≠ 1 := fun h1 => hi1 (by
    have h2 : g * i * g⁻¹ = g * 1 * g⁻¹ := by rw [h1]; group
    exact mul_left_cancel (mul_right_cancel h2))
  have hi₁q : g * i * g⁻¹ ≠ d.q := fun h1 => hiz (by
    have : i = g⁻¹ * (g * i * g⁻¹) * g := by group
    rw [this, h1, hgq])
  have hqi₁ : (g * i * g⁻¹) * d.q = d.q * (g * i * g⁻¹) := (d.comm_Q_S hqQ hi₁S)
  have hj2 : (d.q * (g * i * g⁻¹)) * (d.q * (g * i * g⁻¹)) = 1 := by
    calc (d.q * (g * i * g⁻¹)) * (d.q * (g * i * g⁻¹))
        = d.q * ((g * i * g⁻¹) * d.q) * (g * i * g⁻¹) := by group
      _ = d.q * (d.q * (g * i * g⁻¹)) * (g * i * g⁻¹) := by rw [hqi₁]
      _ = (d.q * d.q) * ((g * i * g⁻¹) * (g * i * g⁻¹)) := by group
      _ = 1 := by rw [hqq, hi₁2, one_mul]
  have hj1 : d.q * (g * i * g⁻¹) ≠ 1 := fun h1 => hi₁q (by
    have : g * i * g⁻¹ = d.q⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact inv_eq_of_mul_eq_one_right hqq)
  have hjq : d.q * (g * i * g⁻¹) ≠ d.q := fun h1 => hi₁1 (by
    have h2 : d.q * (g * i * g⁻¹) = d.q * 1 := by rw [h1, mul_one]
    exact mul_left_cancel h2)
  have hjπ : IsConj (d.q * (g * i * g⁻¹)) c.pi := hconjpi (mul_mem hqS hi₁S) hj2 hj1 hjq
  have hiz2 : (i * (y * x)) * (i * (y * x)) = 1 := by
    calc (i * (y * x)) * (i * (y * x)) = i * ((y * x) * i) * (y * x) := by group
      _ = i * (i * (y * x)) * (y * x) := by rw [hicomm]
      _ = (i * i) * ((y * x) * (y * x)) := by group
      _ = 1 := by rw [hi2, hz'2, one_mul]
  obtain ⟨s₂, hs₂, hs₂eq⟩ := c.coset_conj_unitary hα h hP hQ hz'X hz'act hz'2
    (a := y * x) ⟨1, one_mem _, (one_mul _).symm⟩ hz'2 (b := i * (y * x)) ⟨i, hiS, rfl⟩ hiz2
  have hgz : g * (y * x) * g⁻¹ = d.q := by rw [← hgq]; group
  have hconj₂ : IsConj (i * (y * x)) (d.q * (g * i * g⁻¹)) := by
    refine isConj_iff.2 ⟨g, ?_⟩
    rw [← hqi₁]
    calc g * (i * (y * x)) * g⁻¹ = (g * i * g⁻¹) * (g * (y * x) * g⁻¹) := by group
      _ = (g * i * g⁻¹) * d.q := by rw [hgz]
  exact hz'q.trans ((isConj_of_cj_eq hs₂eq).trans (hconj₂.trans hjπ))

end CFSG.OddStandard.ChengHeld
