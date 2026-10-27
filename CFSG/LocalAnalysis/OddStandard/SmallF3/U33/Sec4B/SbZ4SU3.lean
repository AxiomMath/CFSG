module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SE0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem z4_mem_zpowers_of_mul_self {g c : G} (hgg : g * g = 1) (hc : c ∈ zpowers g) :
    c = 1 ∨ c = g := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have h2 : g ^ (2 : ℕ) = 1 := by rw [pow_two, hgg]
  have hmod : g ^ n = g ^ (n % 2) := zpow_eq_zpow_emod' n h2
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left; rw [hmod, h]; simp
  · right; rw [hmod, h]; simp

namespace Z4Good

variable (hg : Z4Good t L S x₁ x₂ lam rho tau)
include hg

theorem lam_conj_x₁ : lam * x₁ * lam⁻¹ = x₂ := by
  have hlam : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right hg.lam_mul_self
  rw [← hg.lam_conj_x₂, hlam]
  calc lam * (lam * x₂ * lam) * lam = (lam * lam) * x₂ * (lam * lam) := by group
    _ = x₂ := by rw [hg.lam_mul_self]; group

theorem lam_conj_y : lam * x₁ ^ 2 * lam⁻¹ = x₂ ^ 2 := by
  rw [← conj_pow (a := lam) (b := x₁) (i := 2), hg.lam_conj_x₁]

theorem mem_U_decomp_O {s : G} (hs : s ∈ ctxU t tau x₁ x₂ lam) :
    ∃ o ∈ ctxO t tau x₁ x₂, ∃ d ∈ zpowers lam, s = o * d := by
  unfold ctxU at hs
  exact mem_sup_of_normalizes (A := ctxO t tau x₁ x₂) (C := zpowers lam)
    (fun c hc a ha => (S4B.p0_normal_O t tau x₁ x₂).2 c
      (Subgroup.zpowers_le.mpr hg.lam_mem_M hc) a ha) hs

theorem mem_O_of_comm_y {s : G} (hs : s ∈ ctxU t tau x₁ x₂ lam)
    (h : s * x₁ ^ 2 = x₁ ^ 2 * s) : s ∈ ctxO t tau x₁ x₂ := by
  obtain ⟨o, ho, d, hd, rfl⟩ := hg.mem_U_decomp_O hs
  rcases z4_mem_zpowers_of_mul_self hg.lam_mul_self hd with hd1 | hdlam
  · rw [hd1, mul_one]; exact ho
  · exfalso
    rw [hdlam] at h
    have hO : o ∈ ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
      rw [← hg.O_eq_CV]; exact ho
    have ho_w : o * x₂ ^ 2 = x₂ ^ 2 * o :=
      (mem_centralizer_iff.mp hO.2 (x₂ ^ 2) hg.w_mem_V).symm
    have h1 : o * lam * x₁ ^ 2 * (o * lam)⁻¹ = x₁ ^ 2 := by rw [h]; group
    have h2 : o * lam * x₁ ^ 2 * (o * lam)⁻¹ = x₂ ^ 2 := by
      rw [show o * lam * x₁ ^ 2 * (o * lam)⁻¹ = o * (lam * x₁ ^ 2 * lam⁻¹) * o⁻¹
        from by group, hg.lam_conj_y, ho_w]
      group
    have : x₁ ^ 2 = x₂ ^ 2 := by rw [← h1, h2]
    exact hg.y_ne_x₂_sq this

theorem mem_Q_of_comm_p (htau : ∀ a ∈ ctxQ t tau x₁ x₂ rho, tau * a * tau⁻¹ = a⁻¹)
    {V' : Subgroup G} {v₁ v₂ : G} (hV : Z4VBase t tau x₁ x₂ lam rho V' v₁ v₂) {s : G}
    (hs : s ∈ ctxO t tau x₁ x₂) (h₁ : s * (x₂ * x₁⁻¹) = (x₂ * x₁⁻¹) * s)
    (h₃ : s * (v₂ * v₁) = (v₂ * v₁) * s) : s ∈ ctxQ t tau x₁ x₂ rho := by
  have hcl : closure ({t, tau} : Set G) ≤ ctxM t tau x₁ x₂ := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hg.t_mem_M
    · exact hg.tau_mem_M
  rw [hg.O_eq_Q] at hs
  obtain ⟨q, hq, c, hc, rfl⟩ := mem_sup_of_normalizes
    (A := ctxQ t tau x₁ x₂ rho) (C := closure ({t, tau} : Set G))
    (fun c hc a ha => hg.normal_Q.2 c (hcl hc) a ha) hs
  let p₁ : G := x₂ * x₁⁻¹
  let p₃ : G := v₂ * v₁
  have hp₁ : p₁ = x₂ * x₁⁻¹ := rfl
  have hp₃ : p₃ = v₂ * v₁ := rfl
  have h₁' : (q * c) * p₁ = p₁ * (q * c) := by rw [hp₁]; exact h₁
  have h₃' : (q * c) * p₃ = p₃ * (q * c) := by rw [hp₃]; exact h₃
  have hp₁_mem : p₁ ∈ ctxQ t tau x₁ x₂ rho := by
    rw [hp₁]; exact mul_mem hg.x₂_mem_Q (inv_mem hg.x₁_mem_Q)
  have hp₃_mem : p₃ ∈ ctxQ t tau x₁ x₂ rho := by
    rw [hp₃]
    exact mul_mem (hV.V'_le_Q hg.toZ4Pre hV.v₂_mem) (hV.V'_le_Q hg.toZ4Pre hV.v₁_mem)
  have hx1sq_inv : (x₁ ^ 2)⁻¹ = x₁ ^ 2 :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hg.y_sq)
  have hx2sq_inv : (x₂ ^ 2)⁻¹ = x₂ ^ 2 :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hg.x₂_sq_sq)
  have K1 : x₂ ^ 2 * x₁ ^ 2 ≠ 1 := by
    intro h
    apply hg.y_ne_x₂_sq
    have h' : x₁ ^ 2 = (x₂ ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h
    rwa [hx2sq_inv] at h'
  have comm_p₃ : z4Comm t p₃ = x₂ ^ 2 * x₁ ^ 2 := by
    rw [hp₃, hg.comm_mul hg.t_mem_X (hV.V'_le_Q hg.toZ4Pre hV.v₂_mem)
        (hV.V'_le_Q hg.toZ4Pre hV.v₁_mem),
      hV.comm_v₂ hg.toZ4Pre, hV.comm_v₁ hg.toZ4Pre]
  have K2 : t * p₃ ≠ p₃ * t := by
    intro hcomm
    have h1c : z4Comm t p₃ = 1 := hg.comm_eq_one_iff.mpr hcomm
    rw [comm_p₃] at h1c
    exact K1 h1c
  have hx1neg2 : x₁⁻¹ * x₁⁻¹ = x₁ * x₁ := by
    calc x₁⁻¹ * x₁⁻¹ = (x₁ * x₁)⁻¹ := by group
      _ = (x₁ ^ 2)⁻¹ := by rw [pow_two]
      _ = x₁ ^ 2 := hx1sq_inv
      _ = x₁ * x₁ := by rw [pow_two]
  have K3 : tau * p₁ ≠ p₁ * tau := by
    intro hcomm
    have hinv : p₁⁻¹ = p₁ := by rw [← htau p₁ hp₁_mem, hcomm]; group
    have hsq : p₁ * p₁ = 1 := inv_eq_iff_mul_eq_one.mp hinv
    have hp1sq : p₁ * p₁ = x₂ ^ 2 * x₁ ^ 2 := by
      rw [hp₁]
      have hc21 : x₂ * x₁⁻¹ = x₁⁻¹ * x₂ :=
        hg.Q_comm x₂ hg.x₂_mem_Q x₁⁻¹ (inv_mem hg.x₁_mem_Q)
      calc (x₂ * x₁⁻¹) * (x₂ * x₁⁻¹)
          = x₂ * ((x₁⁻¹ * x₂) * x₁⁻¹) := by group
        _ = x₂ * ((x₂ * x₁⁻¹) * x₁⁻¹) := by rw [← hc21]
        _ = x₂ * (x₂ * (x₁⁻¹ * x₁⁻¹)) := by group
        _ = x₂ * (x₂ * (x₁ * x₁)) := by rw [hx1neg2]
        _ = x₂ ^ 2 * x₁ ^ 2 := by simp [pow_two, mul_assoc]
    have hX : x₂ ^ 2 * x₁ ^ 2 = 1 := by rw [← hp1sq]; exact hsq
    exact K1 hX
  rcases (S4B.mem_closure_pair_of_invol hg.t_mul_self hg.tau_mul_self hg.t_comm_tau).mp hc
    with hc1 | hc1 | hc1 | hc1
  · rw [hc1, mul_one]; exact hq
  · exfalso
    rw [hc1] at h₃'
    have hq_comm : q * p₃ = p₃ * q := hg.Q_comm q hq p₃ hp₃_mem
    have ht_comm : t * p₃ = p₃ * t := by
      have hh : q * (t * p₃) = q * (p₃ * t) := by
        calc q * (t * p₃) = (q * t) * p₃ := by group
          _ = p₃ * (q * t) := h₃'
          _ = (p₃ * q) * t := by group
          _ = (q * p₃) * t := by rw [hq_comm]
          _ = q * (p₃ * t) := by group
      exact mul_left_cancel hh
    exact K2 ht_comm
  · exfalso
    rw [hc1] at h₁'
    have hq_comm : q * p₁ = p₁ * q := hg.Q_comm q hq p₁ hp₁_mem
    have htau_comm : tau * p₁ = p₁ * tau := by
      have hh : q * (tau * p₁) = q * (p₁ * tau) := by
        calc q * (tau * p₁) = (q * tau) * p₁ := by group
          _ = p₁ * (q * tau) := h₁'
          _ = (p₁ * q) * tau := by group
          _ = (q * p₁) * tau := by rw [hq_comm]
          _ = q * (p₁ * tau) := by group
      exact mul_left_cancel hh
    exact K3 htau_comm
  · exfalso
    rw [hc1] at h₃'
    have hq_comm : q * p₃ = p₃ * q := hg.Q_comm q hq p₃ hp₃_mem
    have hq_q : (t * tau) * p₃ = p₃ * (t * tau) := by
      have hh : q * ((t * tau) * p₃) = q * (p₃ * (t * tau)) := by
        calc q * ((t * tau) * p₃) = (q * (t * tau)) * p₃ := by group
          _ = p₃ * (q * (t * tau)) := h₃'
          _ = (p₃ * q) * (t * tau) := by group
          _ = (q * p₃) * (t * tau) := by rw [hq_comm]
          _ = q * (p₃ * (t * tau)) := by group
      exact mul_left_cancel hh
    have hp₃_Y : p₃ ∈ ctxYq t tau x₁ x₂ rho := by
      rw [hp₃]
      exact mul_mem (hV.V'_le_Y hV.v₂_mem) (hV.V'_le_Y hV.v₁_mem)
    have htau_p₃ : tau * p₃ = p₃ * tau := hg.tau_cent p₃ hp₃_Y
    have ht_comm : t * p₃ = p₃ * t := by
      have hh : (t * p₃) * tau = (p₃ * t) * tau := by
        calc (t * p₃) * tau = t * (p₃ * tau) := by group
          _ = t * (tau * p₃) := by rw [htau_p₃]
          _ = (t * tau) * p₃ := by group
          _ = p₃ * (t * tau) := hq_q
          _ = (p₃ * t) * tau := by group
      exact mul_right_cancel hh
    exact K2 ht_comm

end Z4Good

end CFSG.OddStandard.SmallF3.HarrisU33
