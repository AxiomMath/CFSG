module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SE0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Z4Pre

variable (hp : Z4Pre t L S x₁ x₂ lam rho tau)
include hp

theorem not_comm_tau_Q : ¬ ∀ q ∈ ctxQ t tau x₁ x₂ rho, tau * q = q * tau := by
  intro h
  have hMle : ctxM t tau x₁ x₂ ≤ centralizer ({tau} : Set G) := by
    rw [hp.M_eq]
    apply sup_le
    · rw [hp.O_eq_Q]
      apply sup_le
      · intro q hq
        exact mem_centralizer_singleton_iff.mpr (h q hq).symm
      · rw [Subgroup.closure_le]
        rintro u (rfl | rfl)
        · exact mem_centralizer_singleton_iff.mpr hp.t_comm_tau
        · exact mem_centralizer_singleton_iff.mpr rfl
    · rw [Subgroup.closure_le]
      rintro u (rfl | rfl)
      · exact mem_centralizer_singleton_iff.mpr hp.rho_comm_tau
      · exact mem_centralizer_singleton_iff.mpr hp.tau_lam.symm
  have hC : ∀ g ∈ ctxM t tau x₁ x₂, g * tau * g⁻¹ = tau := by
    intro g hgM
    have hgc : g * tau = tau * g :=
      (mem_centralizer_iff.mp (hMle hgM) tau (Set.mem_singleton tau)).symm
    rw [hgc]; group
  have hmem : tau * x₁ ^ 2 ∈ tau • (fourGrp x₁ x₂ : Set G) :=
    Set.mem_smul_set.mpr ⟨x₁ ^ 2, hp.y_mem_V, rfl⟩
  rw [← hp.tauM] at hmem
  obtain ⟨g, hgM, hgconj⟩ := hmem
  rw [hC g hgM] at hgconj
  have hx1 : x₁ ^ 2 = 1 := by
    have h' : tau * 1 = tau * x₁ ^ 2 := by rw [mul_one]; exact hgconj
    exact (mul_left_cancel h').symm
  exact hp.y_ne_one hx1

end Z4Pre

namespace Z4Good

variable (hg : Z4Good t L S x₁ x₂ lam rho tau)
include hg

theorem comm_tau_eq_of_sq_eq {a b : G} (ha : a ∈ ctxQ t tau x₁ x₂ rho)
    (hb : b ∈ ctxQ t tau x₁ x₂ rho) (h : a ^ 2 = b ^ 2) : z4Comm tau a = z4Comm tau b := by
  have hd : a * b⁻¹ ∈ ctxQ t tau x₁ x₂ rho := mul_mem ha (inv_mem hb)
  have hd2 : (a * b⁻¹) ^ 2 = 1 := by
    have hcomm : a * b⁻¹ = b⁻¹ * a := hg.Q_comm a ha b⁻¹ (inv_mem hb)
    rw [Commute.mul_pow hcomm 2, inv_pow, ← h, mul_inv_cancel]
  have hdY : a * b⁻¹ ∈ ctxYq t tau x₁ x₂ rho := (hg.mem_Y_iff _).mpr ⟨hd, hd2⟩
  have hcent : tau * (a * b⁻¹) = (a * b⁻¹) * tau := hg.tau_cent _ hdY
  have h1 : z4Comm tau (a * b⁻¹) = 1 := hg.comm_eq_one_iff.mpr hcent
  have h2 : z4Comm tau (a * b⁻¹) = z4Comm tau a * (z4Comm tau b)⁻¹ := by
    rw [hg.comm_mul hg.tau_mem_X ha (inv_mem hb), hg.comm_inv hg.tau_mem_X hb]
  rw [h2] at h1
  exact mul_inv_eq_one.mp h1

theorem comm_tau_trivial_or_sq {V' : Subgroup G} {v₁ v₂ : G}
    (hV : Z4VBase t tau x₁ x₂ lam rho V' v₁ v₂) :
    (∀ q ∈ ctxQ t tau x₁ x₂ rho, z4Comm tau q = 1) ∨
      ∀ q ∈ ctxQ t tau x₁ x₂ rho, z4Comm tau q = q ^ 2 := by
  have hx₁Q : x₁ ∈ ctxQ t tau x₁ x₂ rho := hg.x₁_mem_Q
  have hx₂Q : x₂ ∈ ctxQ t tau x₁ x₂ rho := hg.x₂_mem_Q
  have ha₁ : z4Comm tau x₁ ∈ fourGrp x₁ x₂ :=
    hg.comm_mem hg.tau_mem_X (hg.Q_le_O hx₁Q)
  have ha₂ : z4Comm tau x₂ ∈ fourGrp x₁ x₂ :=
    hg.comm_mem hg.tau_mem_X (hg.Q_le_O hx₂Q)
  have hσx₁mem : (lam * t) * x₁ * (lam * t)⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    hg.normal_Q.2 (lam * t) hg.sigma_mem_M x₁ hx₁Q
  have hσx₁sq : ((lam * t) * x₁ * (lam * t)⁻¹) ^ 2 = x₂ ^ 2 := by
    rw [conj_pow, hg.sigma_y]
  have hb : z4Comm tau x₂ = (lam * t) * z4Comm tau x₁ * (lam * t)⁻¹ := by
    have h1 : z4Comm tau ((lam * t) * x₁ * (lam * t)⁻¹) = z4Comm tau x₂ :=
      hg.comm_tau_eq_of_sq_eq hσx₁mem hx₂Q hσx₁sq
    have h2 : z4Comm tau ((lam * t) * x₁ * (lam * t)⁻¹) =
        (lam * t) * z4Comm tau x₁ * (lam * t)⁻¹ :=
      hg.comm_conj (g := tau) (c := lam * t) hg.sigma_comm_tau.symm x₁
    exact h1.symm.trans h2
  have hρbig :
      (rho * x₁ ^ 2 * rho⁻¹ = x₂ ^ 2 ∧ rho * x₂ ^ 2 * rho⁻¹ = (x₁ * x₂) ^ 2 ∧
        rho * (x₁ * x₂) ^ 2 * rho⁻¹ = x₁ ^ 2 ∧
        z4Comm tau x₂ = rho * z4Comm tau x₁ * rho⁻¹) ∨
      (rho * x₁ ^ 2 * rho⁻¹ = (x₁ * x₂) ^ 2 ∧ rho * (x₁ * x₂) ^ 2 * rho⁻¹ = x₂ ^ 2 ∧
        rho * x₂ ^ 2 * rho⁻¹ = x₁ ^ 2 ∧
        z4Comm tau x₁ * z4Comm tau x₂ = rho * z4Comm tau x₁ * rho⁻¹) := by
    rcases hg.rho_V with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · left
      refine ⟨h1, h2, h3, ?_⟩
      have hρx₁mem : rho * x₁ * rho⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
        hg.normal_Q.2 rho hg.rho_mem_M x₁ hx₁Q
      have hρx₁sq : (rho * x₁ * rho⁻¹) ^ 2 = x₂ ^ 2 := by rw [conj_pow, h1]
      have h4 : z4Comm tau (rho * x₁ * rho⁻¹) = z4Comm tau x₂ :=
        hg.comm_tau_eq_of_sq_eq hρx₁mem hx₂Q hρx₁sq
      have h5 : z4Comm tau (rho * x₁ * rho⁻¹) = rho * z4Comm tau x₁ * rho⁻¹ :=
        hg.comm_conj (g := tau) (c := rho) hg.rho_comm_tau.symm x₁
      exact h4.symm.trans h5
    · right
      refine ⟨h1, h2, h3, ?_⟩
      have hρx₁mem : rho * x₁ * rho⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
        hg.normal_Q.2 rho hg.rho_mem_M x₁ hx₁Q
      have hx₁x₂Q : x₁ * x₂ ∈ ctxQ t tau x₁ x₂ rho := mul_mem hx₁Q hx₂Q
      have hρx₁sq : (rho * x₁ * rho⁻¹) ^ 2 = (x₁ * x₂) ^ 2 := by rw [conj_pow, h1]
      have h4 : z4Comm tau (rho * x₁ * rho⁻¹) = z4Comm tau (x₁ * x₂) :=
        hg.comm_tau_eq_of_sq_eq hρx₁mem hx₁x₂Q hρx₁sq
      have h5 : z4Comm tau (x₁ * x₂) = z4Comm tau x₁ * z4Comm tau x₂ :=
        hg.comm_mul hg.tau_mem_X hx₁Q hx₂Q
      have h6 : z4Comm tau (rho * x₁ * rho⁻¹) = rho * z4Comm tau x₁ * rho⁻¹ :=
        hg.comm_conj (g := tau) (c := rho) hg.rho_comm_tau.symm x₁
      calc z4Comm tau x₁ * z4Comm tau x₂ = z4Comm tau (x₁ * x₂) := h5.symm
        _ = z4Comm tau (rho * x₁ * rho⁻¹) := h4.symm
        _ = rho * z4Comm tau x₁ * rho⁻¹ := h6
  have hschur := schur_V (y := x₁ ^ 2) (z := (x₁ * x₂) ^ 2) (w := x₂ ^ 2)
    (ρ := rho) (σ := lam * t) (a := z4Comm tau x₁) (b := z4Comm tau x₂)
    (by rw [← pow_two]; exact hg.y_sq)
    (by rw [← pow_two]; exact hg.z_sq)
    hg.x₂_sq.symm
    (by rw [← hg.y_comm_z]; exact hg.x₂_sq.symm)
    hg.x₂_sq_ne_one
    hg.y_ne_z
    ((hg.mem_V_iff _).mp ha₁)
    hg.sigma_y hg.sigma_z hg.sigma_w
    hb hρbig
  have hVcomm : ∀ v ∈ V', z4Comm tau v = 1 := fun v hv =>
    hg.comm_eq_one_iff.mpr (hg.tau_cent v (hV.V'_le_Y hv))
  rcases hschur with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have hB : ∀ b ∈ baseGrp x₁ x₂, z4Comm tau b = 1 := by
      intro b hb0
      rw [baseGrp] at hb0
      induction hb0 using Subgroup.closure_induction with
      | mem g hmem =>
          rcases hmem with rfl | rfl
          · exact h1
          · exact h2
      | one => simp [z4Comm]
      | mul x y hx hy ihx ihy =>
          rw [hg.comm_mul hg.tau_mem_X (hg.base_le_Q hx) (hg.base_le_Q hy), ihx, ihy,
            mul_one]
      | inv x hx ihx =>
          rw [hg.comm_inv hg.tau_mem_X (hg.base_le_Q hx), ihx, inv_one]
    intro q hq
    obtain ⟨b, hbB, v, hvV, rfl⟩ := hV.mem_Q_decomp hg.toZ4Pre hq
    rw [hg.comm_mul hg.tau_mem_X (hg.base_le_Q hbB) (hV.V'_le_Q hg.toZ4Pre hvV),
      hB b hbB, hVcomm v hvV, mul_one]
  · right
    have hB : ∀ b ∈ baseGrp x₁ x₂, z4Comm tau b = b ^ 2 := by
      intro b hb0
      rw [baseGrp] at hb0
      induction hb0 using Subgroup.closure_induction with
      | mem g hmem =>
          rcases hmem with rfl | rfl
          · exact h1
          · exact h2
      | one => simp [z4Comm]
      | mul x y hx hy ihx ihy =>
          have hxy : x * y = y * x := hg.Q_comm x (hg.base_le_Q hx) y (hg.base_le_Q hy)
          rw [hg.comm_mul hg.tau_mem_X (hg.base_le_Q hx) (hg.base_le_Q hy), ihx, ihy,
            Commute.mul_pow hxy 2]
      | inv x hx ihx =>
          rw [hg.comm_inv hg.tau_mem_X (hg.base_le_Q hx), ihx, inv_pow]
    intro q hq
    obtain ⟨b, hbB, v, hvV, rfl⟩ := hV.mem_Q_decomp hg.toZ4Pre hq
    have hv2 : v ^ 2 = 1 := by rw [pow_two]; exact hV.sq_eq_one hvV
    rw [hg.comm_mul hg.tau_mem_X (hg.base_le_Q hbB) (hV.V'_le_Q hg.toZ4Pre hvV),
      hB b hbB, hVcomm v hvV, mul_one]
    have hbv : b * v = v * b := hg.Q_comm b (hg.base_le_Q hbB) v (hV.V'_le_Q hg.toZ4Pre hvV)
    rw [Commute.mul_pow hbv 2, hv2, mul_one]

theorem tau_inv_Q {V' : Subgroup G} {v₁ v₂ : G} (hV : Z4VBase t tau x₁ x₂ lam rho V' v₁ v₂) :
    ∀ a ∈ ctxQ t tau x₁ x₂ rho, tau * a * tau⁻¹ = a⁻¹ := by
  rcases hg.comm_tau_trivial_or_sq hV with h | h
  · exfalso
    apply hg.not_comm_tau_Q
    intro q hq
    exact hg.comm_eq_one_iff.mp (h q hq)
  · intro a ha
    have h1 : tau * a * tau⁻¹ * a⁻¹ = a ^ 2 := h a ha
    have h2 : tau * a * tau⁻¹ = a ^ 2 * a := by
      calc tau * a * tau⁻¹ = (tau * a * tau⁻¹ * a⁻¹) * a := by group
        _ = a ^ 2 * a := by rw [h1]
    have h4 : a ^ 4 = 1 := hg.Q_pow_four a ha
    rw [h2]
    have h5 : a ^ 2 * a * a = 1 := by
      calc a ^ 2 * a * a = a ^ 4 := by group
        _ = 1 := h4
    exact eq_inv_of_mul_eq_one_left h5

end Z4Good

end CFSG.OddStandard.SmallF3.HarrisU33
