module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2Basic

public section

namespace CFSG.OddStandard.ChengHeld.Excl2

open Subgroup CFSG.OddStandard.ChengHeldData
open CFSG.OddStandard.ChengHeld.ChartShape (cj_mul cj_inv cj_cj cj_of_commute cm_eq_one_iff)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem mul_eq_of_cj_eq {a b c : G} (h : cj a b = c) : a * b = b * c := by
  unfold cj at h
  calc a * b = b * (b⁻¹ * a * b) := by group
    _ = b * c := by rw [h]

omit [Finite G] in
theorem mul_mul_eq_of_cj_eq {a b c : G} (hb : b * b = 1) (h : cj a b = c) : b * a * b = c := by
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  rw [← h]
  unfold cj
  rw [hb']

namespace Cfg

variable {d : Datum A} {α : ℕ} (K : Cfg d α)

include K

theorem mu_mul_self : K.c.mu * K.c.mu = 1 := by rw [← pow_two]; exact K.c.frame.mu2
theorem lam_mul_self : K.c.lam * K.c.lam = 1 := by rw [← pow_two]; exact K.c.frame.lam2
theorem ze_mul_self : K.c.ze * K.c.ze = 1 := by rw [← pow_two]; exact K.c.frame.ze2
theorem xi_mul_self : K.c.xi * K.c.xi = 1 := by rw [← pow_two]; exact K.c.frame.xi2
theorem pi_mul_self' : K.c.pi * K.c.pi = 1 := by rw [← pow_two]; exact K.c.frame.pi2

theorem tau_mul_self : K.c.tau * K.c.tau = d.q := by
  rw [← pow_two, K.c.frame.tau_sq, K.c.q_eq]

theorem q_comm_S' {s : G} (hs : s ∈ d.S) : s * d.q = d.q * s := d.comm_Q_S K.q_mem_Q hs

theorem rel_pm : K.c.pi * K.c.mu = K.c.mu * (d.q * K.c.pi) := by
  have := mul_eq_of_cj_eq K.c.frame.pi_mu
  rwa [← K.c.q_eq] at this

theorem rel_pl : K.c.pi * K.c.lam = K.c.lam * (d.q * K.c.pi) := by
  have := mul_eq_of_cj_eq K.c.frame.pi_lam
  rwa [← K.c.q_eq] at this

theorem rel_px : K.c.pi * K.c.xi = K.c.xi * K.c.pi :=
  mul_eq_of_cj_eq K.c.frame.pi_xi

theorem rel_um : K.c.tau * K.c.mu = K.c.mu * K.c.tau :=
  (cm_eq_one_iff.1 K.c.frame.tau_mu).eq

theorem rel_ul : K.c.tau * K.c.lam = K.c.lam * (d.q * K.c.tau) := by
  have := mul_eq_of_cj_eq K.c.frame.tau_lam
  rwa [← K.c.q_eq] at this

theorem rel_ux : K.c.tau * K.c.xi = K.c.xi * (d.q * K.c.tau) := by
  have := mul_eq_of_cj_eq K.c.frame.tau_xi
  rwa [← K.c.q_eq] at this

theorem rel_ml : K.c.mu * K.c.lam = K.c.lam * K.c.mu :=
  (cm_eq_one_iff.1 K.c.frame.mu_lam).eq

theorem rel_zx : K.c.ze * K.c.xi = K.c.xi * K.c.ze :=
  (cm_eq_one_iff.1 K.c.frame.ze_xi).eq

theorem rel_mxx : K.c.mu * K.c.xi * K.c.mu * K.c.xi = K.c.pi * K.c.tau := by
  have h := K.c.frame.mu_xi
  unfold cm at h
  rwa [inv_eq_of_mul_eq_one_right K.mu_mul_self, inv_eq_of_mul_eq_one_right K.xi_mul_self] at h

theorem rel_lxx : K.c.lam * K.c.xi * K.c.lam * K.c.xi = K.c.tau := by
  have h := K.c.frame.lam_xi
  unfold cm at h
  rwa [inv_eq_of_mul_eq_one_right K.lam_mul_self, inv_eq_of_mul_eq_one_right K.xi_mul_self] at h

theorem rel_xm : K.c.xi * K.c.mu = K.c.mu * (K.c.pi * K.c.tau) * K.c.xi := by
  calc K.c.xi * K.c.mu = (K.c.mu * K.c.mu) * (K.c.xi * K.c.mu) * (K.c.xi * K.c.xi) := by
        rw [K.mu_mul_self, K.xi_mul_self]; simp
    _ = K.c.mu * (K.c.mu * K.c.xi * K.c.mu * K.c.xi) * K.c.xi := by group
    _ = K.c.mu * (K.c.pi * K.c.tau) * K.c.xi := by rw [K.rel_mxx]

theorem rel_xl : K.c.xi * K.c.lam = K.c.lam * K.c.tau * K.c.xi := by
  calc K.c.xi * K.c.lam = (K.c.lam * K.c.lam) * (K.c.xi * K.c.lam) * (K.c.xi * K.c.xi) := by
        rw [K.lam_mul_self, K.xi_mul_self]; simp
    _ = K.c.lam * (K.c.lam * K.c.xi * K.c.lam * K.c.xi) * K.c.xi := by group
    _ = K.c.lam * K.c.tau * K.c.xi := by rw [K.rel_lxx]

theorem mlx_mem_S : K.c.mu * K.c.lam * K.c.xi ∈ d.S :=
  mul_mem (mul_mem K.c.mem.2.2.1 K.c.mem.2.2.2.1) K.c.mem.2.2.2.2.2

theorem tau_comm_mlx :
    K.c.tau * (K.c.mu * K.c.lam * K.c.xi) = K.c.mu * K.c.lam * K.c.xi * K.c.tau := by
  have hqq : d.q * d.q = 1 := Sec1.q_mul_self d
  have hqx : d.q * K.c.xi = K.c.xi * d.q := (K.q_comm_S' K.c.mem.2.2.2.2.2).symm
  calc K.c.tau * (K.c.mu * K.c.lam * K.c.xi) = (K.c.tau * K.c.mu) * K.c.lam * K.c.xi := by group
    _ = (K.c.mu * K.c.tau) * K.c.lam * K.c.xi := by rw [K.rel_um]
    _ = K.c.mu * (K.c.tau * K.c.lam) * K.c.xi := by group
    _ = K.c.mu * (K.c.lam * (d.q * K.c.tau)) * K.c.xi := by rw [K.rel_ul]
    _ = K.c.mu * K.c.lam * d.q * (K.c.tau * K.c.xi) := by group
    _ = K.c.mu * K.c.lam * d.q * (K.c.xi * (d.q * K.c.tau)) := by rw [K.rel_ux]
    _ = K.c.mu * K.c.lam * (d.q * K.c.xi) * (d.q * K.c.tau) := by group
    _ = K.c.mu * K.c.lam * (K.c.xi * d.q) * (d.q * K.c.tau) := by rw [hqx]
    _ = K.c.mu * K.c.lam * K.c.xi * (d.q * d.q) * K.c.tau := by group
    _ = K.c.mu * K.c.lam * K.c.xi * K.c.tau := by rw [hqq, mul_one]

theorem mlx_sq : (K.c.mu * K.c.lam * K.c.xi) * (K.c.mu * K.c.lam * K.c.xi) = d.q * K.c.pi := by
  have hqq : d.q * d.q = 1 := Sec1.q_mul_self d
  have h1 := K.sf.sq_mlxt
  rw [pow_two] at h1
  have h2 : (K.c.mu * K.c.lam * K.c.xi) * (K.c.mu * K.c.lam * K.c.xi) * d.q = K.c.pi := by
    rw [← h1, ← K.tau_mul_self]
    calc (K.c.mu * K.c.lam * K.c.xi) * (K.c.mu * K.c.lam * K.c.xi) * (K.c.tau * K.c.tau)
        = (K.c.mu * K.c.lam * K.c.xi) * ((K.c.mu * K.c.lam * K.c.xi) * K.c.tau) * K.c.tau := by
          group
      _ = (K.c.mu * K.c.lam * K.c.xi) * (K.c.tau * (K.c.mu * K.c.lam * K.c.xi)) * K.c.tau := by
          rw [K.tau_comm_mlx]
      _ = K.c.mu * K.c.lam * K.c.xi * K.c.tau * (K.c.mu * K.c.lam * K.c.xi * K.c.tau) := by group
  have hqpi : K.c.pi * d.q = d.q * K.c.pi := (K.q_comm_S' K.c.mem.1)
  calc (K.c.mu * K.c.lam * K.c.xi) * (K.c.mu * K.c.lam * K.c.xi)
      = (K.c.mu * K.c.lam * K.c.xi) * (K.c.mu * K.c.lam * K.c.xi) * (d.q * d.q) := by
        rw [hqq, mul_one]
    _ = K.c.pi * d.q := by rw [← mul_assoc, h2]
    _ = d.q * K.c.pi := hqpi

theorem mlx_mem_W : K.c.mu * K.c.lam * K.c.xi ∈ K.c.W := by
  have hqq : d.q * d.q = 1 := Sec1.q_mul_self d
  have hql : d.q * K.c.lam = K.c.lam * d.q := (K.q_comm_S' K.c.mem.2.2.2.1).symm
  have hq : (K.c.mu * K.c.lam * K.c.xi) * d.q = d.q * (K.c.mu * K.c.lam * K.c.xi) :=
    K.q_comm_S' K.mlx_mem_S
  have hpi : K.c.pi * (K.c.mu * K.c.lam * K.c.xi) = (K.c.mu * K.c.lam * K.c.xi) * K.c.pi := by
    calc K.c.pi * (K.c.mu * K.c.lam * K.c.xi) = (K.c.pi * K.c.mu) * K.c.lam * K.c.xi := by group
      _ = (K.c.mu * (d.q * K.c.pi)) * K.c.lam * K.c.xi := by rw [K.rel_pm]
      _ = K.c.mu * d.q * (K.c.pi * K.c.lam) * K.c.xi := by group
      _ = K.c.mu * d.q * (K.c.lam * (d.q * K.c.pi)) * K.c.xi := by rw [K.rel_pl]
      _ = K.c.mu * (d.q * K.c.lam) * (d.q * K.c.pi) * K.c.xi := by group
      _ = K.c.mu * (K.c.lam * d.q) * (d.q * K.c.pi) * K.c.xi := by rw [hql]
      _ = K.c.mu * K.c.lam * (d.q * d.q) * K.c.pi * K.c.xi := by group
      _ = K.c.mu * K.c.lam * K.c.pi * K.c.xi := by rw [hqq, mul_one]
      _ = K.c.mu * K.c.lam * (K.c.pi * K.c.xi) := by group
      _ = K.c.mu * K.c.lam * (K.c.xi * K.c.pi) := by rw [K.rel_px]
      _ = (K.c.mu * K.c.lam * K.c.xi) * K.c.pi := by group
  have htu : (K.c.mu * K.c.lam * K.c.xi) * (K.c.t * K.c.tau) =
      (K.c.t * K.c.tau) * (K.c.mu * K.c.lam * K.c.xi) := by
    have ht : (K.c.mu * K.c.lam * K.c.xi) * K.c.t = K.c.t * (K.c.mu * K.c.lam * K.c.xi) :=
      K.t_comm K.mlx_mem_S
    calc (K.c.mu * K.c.lam * K.c.xi) * (K.c.t * K.c.tau)
        = ((K.c.mu * K.c.lam * K.c.xi) * K.c.t) * K.c.tau := by group
      _ = (K.c.t * (K.c.mu * K.c.lam * K.c.xi)) * K.c.tau := by rw [ht]
      _ = K.c.t * ((K.c.mu * K.c.lam * K.c.xi) * K.c.tau) := by group
      _ = K.c.t * (K.c.tau * (K.c.mu * K.c.lam * K.c.xi)) := by rw [K.tau_comm_mlx]
      _ = (K.c.t * K.c.tau) * (K.c.mu * K.c.lam * K.c.xi) := by group
  have hV : K.c.V ≤ centralizer ({K.c.mu * K.c.lam * K.c.xi} : Set G) := by
    unfold Chart4.V
    rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    rcases hg with rfl | rfl | rfl
    · exact hq.symm
    · exact hpi
    · exact htu.symm
  refine K.c.mem_W_of_comm K.mlx_mem_S fun v hv => ?_
  exact (mem_centralizer_singleton_iff.1 (hV hv)).symm

theorem cj_mlx_field {y : G}
    (hact : Kind.field.Act α K.c.t K.c.pi K.c.tau K.c.mu K.c.lam K.c.ze K.c.xi y) :
    cj (K.c.mu * K.c.lam * K.c.xi) y = K.c.mu * K.c.lam * K.c.xi := by
  have hqq : d.q * d.q = 1 := Sec1.q_mul_self d
  obtain ⟨h4, h5, h7⟩ : cj K.c.mu y = d.q * K.c.lam ∧ cj K.c.lam y = d.q * K.c.mu ∧
      cj K.c.xi y = K.c.xi := by
    by_cases hα0 : α = 0
    · simp only [Kind.Act, hα0, ↓reduceIte] at hact
      rw [← K.c.q_eq] at hact
      exact ⟨hact.2.2.2.1, hact.2.2.2.2.1, hact.2.2.2.2.2.2⟩
    · simp only [Kind.Act, hα0, ↓reduceIte] at hact
      rw [← K.c.q_eq] at hact
      exact ⟨hact.2.2.2.1, hact.2.2.2.2.1, hact.2.2.2.2.2.2⟩
  have hql : d.q * K.c.lam = K.c.lam * d.q := (K.q_comm_S' K.c.mem.2.2.2.1).symm
  have hqm : d.q * K.c.mu = K.c.mu * d.q := (K.q_comm_S' K.c.mem.2.2.1).symm
  rw [cj_mul, cj_mul, h4, h5, h7]
  calc d.q * K.c.lam * (d.q * K.c.mu) * K.c.xi = d.q * (K.c.lam * d.q) * K.c.mu * K.c.xi := by group
    _ = d.q * (d.q * K.c.lam) * K.c.mu * K.c.xi := by rw [hql]
    _ = (d.q * d.q) * K.c.lam * K.c.mu * K.c.xi := by group
    _ = K.c.lam * K.c.mu * K.c.xi := by rw [hqq, one_mul]
    _ = K.c.mu * K.c.lam * K.c.xi := by rw [← K.rel_ml]

theorem cj_mlx_graph (hα1 : α = 1) {y : G}
    (hact : Kind.graph.Act α K.c.t K.c.pi K.c.tau K.c.mu K.c.lam K.c.ze K.c.xi y) :
    cj (K.c.mu * K.c.lam * K.c.xi) y = (K.c.mu * K.c.lam * K.c.xi) * (d.q * K.c.pi) := by
  have hqq : d.q * d.q = 1 := Sec1.q_mul_self d
  have hα0 : ¬ α = 0 := by omega
  simp only [Kind.Act, hα0, ↓reduceIte] at hact
  obtain ⟨-, -, -, h4, h5, -, h7⟩ := hact
  have hqx : d.q * K.c.xi = K.c.xi * d.q := (K.q_comm_S' K.c.mem.2.2.2.2.2).symm
  rw [cj_mul, cj_mul, h4, h5, h7]
  calc K.c.ze * K.c.xi * K.c.ze * (K.c.mu * K.c.lam)
      = K.c.xi * K.c.ze * K.c.ze * (K.c.mu * K.c.lam) := by rw [K.rel_zx]
    _ = K.c.xi * (K.c.ze * K.c.ze) * (K.c.mu * K.c.lam) := by group
    _ = K.c.xi * K.c.mu * K.c.lam := by rw [K.ze_mul_self, mul_one]; group
    _ = (K.c.mu * (K.c.pi * K.c.tau) * K.c.xi) * K.c.lam := by rw [K.rel_xm]
    _ = K.c.mu * K.c.pi * K.c.tau * (K.c.xi * K.c.lam) := by group
    _ = K.c.mu * K.c.pi * K.c.tau * (K.c.lam * K.c.tau * K.c.xi) := by rw [K.rel_xl]
    _ = K.c.mu * K.c.pi * (K.c.tau * K.c.lam) * K.c.tau * K.c.xi := by group
    _ = K.c.mu * K.c.pi * (K.c.lam * (d.q * K.c.tau)) * K.c.tau * K.c.xi := by rw [K.rel_ul]
    _ = K.c.mu * (K.c.pi * K.c.lam) * (d.q * (K.c.tau * K.c.tau)) * K.c.xi := by group
    _ = K.c.mu * (K.c.lam * (d.q * K.c.pi)) * (d.q * d.q) * K.c.xi := by
        rw [K.rel_pl, K.tau_mul_self]
    _ = K.c.mu * K.c.lam * (d.q * K.c.pi) * K.c.xi := by rw [hqq, mul_one]; group
    _ = K.c.mu * K.c.lam * d.q * (K.c.pi * K.c.xi) := by group
    _ = K.c.mu * K.c.lam * d.q * (K.c.xi * K.c.pi) := by rw [K.rel_px]
    _ = K.c.mu * K.c.lam * (d.q * K.c.xi) * K.c.pi := by group
    _ = K.c.mu * K.c.lam * (K.c.xi * d.q) * K.c.pi := by rw [hqx]
    _ = (K.c.mu * K.c.lam * K.c.xi) * (d.q * K.c.pi) := by group

end Cfg

end CFSG.OddStandard.ChengHeld.Excl2
