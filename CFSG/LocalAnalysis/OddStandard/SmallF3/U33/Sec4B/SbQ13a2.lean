module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP12f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13a0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem q13a_closure_ttau_le_X (t tau x₁ x₂ : G) :
    closure ({t, tau} : Set G) ≤ ctxX t tau x₁ x₂ := by
  rw [ctxX]
  apply Subgroup.closure_mono
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
  rcases hy with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

private theorem q13a_om_central_N (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ctxN tau x₁ x₂ ≤ centralizer ({om} : Set G) := by
  rw [ctxN, Subgroup.closure_le]
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with hv | hv | hv
  · rw [hv]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (q13a_om_comm h).1.symm
  · rw [hv]
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((q13a_om_comm h).2.2 (x₁ ^ 2) (Subgroup.subset_closure (by simp))).symm
  · rw [hv]
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((q13a_om_comm h).2.2 ((x₁ * x₂) ^ 2) (Subgroup.subset_closure (by simp))).symm

private theorem q13a_conj_mem_A (h : Q13Om t L S x₁ x₂ lam rho tau om) {g a : G}
    (hg : g ∈ ctxM t tau x₁ x₂) (hgtau : g * tau = tau * g)
    (ha : a ∈ q13A t tau x₁ x₂ rho) : g * a * g⁻¹ ∈ q13A t tau x₁ x₂ rho := by
  rw [q13A] at ha ⊢
  refine ⟨q13a_conj_Q h hg ha.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have hatau : a * tau = tau * a := Subgroup.mem_centralizer_singleton_iff.mp ha.2
  have hgtau_inv : g⁻¹ * tau = tau * g⁻¹ := by
    have hh : tau * g⁻¹ = g⁻¹ * tau := by
      calc tau * g⁻¹ = g⁻¹ * (g * tau) * g⁻¹ := by group
        _ = g⁻¹ * (tau * g) * g⁻¹ := by rw [hgtau]
        _ = g⁻¹ * tau := by group
    exact hh.symm
  calc (g * a * g⁻¹) * tau = g * a * (g⁻¹ * tau) := by group
    _ = g * a * (tau * g⁻¹) := by rw [hgtau_inv]
    _ = g * (a * tau) * g⁻¹ := by group
    _ = g * (tau * a) * g⁻¹ := by rw [hatau]
    _ = g * tau * a * g⁻¹ := by group
    _ = tau * g * a * g⁻¹ := by rw [hgtau]
    _ = tau * (g * a * g⁻¹) := by group

private theorem q13a_conj_ttau_iff (h : Q13Om t L S x₁ x₂ lam rho tau om) (a : G) :
    a * t = t * a ↔
      (om * a * om⁻¹) * (t * tau) = (t * tau) * (om * a * om⁻¹) := by
  constructor
  · intro hat
    have hcongr := congrArg (fun x => om * x * om⁻¹) hat
    have h1 : (om * a * om⁻¹) * (om * t * om⁻¹) =
        (om * t * om⁻¹) * (om * a * om⁻¹) := by
      rw [show om * (a * t) * om⁻¹ = (om * a * om⁻¹) * (om * t * om⁻¹) from by group,
        show om * (t * a) * om⁻¹ = (om * t * om⁻¹) * (om * a * om⁻¹) from by group] at hcongr
      exact hcongr
    rw [h.t_om] at h1
    exact h1
  · intro hcent
    have h1 : (om * a * om⁻¹) * (om * t * om⁻¹) =
        (om * t * om⁻¹) * (om * a * om⁻¹) := by
      rw [← h.t_om] at hcent
      exact hcent
    have h2 : om * (a * t) * om⁻¹ = om * (t * a) * om⁻¹ := by
      rw [show (om * a * om⁻¹) * (om * t * om⁻¹) = om * (a * t) * om⁻¹ from by group,
        show (om * t * om⁻¹) * (om * a * om⁻¹) = om * (t * a) * om⁻¹ from by group] at h1
      exact h1
    exact mul_left_cancel (mul_right_cancel h2)

theorem q13a_X_om (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ctxX t tau x₁ x₂ ⊓ centralizer ({om} : Set G) = ctxN tau x₁ x₂ := by
  apply le_antisymm
  · intro g hg
    rcases l12_X_cases h.c11.toCtx4 hg.1 with hgN | htgN
    · exact hgN
    · exfalso
      have hgC : g ∈ centralizer ({om} : Set G) := hg.2
      have htgC : t * g ∈ centralizer ({om} : Set G) := q13a_om_central_N h htgN
      have htC : t ∈ centralizer ({om} : Set G) := by
        have hmem : (t * g) * g⁻¹ ∈ centralizer ({om} : Set G) :=
          Subgroup.mul_mem _ htgC (Subgroup.inv_mem _ hgC)
        have ht : (t * g) * g⁻¹ = t := by group
        rw [ht] at hmem
        exact hmem
      have hcomm_t : t * om = om * t := Subgroup.mem_centralizer_singleton_iff.mp htC
      have htau1 : tau = 1 := by
        have h1 : om * t * om⁻¹ = t := by rw [← hcomm_t]; group
        have h2 : t * tau = t := by rw [← h.t_om, h1]
        exact mul_left_cancel (by rw [h2, mul_one])
      exact l12_tau_not_mem_V h.c11.toCtx4 (by rw [htau1]; exact Subgroup.one_mem _)
  · intro g hg
    exact ⟨(p0_V_le_N_le_X t tau x₁ x₂).2 hg, q13a_om_central_N h hg⟩

theorem q13a_U_eq (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ctxU t tau x₁ x₂ lam = ctxQ t tau x₁ x₂ rho ⊔ closure {t, om} ⊔ zpowers lam := by
  have htau : tau = t * (om * t * om⁻¹) := by
    rw [h.t_om, ← mul_assoc, q13a_t_mul_self h, one_mul]
  have hsub : closure ({t, tau} : Set G) ≤ closure ({t, om} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact Subgroup.subset_closure (by simp)
    · rw [hx, htau]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp)))
          (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))))
  rw [ctxU, h.c11.O_eq, l12_R_eq h.c11, h.CO_eq]
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      · exact sup_le (le_sup_left.trans le_sup_left)
          (hsub.trans (le_sup_right.trans le_sup_left))
      · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  · apply sup_le
    · apply sup_le
      · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
      · exact le_sup_right.trans le_sup_left
    · exact le_sup_right

theorem q13a_CQt_ne (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    baseGrp x₁ x₂ ≠ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) := by
  intro heq
  have hfacts := q13a_x₁_facts h
  have hxbase : x₁ ∈ baseGrp x₁ x₂ := hfacts.2.1
  have hxQt : x₁ * t = t * x₁ := by
    have hmem : x₁ ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) :=
      (l12_CQ_t h.c11).symm ▸ hxbase
    exact Subgroup.mem_centralizer_singleton_iff.mp hmem.2
  have hxQtt : x₁ * (t * tau) = (t * tau) * x₁ := by
    have hmem : x₁ ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) :=
      heq ▸ hxbase
    exact Subgroup.mem_centralizer_singleton_iff.mp hmem.2
  have hxtau : x₁ * tau = tau * x₁ := by
    have h2 : t * (x₁ * tau) = t * (tau * x₁) := by
      calc t * (x₁ * tau) = (t * x₁) * tau := by group
        _ = (x₁ * t) * tau := by rw [hxQt]
        _ = x₁ * (t * tau) := by group
        _ = (t * tau) * x₁ := hxQtt
        _ = t * (tau * x₁) := by group
    exact mul_left_cancel h2
  have hx1 : x₁ = x₁⁻¹ := by
    rw [← hfacts.2.2.2.1, ← hxtau]
    group
  have hsq : x₁ ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [hx1]
    exact inv_mul_cancel x₁
  exact hfacts.2.2.2.2.2 hsq

theorem q13a_CQt_om (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ ctxQ t tau x₁ x₂ rho, a ∈ baseGrp x₁ x₂ ↔
      om * a * om⁻¹ ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) := by
  intro a ha
  have homM : om ∈ ctxM t tau x₁ x₂ := (q13a_mem_M h).2.2.2.2
  have hconjQ : om * a * om⁻¹ ∈ ctxQ t tau x₁ x₂ rho := q13a_conj_Q h homM ha
  constructor
  · intro hbase
    have hmem : a ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) :=
      (l12_CQ_t h.c11).symm ▸ hbase
    have hat : a * t = t * a := Subgroup.mem_centralizer_singleton_iff.mp hmem.2
    exact ⟨hconjQ, Subgroup.mem_centralizer_singleton_iff.mpr
      ((q13a_conj_ttau_iff h a).mp hat)⟩
  · rintro ⟨-, hct⟩
    have hcent : (om * a * om⁻¹) * (t * tau) = (t * tau) * (om * a * om⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp hct
    have hat : a * t = t * a := (q13a_conj_ttau_iff h a).mpr hcent
    exact (l12_CQ_t h.c11) ▸ ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr hat⟩

theorem q13a_tauQ (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    conjIn (ctxQ t tau x₁ x₂ rho) tau = tau • (fourGrp x₁ x₂ : Set G) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := hx
    rw [← h.c11.tauR]
    exact ⟨q, l12_Q_le_R h.c11 hq, rfl⟩
  · intro x hx
    rw [← h.c11.tauR] at hx
    obtain ⟨r, hr, hrx⟩ := hx
    rw [l12_R_eq h.c11] at hr
    have hK : ∀ k ∈ closure ({t, tau} : Set G), ∀ a ∈ ctxQ t tau x₁ x₂ rho,
        k * a * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
      intro k hk a ha
      have hkX : k ∈ ctxX t tau x₁ x₂ := q13a_closure_ttau_le_X t tau x₁ x₂ hk
      have hkM : k ∈ ctxM t tau x₁ x₂ := Subgroup.le_normalizer hkX
      exact h.c11.normal_Q.2 k hkM a ha
    obtain ⟨q, hq, u, hu, rfl⟩ := (mem_sup_iff_of_normalizes hK).mp hr
    have huX : u ∈ ctxX t tau x₁ x₂ := q13a_closure_ttau_le_X t tau x₁ x₂ hu
    have hucomm : u * tau = tau * u :=
      q13a_X_comm h u huX tau (Subgroup.subset_closure (by simp))
    have hcalc : (q * u) * tau * (q * u)⁻¹ = q * tau * q⁻¹ := by
      calc (q * u) * tau * (q * u)⁻¹ = q * (u * tau) * (q * u)⁻¹ := by group
        _ = q * (tau * u) * (q * u)⁻¹ := by rw [hucomm]
        _ = q * tau * q⁻¹ := by group
    exact ⟨q, hq, hcalc.symm.trans hrx⟩

theorem q13a_card_A (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card (q13A t tau x₁ x₂ rho) = 2 ^ 4 := by
  have horb := card_eq_ncard_conjIn_mul (ctxQ t tau x₁ x₂ rho) tau
  rw [q13a_tauQ h, l12_card_Q h.c11] at horb
  have hncard : (tau • (fourGrp x₁ x₂ : Set G)).ncard = 4 := by
    rw [Set.ncard_smul_set, ← Nat.card_coe_set_eq]
    exact h.c11.wreath.fourGrp_eq_omega.2.2
  rw [hncard] at horb
  have h16 : Nat.card (q13A t tau x₁ x₂ rho) = 16 := by
    change Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊓ centralizer ({tau} : Set G)) = 16
    have hh := horb
    norm_num at hh
    omega
  rw [show (2 : ℕ) ^ 4 = 16 by norm_num]
  exact h16

theorem q13a_V_le_A (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    fourGrp x₁ x₂ ≤ q13A t tau x₁ x₂ rho := by
  intro v hv
  have hvX : v ∈ ctxX t tau x₁ x₂ :=
    (p0_V_le_N_le_X t tau x₁ x₂).2 ((p0_V_le_N_le_X t tau x₁ x₂).1 hv)
  rw [q13A]
  exact ⟨q13a_V_le_Q h hv, Subgroup.mem_centralizer_singleton_iff.mpr
    (q13a_X_comm h v hvX tau (Subgroup.subset_closure (by simp)))⟩

theorem q13a_A_inv (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ q13A t tau x₁ x₂ rho, rho * a * rho⁻¹ ∈ q13A t tau x₁ x₂ rho ∧
      lam * a * lam⁻¹ ∈ q13A t tau x₁ x₂ rho ∧ om * a * om⁻¹ ∈ q13A t tau x₁ x₂ rho := by
  intro a ha
  have hM := q13a_mem_M h
  exact ⟨q13a_conj_mem_A h hM.2.2.1 h.c11.tau_rho.symm ha,
    q13a_conj_mem_A h hM.2.2.2.1 h.c11.tau_lam.symm ha,
    q13a_conj_mem_A h hM.2.2.2.2 (q13a_om_comm h).1 ha⟩

theorem q13a_t_norm_A (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ q13A t tau x₁ x₂ rho, t * a * t⁻¹ ∈ q13A t tau x₁ x₂ rho := by
  intro a ha
  exact q13a_conj_mem_A h (q13a_mem_M h).1 (q13a_t_comm h).2.2 ha

theorem q13a_x₁_not_mem_A (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    x₁ ∉ q13A t tau x₁ x₂ rho := by
  intro hx
  rw [q13A] at hx
  have hxtau : x₁ * tau = tau * x₁ := Subgroup.mem_centralizer_singleton_iff.mp hx.2
  have hfacts := q13a_x₁_facts h
  have hx1 : x₁ = x₁⁻¹ := by
    rw [← hfacts.2.2.2.1, ← hxtau]
    group
  have hsq : x₁ ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [hx1]
    exact inv_mul_cancel x₁
  exact hfacts.2.2.2.2.2 hsq

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
