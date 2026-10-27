module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G}

private theorem mem_normalizer_of_normalIn {A B : Subgroup G} (h : NormalIn A B) {g : G}
    (hg : g ∈ B) : g ∈ normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => h.2 g hg a ha, fun ha => ?_⟩
  have hmem := h.2 g⁻¹ (Subgroup.inv_mem _ hg) (g * a * g⁻¹) ha
  have heq : g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a := by group
  rwa [heq] at hmem

private theorem mem_zpowers_eq_one_or_eq {z x : G} (hz : z * z = 1) (hx : x ∈ zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : z ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, hz]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

theorem c13_M_le_K (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    ctxM t tau x₁ x₂ ≤ ctxK t tau x₁ x₂ rho := by
  intro g hg
  rw [ctxK, ← l12_R_eq hc]
  exact mem_normalizer_of_normalIn hc.normal_R hg

theorem c13_U_le_K (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    ctxU t tau x₁ x₂ lam ≤ ctxK t tau x₁ x₂ rho := by
  rw [ctxU]
  refine sup_le ?_ ?_
  · rw [ctxO, CFSG.Open.pCoreOf]
    exact (Subgroup.map_subtype_le _).trans (c13_M_le_K hc)
  · rw [ctxK, ← l12_R_eq hc]
    exact Subgroup.zpowers_le.mpr
      (mem_normalizer_of_normalIn hc.normal_R (l12_rho_lam_mem_M hc).2)

theorem c13_Q_le_K (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    ctxQ t tau x₁ x₂ rho ≤ ctxK t tau x₁ x₂ rho := by
  rw [ctxK, ← l12_R_eq hc]
  exact (l12_Q_le_R hc).trans Subgroup.le_normalizer

theorem c13_normalizer_Q_le_Y (t tau x₁ x₂ rho : G) :
    normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) ≤
      normalizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
  intro n hn
  have key : ∀ m ∈ normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G),
      ∀ y ∈ ctxYq t tau x₁ x₂ rho, m * y * m⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
    intro m hm y hy
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hy
    · rintro g ⟨hgQ, hg2⟩
      refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hm g).mp hgQ, ?_⟩
      calc (m * g * m⁻¹) ^ 2 = m * g ^ 2 * m⁻¹ := by rw [conj_pow]
        _ = 1 := by rw [hg2]; group
    · simpa using Subgroup.one_mem (ctxYq t tau x₁ x₂ rho)
    · intro a b _ _ ha hb
      rw [show m * (a * b) * m⁻¹ = (m * a * m⁻¹) * (m * b * m⁻¹) by group]
      exact Subgroup.mul_mem _ ha hb
    · intro a _ ha
      rw [show m * a⁻¹ * m⁻¹ = (m * a * m⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact key n hn y hy
  · intro hy
    have hn' : n⁻¹ ∈ normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      Subgroup.inv_mem _ hn
    have h := key n⁻¹ hn' (n * y * n⁻¹) hy
    have heq : n⁻¹ * (n * y * n⁻¹) * n⁻¹⁻¹ = y := by group
    rwa [heq] at h

theorem c13_Qtau_sq (hc : Ctx13C t L S x₁ x₂ lam rho tau om) {x : G}
    (hx : x ∈ ctxQ t tau x₁ x₂ rho ⊔ zpowers tau) :
    x ∈ ctxQ t tau x₁ x₂ rho ∨ x ^ 2 = 1 := by
  have hK : ∀ k ∈ zpowers tau, ∀ h ∈ ctxQ t tau x₁ x₂ rho,
      k * h * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
    intro k hk h hh
    have hkM : k ∈ ctxM t tau x₁ x₂ :=
      Subgroup.zpowers_le.mpr (c13_tau_data hc.toCtx13A).1 hk
    exact hc.normal_Q.2 k hkM h hh
  obtain ⟨h, hh, k, hk, rfl⟩ := (mem_sup_iff_of_normalizes hK).mp hx
  rcases mem_zpowers_eq_one_or_eq (c13_tau_data hc.toCtx13A).2.1 hk with rfl | hktau
  · left
    simpa using hh
  · right
    rw [hktau]
    have htau : tau * h * tau⁻¹ = h⁻¹ := hc.tau_inv_Q h hh
    have htau2 : tau * tau = 1 := (c13_tau_data hc.toCtx13A).2.1
    have h1 : (h * tau) * (h * tau) = 1 := by
      calc (h * tau) * (h * tau) = h * (tau * h * tau⁻¹) * (tau * tau) := by group
        _ = h * h⁻¹ * 1 := by rw [htau, htau2]
        _ = 1 := by group
    simpa [pow_two] using h1

theorem c13_Q_eq_closure_sq_ne (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    ctxQ t tau x₁ x₂ rho =
      closure {g : G | g ∈ ctxQ t tau x₁ x₂ rho ∧ g ^ 2 ≠ 1} := by
  apply le_antisymm
  · intro q hq
    by_cases hq2 : q ^ 2 = 1
    · have hx₁Q : x₁ ∈ ctxQ t tau x₁ x₂ rho :=
        hc.base_le_Q (Subgroup.subset_closure (by simp))
      have hx₁2 : x₁ ^ 2 ≠ 1 := by
        intro h
        have hd : orderOf x₁ ∣ 2 := orderOf_dvd_of_pow_eq_one h
        rw [hc.wreath.ord_x₁] at hd
        obtain ⟨k, hk⟩ := hd
        omega
      have hqx₁Q : q * x₁ ∈ ctxQ t tau x₁ x₂ rho := Subgroup.mul_mem _ hq hx₁Q
      have hqx₁2 : (q * x₁) ^ 2 ≠ 1 := by
        have hcomm : q * x₁ = x₁ * q := hc.Q_comm q hq x₁ hx₁Q
        have hsq : (q * x₁) ^ 2 = q ^ 2 * x₁ ^ 2 := by
          calc (q * x₁) ^ 2 = (q * x₁) * (q * x₁) := by rw [pow_two]
            _ = q * (x₁ * q) * x₁ := by group
            _ = q * (q * x₁) * x₁ := by rw [hcomm]
            _ = (q * q) * (x₁ * x₁) := by group
            _ = q ^ 2 * x₁ ^ 2 := by rw [pow_two, pow_two]
        rw [hsq, hq2, one_mul]
        exact hx₁2
      have hx₁invQ : x₁⁻¹ ∈ ctxQ t tau x₁ x₂ rho := Subgroup.inv_mem _ hx₁Q
      have hx₁inv2 : (x₁⁻¹) ^ 2 ≠ 1 := by
        intro h
        apply hx₁2
        have hinv : (x₁⁻¹) ^ 2 = (x₁ ^ 2)⁻¹ := by rw [inv_pow]
        rw [hinv] at h
        exact inv_eq_one.mp h
      have hqeq : q = (q * x₁) * x₁⁻¹ := by group
      rw [hqeq]
      exact Subgroup.mul_mem _
        (Subgroup.subset_closure ⟨hqx₁Q, hqx₁2⟩)
        (Subgroup.subset_closure ⟨hx₁invQ, hx₁inv2⟩)
    · exact Subgroup.subset_closure ⟨hq, hq2⟩
  · exact (Subgroup.closure_le _).2 (fun g hg => hg.1)

theorem c13_normalizer_Qtau_le_Q (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    normalizer ((ctxQ t tau x₁ x₂ rho ⊔ zpowers tau : Subgroup G) : Set G) ≤
      normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := by
  intro n hn
  have key : ∀ m ∈ normalizer ((ctxQ t tau x₁ x₂ rho ⊔ zpowers tau : Subgroup G) : Set G),
      ∀ g ∈ ctxQ t tau x₁ x₂ rho, m * g * m⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
    intro m hm g hg
    have hg' : g ∈ closure {g : G | g ∈ ctxQ t tau x₁ x₂ rho ∧ g ^ 2 ≠ 1} := by
      rw [← c13_Q_eq_closure_sq_ne hc]
      exact hg
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hg'
    · rintro a ⟨haQ, ha2⟩
      have haQ' : a ∈ ctxQ t tau x₁ x₂ rho ⊔ zpowers tau := Subgroup.mem_sup_left haQ
      have hconj : m * a * m⁻¹ ∈ ctxQ t tau x₁ x₂ rho ⊔ zpowers tau :=
        (Subgroup.mem_normalizer_iff.mp hm a).mp haQ'
      rcases c13_Qtau_sq hc hconj with h | h
      · exact h
      · exfalso
        apply ha2
        have hc2 : (m * a * m⁻¹) ^ 2 = m * a ^ 2 * m⁻¹ := by rw [conj_pow]
        rw [hc2] at h
        have hmul : m * a ^ 2 = m := by
          have h1 : m * a ^ 2 * m⁻¹ = m * m⁻¹ := by rw [h, mul_inv_cancel]
          exact mul_right_cancel h1
        exact mul_left_cancel (by rw [hmul, mul_one])
    · simpa using Subgroup.one_mem (ctxQ t tau x₁ x₂ rho)
    · intro a b _ _ ha hb
      rw [show m * (a * b) * m⁻¹ = (m * a * m⁻¹) * (m * b * m⁻¹) by group]
      exact Subgroup.mul_mem _ ha hb
    · intro a _ ha
      rw [show m * a⁻¹ * m⁻¹ = (m * a * m⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact key n hn y hy
  · intro hy
    have hn' : n⁻¹ ∈
        normalizer ((ctxQ t tau x₁ x₂ rho ⊔ zpowers tau : Subgroup G) : Set G) :=
      Subgroup.inv_mem _ hn
    have h := key n⁻¹ hn' (n * y * n⁻¹) hy
    have heq : n⁻¹ * (n * y * n⁻¹) * n⁻¹⁻¹ = y := by group
    rwa [heq] at h

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
