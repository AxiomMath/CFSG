module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13e

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G}

private lemma mem_zpowers_eq_one_or_eq {z x : G} (hz : z * z = 1) (hx : x ∈ zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : z ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, hz]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

private lemma c13_commutator_tau_B (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    ∀ b ∈ baseGrp x₁ x₂, b * tau * b⁻¹ * tau⁻¹ = b ^ 2 := by
  intro b hb
  have hbi : tau * b⁻¹ * tau⁻¹ = b := by
    have h := c13_tau_inv_B hc.toCtx13A b⁻¹ (Subgroup.inv_mem _ hb)
    simpa using h
  calc b * tau * b⁻¹ * tau⁻¹ = b * (tau * b⁻¹ * tau⁻¹) := by group
    _ = b * b := by rw [hbi]
    _ = b ^ 2 := by rw [pow_two]

theorem c13_comm_tau (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    ⁅ctxQ t tau x₁ x₂ rho, zpowers tau⁆ = fourGrp x₁ x₂ := by
  have htau := c13_tau_data hc.toCtx13A
  have hcomm := comm_zpowers_inv (A := ctxQ t tau x₁ x₂ rho) (g := tau)
    hc.Q_comm htau.2.1 (fun a ha => hc.normal_Q.2 tau htau.1 a ha)
  apply le_antisymm
  · intro n hn
    obtain ⟨a, ha, rfl⟩ := (hcomm.1 n).mp hn
    have hai : tau * a⁻¹ * tau⁻¹ = a := by
      have h := hc.tau_inv_Q a⁻¹ (Subgroup.inv_mem _ ha)
      simpa using h
    have heq : a * tau * a⁻¹ * tau⁻¹ = a ^ 2 := by
      calc a * tau * a⁻¹ * tau⁻¹ = a * (tau * a⁻¹ * tau⁻¹) := by group
        _ = a * a := by rw [hai]
        _ = a ^ 2 := by rw [pow_two]
    rw [heq]
    exact hc.sq_V a ha
  · rw [fourGrp, Subgroup.closure_le]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact (hcomm.1 (x₁ ^ 2)).mpr
        ⟨x₁, hc.base_le_Q (Subgroup.subset_closure (by simp)),
          (c13_commutator_tau_B hc x₁ (Subgroup.subset_closure (by simp))).symm⟩
    · exact (hcomm.1 ((x₁ * x₂) ^ 2)).mpr
        ⟨x₁ * x₂,
          hc.base_le_Q (Subgroup.mul_mem _
            (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))),
          (c13_commutator_tau_B hc (x₁ * x₂) (Subgroup.mul_mem _
            (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp)))).symm⟩

theorem c13_comm_Y (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    ⁅ctxQ t tau x₁ x₂ rho, zpowers om⁆ ⊔ ⁅ctxQ t tau x₁ x₂ rho, zpowers tau⁆ =
      ctxYq t tau x₁ x₂ rho := by
  obtain ⟨hle, hcard, hinf, -⟩ := c13_comm_w hc.toCtx13B
    (c13_om_data hc.toCtx13A).1 (c13_om_data hc.toCtx13A).2.1
    (c13_om_data hc.toCtx13A).2.2 hc.om_cent_Y (c13_om_nontriv hc.toCtx13B)
  rw [c13_comm_tau hc]
  apply Subgroup.eq_of_le_of_card_ge
  · exact sup_le hle hc.V_le_Y
  · have hcomm : ∀ h ∈ ⁅ctxQ t tau x₁ x₂ rho, zpowers om⁆, ∀ k ∈ fourGrp x₁ x₂,
        h * k = k * h := by
      intro h hh k hk
      exact hc.Q_comm h (ctxYq_le_ctxQ (hle hh)) k (ctxYq_le_ctxQ (hc.V_le_Y hk))
    have h := card_sup_mul_card_inf (H := ⁅ctxQ t tau x₁ x₂ rho, zpowers om⁆)
      (K := fourGrp x₁ x₂) hcomm
    rw [hinf, hcard, hc.wreath.fourGrp_eq_omega.2.2, Subgroup.card_bot] at h
    rw [mul_one] at h
    rw [card_ctxYq hc.q_iso]
    omega

theorem c13_E32_cent_Y (hc : Ctx13C t L S x₁ x₂ lam rho tau om) {u : G} (hu2 : u * u = 1)
    (huY : ∀ a ∈ ctxYq t tau x₁ x₂ rho, u * a = a * u) :
    ∃ A : Subgroup G, CFSG.Open.IsElemAbelian 2 A ∧ A ≤ centralizer ({u} : Set G) ∧
      32 ≤ Nat.card A := by
  have hYQ : ctxYq t tau x₁ x₂ rho ≤ ctxQ t tau x₁ x₂ rho := ctxYq_le_ctxQ
  by_cases hu : u ∈ ctxYq t tau x₁ x₂ rho
  · have htau2 : tau * tau = 1 := (c13_tau_data hc.toCtx13A).2.1
    have hzu : zpowers tau ≤ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_iff.mpr (fun h hh => (hc.tau_cent_Y h hh).symm))
    have hHK : ∀ h ∈ ctxYq t tau x₁ x₂ rho, ∀ k ∈ zpowers tau, h * k = k * h :=
      fun h hh k hk => Subgroup.mem_centralizer_iff.mp (hzu hk) h hh
    have htau1 : tau ≠ 1 :=
      fun h => hc.tau_not_mem (by rw [h]; exact Subgroup.mem_sup_right L.one_mem)
    have htau_notY : tau ∉ ctxYq t tau x₁ x₂ rho := by
      intro hmem
      have hmemQ : tau ∈ ctxQ t tau x₁ x₂ rho := hYQ hmem
      have hmemT : tau ∈ closure ({t, tau} : Set G) := Subgroup.subset_closure (by simp)
      have hbot : tau ∈ (⊥ : Subgroup G) := by
        rw [← l12_Q_inf_tt hc.toCtx11]
        exact ⟨hmemQ, hmemT⟩
      exact htau1 (Subgroup.mem_bot.mp hbot)
    have hinf_bot : ctxYq t tau x₁ x₂ rho ⊓ zpowers tau = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      rw [Subgroup.mem_bot]
      rcases mem_zpowers_eq_one_or_eq htau2 hx.2 with h | h
      · exact h
      · exact absurd (h ▸ hx.1) htau_notY
    have horder : orderOf tau = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact htau2) htau1
    have hcard_zp : Nat.card ↥(zpowers tau) = 2 := by rw [Nat.card_zpowers, horder]
    refine ⟨ctxYq t tau x₁ x₂ rho ⊔ zpowers tau,
      isElemAbelian_sup hc.Y_elem (isElemAbelian_zpowers htau2) hHK, ?_, ?_⟩
    · exact sup_le
        (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (huY a ha).symm)
        (Subgroup.zpowers_le.mpr
          (Subgroup.mem_centralizer_singleton_iff.mpr (hc.tau_cent_Y u hu)))
    · have hK : ∀ k ∈ zpowers tau, ∀ h ∈ ctxYq t tau x₁ x₂ rho,
          k * h * k⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
        intro k hk h hh
        rw [← hHK h hh k hk, mul_assoc, mul_inv_cancel, mul_one]
        exact hh
      have hcard := card_sup_eq_mul (H := ctxYq t tau x₁ x₂ rho) (K := zpowers tau) hK hinf_bot
      rw [card_ctxYq hc.q_iso, hcard_zp] at hcard
      norm_num at hcard
      omega
  · have hu1 : u ≠ 1 := fun h => hu (by rw [h]; exact Subgroup.one_mem _)
    have hzu : zpowers u ≤ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_iff.mpr (fun h hh => (huY h hh).symm))
    have hHK : ∀ h ∈ ctxYq t tau x₁ x₂ rho, ∀ k ∈ zpowers u, h * k = k * h :=
      fun h hh k hk => Subgroup.mem_centralizer_iff.mp (hzu hk) h hh
    have hinf_bot : ctxYq t tau x₁ x₂ rho ⊓ zpowers u = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      rw [Subgroup.mem_bot]
      rcases mem_zpowers_eq_one_or_eq hu2 hx.2 with h | h
      · exact h
      · exact absurd (h ▸ hx.1) hu
    have horder : orderOf u = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
    have hcard_zp : Nat.card ↥(zpowers u) = 2 := by rw [Nat.card_zpowers, horder]
    refine ⟨ctxYq t tau x₁ x₂ rho ⊔ zpowers u,
      isElemAbelian_sup hc.Y_elem (isElemAbelian_zpowers hu2) hHK, ?_, ?_⟩
    · exact sup_le
        (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (huY a ha).symm)
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    · have hK : ∀ k ∈ zpowers u, ∀ h ∈ ctxYq t tau x₁ x₂ rho,
          k * h * k⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
        intro k hk h hh
        rw [← hHK h hh k hk, mul_assoc, mul_inv_cancel, mul_one]
        exact hh
      have hcard := card_sup_eq_mul (H := ctxYq t tau x₁ x₂ rho) (K := zpowers u) hK hinf_bot
      rw [card_ctxYq hc.q_iso, hcard_zp] at hcard
      norm_num at hcard
      omega

theorem c13_Qom_cent_Y (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    ∀ u ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({om, tau} : Set G),
      ∀ a ∈ ctxYq t tau x₁ x₂ rho, u * a = a * u := by
  have hQ_cent : ctxQ t tau x₁ x₂ rho ≤
      centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hc.Q_comm a (ctxYq_le_ctxQ ha) q hq
  have hcl_cent : closure ({om, tau} : Set G) ≤
      centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact Subgroup.mem_centralizer_iff.mpr (fun a ha => (hc.om_cent_Y a ha).symm)
    · rw [hx]
      exact Subgroup.mem_centralizer_iff.mpr (fun a ha => (hc.tau_cent_Y a ha).symm)
  intro u hu a ha
  exact (Subgroup.mem_centralizer_iff.mp (sup_le hQ_cent hcl_cent hu) a ha).symm

theorem c13_tG_Qom (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    ∀ g : G, ∀ u ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({om, tau} : Set G), g * t * g⁻¹ ≠ u := by
  intro g u hu hgu
  have hu2 : u * u = 1 := by
    rw [← hgu]
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [S4A.t_mul_self hc.hyp]; group
  have hcent := c13_Qom_cent_Y hc u hu
  obtain ⟨A, hAe, hAc, hA32⟩ := c13_E32_cent_Y hc hu2 hcent
  have hAc' : A ≤ centralizer ({g * t * g⁻¹} : Set G) := by
    rw [hgu]
    exact hAc
  have hle := c17_card_elemAbelian_conj_le hc.toCtx10 g hAc' hAe
  omega

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
