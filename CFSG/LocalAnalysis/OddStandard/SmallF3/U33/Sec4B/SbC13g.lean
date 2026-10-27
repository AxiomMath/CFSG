module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13d

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G}

theorem c13_X_eq (t tau x₁ x₂ : G) :
    ctxX t tau x₁ x₂ = closure ({t, tau} : Set G) ⊔ fourGrp x₁ x₂ := by
  apply le_antisymm
  · rw [ctxX, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  · apply sup_le
    · rw [ctxX]
      apply Subgroup.closure_mono
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · rw [fourGrp, ctxX]
      apply Subgroup.closure_mono
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))

private theorem exists_Y_not_V (hc : Ctx13B t L S x₁ x₂ lam rho tau om) :
    ∃ a ∈ ctxYq t tau x₁ x₂ rho, a ∉ fourGrp x₁ x₂ := by
  by_contra h
  push Not at h
  have hle : ctxYq t tau x₁ x₂ rho ≤ fourGrp x₁ x₂ := fun a ha => h a ha
  have hcard := Subgroup.card_le_of_le hle
  rw [card_ctxYq hc.q_iso, hc.wreath.fourGrp_eq_omega.2.2] at hcard
  norm_num at hcard

theorem c13_V_cent_R (hc : Ctx13B t L S x₁ x₂ lam rho tau om) :
    fourGrp x₁ x₂ ≤ centralizer ((ctxR t tau x₁ x₂ : Subgroup G) : Set G) := by
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  exact c13_cent_V hc.toCtx13A r (hc.R_le_O hr) v hv

theorem c13_not_cent_R (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    t ∉ centralizer ((ctxR t tau x₁ x₂ : Subgroup G) : Set G) ∧
      tau ∉ centralizer ((ctxR t tau x₁ x₂ : Subgroup G) : Set G) ∧
      t * tau ∉ centralizer ((ctxR t tau x₁ x₂ : Subgroup G) : Set G) := by
  have hYV := exists_Y_not_V hc.toCtx13B
  refine ⟨?_, ?_, ?_⟩
  · intro ht
    obtain ⟨a, haY, haV⟩ := hYV
    have haR : a ∈ ctxR t tau x₁ x₂ :=
      l12_Q_le_R hc.toCtx11 (ctxYq_le_ctxQ haY)
    have hcomm : a * t = t * a := (Subgroup.mem_centralizer_iff.mp ht) a haR
    have hcent : a ∈ ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) :=
      ⟨haY, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
    rw [hc.Y_cent.1] at hcent
    exact haV hcent
  · intro htau
    have hx₁Q : x₁ ∈ ctxQ t tau x₁ x₂ rho :=
      hc.base_le_Q (Subgroup.subset_closure (by simp))
    have hx₁R : x₁ ∈ ctxR t tau x₁ x₂ := l12_Q_le_R hc.toCtx11 hx₁Q
    have hcomm : x₁ * tau = tau * x₁ := (Subgroup.mem_centralizer_iff.mp htau) x₁ hx₁R
    have hx1 : x₁ = x₁⁻¹ := by
      have h := hc.tau_x₁
      rw [hcomm.symm] at h
      rw [mul_assoc, mul_inv_cancel, mul_one] at h
      exact h
    have hx1sq : x₁ * x₁ = 1 := by
      nth_rewrite 1 [hx1]
      exact inv_mul_cancel x₁
    have hdvd : orderOf x₁ ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hx1sq)
    rw [hc.wreath.ord_x₁] at hdvd
    exact absurd hdvd (by norm_num)
  · intro httau
    obtain ⟨a, haY, haV⟩ := hYV
    have haR : a ∈ ctxR t tau x₁ x₂ :=
      l12_Q_le_R hc.toCtx11 (ctxYq_le_ctxQ haY)
    have hcomm : a * (t * tau) = (t * tau) * a :=
      (Subgroup.mem_centralizer_iff.mp httau) a haR
    have hcent : a ∈ ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) :=
      ⟨haY, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
    rw [hc.Y_cent.2] at hcent
    exact haV hcent

theorem c13_cent_R (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    centralizer ((ctxR t tau x₁ x₂ : Subgroup G) : Set G) = fourGrp x₁ x₂ := by
  apply le_antisymm
  · intro u hu
    have huX : u ∈ centralizer ((ctxX t tau x₁ x₂ : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp hu) x (hc.X_le_R hx)
    have huX' : u ∈ ctxX t tau x₁ x₂ := by
      rwa [(Ctx4.ctxX_facts hc.toCtx10.toCtx4).2.2.1] at huX
    rw [c13_X_eq t tau x₁ x₂] at huX'
    have hcomm : ∀ h ∈ closure ({t, tau} : Set G), ∀ k ∈ fourGrp x₁ x₂, h * k = k * h := by
      intro h hh k hk
      have hO : h ∈ ctxO t tau x₁ x₂ :=
        (Subgroup.closure_le (K := ctxO t tau x₁ x₂)).mpr
          (fun y hy => by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
            rcases hy with rfl | rfl
            · exact (c13_mem_O hc.toCtx13A).1
            · exact (c13_mem_O hc.toCtx13A).2.1) hh
      exact c13_cent_V hc.toCtx13A h hO k hk
    obtain ⟨s, hs, v, hv, huv⟩ := exists_mul_of_sup hcomm huX'
    have hvC : v ∈ centralizer ((ctxR t tau x₁ x₂ : Subgroup G) : Set G) :=
      c13_V_cent_R hc.toCtx13B hv
    have hsC : s ∈ centralizer ((ctxR t tau x₁ x₂ : Subgroup G) : Set G) := by
      have hs_eq : s = u * v⁻¹ := by rw [huv]; group
      rw [hs_eq]
      exact (Subgroup.centralizer _).mul_mem hu ((Subgroup.centralizer _).inv_mem hvC)
    have hs_cases := (mem_closure_pair_of_invol (S4A.t_mul_self hc.hyp)
      (by simpa [pow_two] using hc.l44.1)
      (S4A.mem_invCent_iff.mp (hc.le_invCent hc.tau_mem)).symm).mp hs
    have hnc := c13_not_cent_R hc
    rcases hs_cases with rfl | rfl | rfl | rfl
    · rw [huv, one_mul]; exact hv
    · exact absurd hsC hnc.1
    · exact absurd hsC hnc.2.1
    · exact absurd hsC hnc.2.2
  · exact c13_V_cent_R hc.toCtx13B

theorem c13_cent_M_Y_le_O (hc : Ctx13B t L S x₁ x₂ lam rho tau om) :
    ctxM t tau x₁ x₂ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) ≤
      ctxO t tau x₁ x₂ := by
  intro x hx
  rw [Subgroup.mem_inf] at hx
  rw [hc.O_cent, Subgroup.mem_inf]
  refine ⟨hx.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro v hv
  exact hx.2 v (hc.V_le_Y hv)

theorem c13_card_Qom (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)) = 2 ^ 8 := by
  have hA2 := c13_A2 hc
  have hKnorm : ∀ k ∈ closure ({tau, om} : Set G), ∀ h ∈ ctxQ t tau x₁ x₂ rho,
      k * h * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
    intro k hk h hh
    have hkM : k ∈ ctxM t tau x₁ x₂ :=
      (Subgroup.closure_le (K := ctxM t tau x₁ x₂)).mpr
        (fun y hy => by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl
          · exact (c13_tau_data hc.toCtx13A).1
          · exact (c13_om_data hc.toCtx13A).1) hk
    exact hc.normal_Q.2 k hkM h hh
  have hinf : ctxQ t tau x₁ x₂ rho ⊓ closure ({tau, om} : Set G) = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    have hxCO : x ∈ ctxCO t tau x₁ x₂ rho := hA2.2.2.1 hx.2
    rw [ctxCO, Subgroup.mem_inf] at hxCO
    have hxrho : x * rho = rho * x :=
      Subgroup.mem_centralizer_singleton_iff.mp hxCO.2
    exact l12_cent_Q_rho hc.toCtx11 x hx.1 hxrho
  have hcard := card_sup_eq_mul hKnorm hinf
  rw [l12_card_Q hc.toCtx11, hA2.2.1] at hcard
  rw [hcard]
  norm_num

theorem c13_t_not_cent_Y (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    t ∈ ctxO t tau x₁ x₂ ∧
      t ∉ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
  refine ⟨(c13_mem_O hc.toCtx13A).1, ?_⟩
  intro ht
  have hle : ctxYq t tau x₁ x₂ rho ≤ fourGrp x₁ x₂ := by
    intro a ha
    have hcent : a ∈ ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) :=
      ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp ht) a ha)⟩
    rw [hc.Y_cent.1] at hcent
    exact hcent
  have hcard := Subgroup.card_le_of_le hle
  rw [card_ctxYq hc.q_iso, hc.wreath.fourGrp_eq_omega.2.2] at hcard
  norm_num at hcard

theorem c13_cent_M_Y (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    ctxM t tau x₁ x₂ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) =
      ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) := by
  have hA2 := c13_A2 hc
  have hP_le_C : ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) ≤
      ctxM t tau x₁ x₂ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    apply sup_le
    · intro q hq
      refine ⟨hc.normal_Q.1 hq, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr
        (fun a ha => (hc.Q_comm q hq a (ctxYq_le_ctxQ ha)).symm)
    · intro g hg
      refine ⟨?_, ?_⟩
      · exact (Subgroup.closure_le (K := ctxM t tau x₁ x₂)).mpr
          (fun y hy => by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
            rcases hy with rfl | rfl
            · exact (c13_tau_data hc.toCtx13A).1
            · exact (c13_om_data hc.toCtx13A).1) hg
      · exact Subgroup.mem_centralizer_iff.mpr
          (fun a ha => (hA2.2.2.2 g hg a ha).symm)
  have hC_le_O : ctxM t tau x₁ x₂ ⊓
      centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) ≤ ctxO t tau x₁ x₂ :=
    c13_cent_M_Y_le_O hc.toCtx13B
  have hcardP : Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)) = 2 ^ 8 :=
    c13_card_Qom hc
  have hdiv : Nat.card ↥(ctxM t tau x₁ x₂ ⊓
      centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G)) ∣ 2 ^ 9 := by
    have h := Subgroup.card_dvd_of_le hC_le_O
    rwa [hc.card_O] at h
  have hge : 2 ^ 8 ≤ Nat.card ↥(ctxM t tau x₁ x₂ ⊓
      centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G)) := by
    have h := Subgroup.card_le_of_le hP_le_C
    rwa [hcardP] at h
  have hC_eq : Nat.card ↥(ctxM t tau x₁ x₂ ⊓
      centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G)) = 2 ^ 8 := by
    obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
    have hk_ge : 8 ≤ k := by
      have h2 : 2 ^ 8 ≤ 2 ^ k := by rw [← hk]; exact hge
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
    have hk_cases : k = 8 ∨ k = 9 := by omega
    rcases hk_cases with rfl | rfl
    · exact hk
    · exfalso
      have hCOeq : ctxM t tau x₁ x₂ ⊓
          centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) = ctxO t tau x₁ x₂ :=
        Subgroup.eq_of_le_of_card_ge hC_le_O (by rw [hk, hc.card_O])
      have htC : t ∈ ctxM t tau x₁ x₂ ⊓
          centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
        rw [hCOeq]
        exact (c13_mem_O hc.toCtx13A).1
      exact (c13_t_not_cent_Y hc).2 htC.2
  exact (Subgroup.eq_of_le_of_card_ge hP_le_C (by rw [hC_eq, hcardP])).symm

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
