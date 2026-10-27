module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbI18b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC17

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem l18_U_tG (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {R A : Subgroup G}
    (hR : IsPGroup 2 R) (h𝒮R : 𝒮 ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) (g : G) :
    g * t * g⁻¹ ∉ A := by
  obtain ⟨-, -, hAcard⟩ := hA
  have hcardR : 2 ^ 12 ≤ Nat.card R := by
    rw [← l18_card_sylow hc.toCtx18S]
    exact Subgroup.card_le_of_le h𝒮R
  exact c17_tG_not_mem_normal hc.toCtx13.toCtx11.toCtx10 hR hcardR hAN
    (le_of_eq hAcard) g

theorem l18_inv_tQ (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {x : G} (hx : x * x = 1)
    (hxQ : (∃ q ∈ ctxQ t tau x₁ x₂ rho, x = t * q) ∨
      (∃ q ∈ ctxQ t tau x₁ x₂ rho, x = (t * tau) * q)) :
    ∃ g : G, g * t * g⁻¹ = x := by
  have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact hx
  have hmemK : x ∈ conjIn (ctxK t tau x₁ x₂ rho) t := by
    rw [hc.tK]
    rcases hxQ with ⟨q, hq, hxq⟩ | ⟨q, hq, hxq⟩
    · left
      refine ⟨?_, hx2, ?_⟩
      · exact Set.mem_smul_set.mpr ⟨q, hq, by rw [hxq]; rfl⟩
      · intro hx1
        have htq : t * q = 1 := by rw [← hxq]; exact hx1
        exact hc.tG_Qom 1 q⁻¹ (Subgroup.mem_sup_left ((ctxQ t tau x₁ x₂ rho).inv_mem hq))
          (by rw [mul_eq_one_iff_eq_inv.mp htq]; group)
    · right
      refine ⟨?_, hx2, ?_⟩
      · exact Set.mem_smul_set.mpr ⟨q, hq, by rw [hxq]; rfl⟩
      · intro hx1
        have hmemM : (t * tau) ∈ conjIn (ctxM t tau x₁ x₂) t := by
          rw [hc.toCtx11.tM]
          exact Or.inr (Set.mem_smul_set.mpr
            ⟨1, (fourGrp x₁ x₂).one_mem, by rw [smul_eq_mul, mul_one]⟩)
        obtain ⟨m, -, hm⟩ := hmemM
        have htq : (t * tau) * q = 1 := by rw [← hxq]; exact hx1
        exact hc.tG_Qom m q⁻¹ (Subgroup.mem_sup_left ((ctxQ t tau x₁ x₂ rho).inv_mem hq))
          (by rw [hm, mul_eq_one_iff_eq_inv.mp htq])
  obtain ⟨k, -, hk⟩ := hmemK
  exact ⟨k, hk⟩

theorem l18_U_tQ (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {R A : Subgroup G}
    (hR : IsPGroup 2 R) (h𝒮R : 𝒮 ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) {q : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) : t * q ∉ A ∧ (t * tau) * q ∉ A := by
  have hAe : CFSG.Open.IsElemAbelian 2 A := hA.2.1
  constructor
  · intro hmem
    have hx2 : (t * q) * (t * q) = 1 := by
      have h := hAe.2 (t * q) hmem
      rwa [pow_two] at h
    obtain ⟨g, hg⟩ := l18_inv_tQ hc.toCtx13 hx2 (Or.inl ⟨q, hq, rfl⟩)
    exact l18_U_tG hc hR h𝒮R hA hAN g (by rw [hg]; exact hmem)
  · intro hmem
    have hx2 : ((t * tau) * q) * ((t * tau) * q) = 1 := by
      have h := hAe.2 ((t * tau) * q) hmem
      rwa [pow_two] at h
    obtain ⟨g, hg⟩ := l18_inv_tQ hc.toCtx13 hx2 (Or.inr ⟨q, hq, rfl⟩)
    exact l18_U_tG hc hR h𝒮R hA hAN g (by rw [hg]; exact hmem)

private theorem l18_U_tauQ_sq_mem (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮)
    {R A : Subgroup G} (h𝒮R : 𝒮 ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) {q : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) (hbA : tau * q ∈ A) :
    ∀ q' ∈ ctxQ t tau x₁ x₂ rho, q' ^ 2 ∈ A := by
  intro q' hq'
  have hq'R : q' ∈ R := h𝒮R ((l18_le_sylow hc.toCtx18S).1 hq')
  have hmem : q' * (tau * q) * q'⁻¹ * (tau * q)⁻¹ ∈ A :=
    (A).mul_mem (hAN.2 q' hq'R (tau * q) hbA) (A.inv_mem hbA)
  have hcommeq : q' * (tau * q) * q'⁻¹ * (tau * q)⁻¹ = q' ^ 2 := by
    have hmemQ : q * q'⁻¹ * q⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
      (ctxQ t tau x₁ x₂ rho).mul_mem
        ((ctxQ t tau x₁ x₂ rho).mul_mem hq ((ctxQ t tau x₁ x₂ rho).inv_mem hq'))
        ((ctxQ t tau x₁ x₂ rho).inv_mem hq)
    have h2 : tau * (q * q'⁻¹ * q⁻¹) * tau⁻¹ = q * q' * q⁻¹ := by
      rw [hc.tau_inv_Q _ hmemQ]
      group
    calc q' * (tau * q) * q'⁻¹ * (tau * q)⁻¹
        = q' * (tau * (q * q'⁻¹ * q⁻¹) * tau⁻¹) := by group
      _ = q' * (q * q' * q⁻¹) := by rw [h2]
      _ = q' ^ 2 := by
            rw [pow_two, IsZ4Z4E4.comm hc.q_iso hq hq']
            group
  rwa [hcommeq] at hmem

private theorem l18_U_tauQ_Y_le_A (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮)
    {R A : Subgroup G} (h𝒮R : 𝒮 ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) {q : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) (hbA : tau * q ∈ A) :
    ctxYq t tau x₁ x₂ rho ≤ A := by
  have hsq := l18_U_tauQ_sq_mem hc h𝒮R hA hAN hq hbA
  have hVA : fourGrp x₁ x₂ ≤ A := by
    rw [fourGrp, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hsq x₁ (hc.base_le_Q (Subgroup.subset_closure (by simp)))
    · refine hsq (x₁ * x₂) (hc.base_le_Q ((baseGrp x₁ x₂).mul_mem ?_ ?_))
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
  intro y hy
  obtain ⟨m, hm, hmy⟩ := l18_comm_tau_surj hc hy
  have hmR : m ∈ R := h𝒮R ((l18_Xi_le_sylow hc.toCtx18S) hm)
  have hcommA : m * (tau * q) * m⁻¹ * (tau * q)⁻¹ ∈ A :=
    (A).mul_mem (hAN.2 m hmR (tau * q) hbA) (A.inv_mem hbA)
  have hmqV : m * q * m⁻¹ * q⁻¹ ∈ fourGrp x₁ x₂ := l18_comm_Xi_Q_mem_V hc hm hq
  have hmqA : m * q * m⁻¹ * q⁻¹ ∈ A := hVA hmqV
  have htaufix : tau * (m * q * m⁻¹ * q⁻¹) * tau⁻¹ = m * q * m⁻¹ * q⁻¹ := by
    rw [hc.tau_cent_Y _ (l17_V_le_Y hc.toCtx13 hmqV)]
    group
  have hid : m * (tau * q) * m⁻¹ * (tau * q)⁻¹ =
      (m * tau * m⁻¹ * tau⁻¹) * (m * q * m⁻¹ * q⁻¹) := by
    rw [show m * (tau * q) * m⁻¹ * (tau * q)⁻¹ =
        (m * tau * m⁻¹ * tau⁻¹) * (tau * (m * q * m⁻¹ * q⁻¹) * tau⁻¹) by group,
      htaufix]
  have hsplit : m * tau * m⁻¹ * tau⁻¹ =
      (m * (tau * q) * m⁻¹ * (tau * q)⁻¹) * (m * q * m⁻¹ * q⁻¹)⁻¹ := by
    rw [hid]; group
  have hmτ : m * tau * m⁻¹ * tau⁻¹ ∈ A := by
    rw [hsplit]
    exact (A).mul_mem hcommA (A.inv_mem hmqA)
  rw [← hmy]
  exact hmτ

theorem l18_U_tauQ (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {R A : Subgroup G}
    (hR : IsPGroup 2 R) (h𝒮R : 𝒮 ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) {q : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) : tau * q ∉ A := by
  intro hbA
  have hYA : ctxYq t tau x₁ x₂ rho ≤ A :=
    l18_U_tauQ_Y_le_A hc h𝒮R hA hAN hq hbA
  have hYeq : ctxYq t tau x₁ x₂ rho = A :=
    Subgroup.eq_of_le_of_card_ge hYA (by rw [hA.2.2, l17_card_Y hc.toCtx13])
  have hbY : tau * q ∈ ctxYq t tau x₁ x₂ rho := hYeq.symm ▸ hbA
  have hbQ : tau * q ∈ ctxQ t tau x₁ x₂ rho := ctxYq_le_ctxQ hbY
  have htauQ : tau ∈ ctxQ t tau x₁ x₂ rho := by
    have h1 : (tau * q) * q⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
      (ctxQ t tau x₁ x₂ rho).mul_mem hbQ ((ctxQ t tau x₁ x₂ rho).inv_mem hq)
    have h2 : (tau * q) * q⁻¹ = tau := by group
    rwa [h2] at h1
  exact Ctx13.tau_not_mem_Q hc.toCtx13 htauQ

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
