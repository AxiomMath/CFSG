module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbA17h
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP15

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem l17_U_tG (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) {R A : Subgroup G}
    (hR : IsPGroup 2 R) (h𝒮R : 𝒮 ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) (g : G) :
    g * t * g⁻¹ ∉ A := by
  obtain ⟨-, -, hAcard⟩ := hA
  have hcardR : 2 ^ 12 ≤ Nat.card R := by
    rw [← l17_card_sylow hc]
    exact Subgroup.card_le_of_le h𝒮R
  exact c17_tG_not_mem_normal hc.toCtx13.toCtx11.toCtx10 hR hcardR hAN
    (le_of_eq hAcard) g

theorem l17_inv_tQ (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {x : G} (hx : x * x = 1)
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

theorem l17_U_tQ (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) {R A : Subgroup G}
    (hR : IsPGroup 2 R) (h𝒮R : 𝒮 ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) {q : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) : t * q ∉ A ∧ (t * tau) * q ∉ A := by
  have hAe : CFSG.Open.IsElemAbelian 2 A := hA.2.1
  constructor
  · intro hmem
    have hx2 : (t * q) * (t * q) = 1 := by
      have h := hAe.2 (t * q) hmem
      rwa [pow_two] at h
    obtain ⟨g, hg⟩ := l17_inv_tQ hc.toCtx13 hx2 (Or.inl ⟨q, hq, rfl⟩)
    exact l17_U_tG hc hR h𝒮R hA hAN g (by rw [hg]; exact hmem)
  · intro hmem
    have hx2 : ((t * tau) * q) * ((t * tau) * q) = 1 := by
      have h := hAe.2 ((t * tau) * q) hmem
      rwa [pow_two] at h
    obtain ⟨g, hg⟩ := l17_inv_tQ hc.toCtx13 hx2 (Or.inr ⟨q, hq, rfl⟩)
    exact l17_U_tG hc hR h𝒮R hA hAN g (by rw [hg]; exact hmem)

theorem l17_U_tauQ (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) {R A : Subgroup G}
    (hR : IsPGroup 2 R) (h𝒮R : 𝒮 ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) {q : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) : tau * q ∉ A := by
  intro hmem
  obtain ⟨-, -, hAcard⟩ := hA
  have hYle : ctxYq t tau x₁ x₂ rho ≤ A := by
    intro c hcY
    obtain ⟨p, hpP, hpτ⟩ := l17_comm_tau hc c hcY
    obtain ⟨-, hpC⟩ := Subgroup.mem_inf.mp hpP
    have hpR : p ∈ R := h𝒮R (l17_P_le_sylow hc hpP)
    have hpq : q * p = p * q :=
      Subgroup.mem_centralizer_iff.mp hpC q hq
    have hpCinv : p⁻¹ ∈ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      (centralizer _).inv_mem hpC
    have hpqinv : q * p⁻¹ = p⁻¹ * q :=
      Subgroup.mem_centralizer_iff.mp hpCinv q hq
    have hconj : p * (tau * q) * p⁻¹ ∈ A := hAN.2 p hpR (tau * q) hmem
    have hstep1 : p * (tau * q) * p⁻¹ = (p * tau * p⁻¹) * q := by
      calc p * (tau * q) * p⁻¹ = p * tau * (q * p⁻¹) := by group
        _ = p * tau * (p⁻¹ * q) := by rw [hpqinv]
        _ = (p * tau * p⁻¹) * q := by group
    have hstep2 : p * tau * p⁻¹ = c * tau := by
      calc p * tau * p⁻¹ = (p * tau * p⁻¹ * tau⁻¹) * tau := by group
        _ = c * tau := by rw [hpτ]
    have heq : p * (tau * q) * p⁻¹ = c * (tau * q) := by
      rw [hstep1, hstep2]; group
    have hcA : c * (tau * q) ∈ A := heq ▸ hconj
    have hprod : (c * (tau * q)) * (tau * q)⁻¹ ∈ A :=
      A.mul_mem hcA (A.inv_mem hmem)
    rwa [show (c * (tau * q)) * (tau * q)⁻¹ = c by group] at hprod
  have hYeq : ctxYq t tau x₁ x₂ rho = A :=
    Subgroup.eq_of_le_of_card_ge hYle (by rw [hAcard, l17_card_Y hc.toCtx13])
  have htauqQ : tau * q ∈ ctxQ t tau x₁ x₂ rho :=
    ctxYq_le_ctxQ (hYeq ▸ hmem)
  have htauQ : tau ∈ ctxQ t tau x₁ x₂ rho := by
    have hprod := (ctxQ t tau x₁ x₂ rho).mul_mem htauqQ
      ((ctxQ t tau x₁ x₂ rho).inv_mem hq)
    rwa [show (tau * q) * q⁻¹ = tau by group] at hprod
  exact Ctx13.tau_not_mem_Q hc.toCtx13 htauQ

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
