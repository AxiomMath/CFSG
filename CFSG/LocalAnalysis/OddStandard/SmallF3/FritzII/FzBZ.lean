module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBI1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB0B

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

structure FzbRel {G : Type} [Group G] (T₂ P : Subgroup G) (t q s lam rho : G) : Prop where
  q_mem : q ∈ T₂
  s_mem : s ∈ T₂
  lam_mem : lam ∈ T₂
  q_pow : q ^ 4 = 1
  q_sq : q ^ 2 = t
  s_sq : ∃ j : ℕ, s ^ 2 = q ^ j
  s_q : s * q * s⁻¹ = q ∨ s * q * s⁻¹ = q⁻¹
  lam_sq : lam ^ 2 = 1
  lam_q : lam * q = q * lam
  lam_s : lam * s = s * lam
  rho_pow : rho ^ 3 = 1
  rho_q : rho * q = q * rho
  rho_s : rho * s = s * rho
  lam_rho : lam * rho * lam⁻¹ = rho⁻¹
  card_cent : Nat.card ↥(P ⊓ Subgroup.centralizer ({t} : Set G)) = 16
  s_inv : ∀ e ∈ P ⊓ Subgroup.centralizer ({t} : Set G), s * e * s⁻¹ = e⁻¹

section Rel

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
  {T₂ P : Subgroup G} {q s : G}

theorem fzb_rel (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 4)
    (hS : FzbStruct t S x₁ x₂ lam rho tau T₂ P q s) : FzbRel T₂ P t q s lam rho := by
  have hq := hS.q_gen
  obtain ⟨hq_ord, hq_sq⟩ := fzbs_q_facts h hK hq
  obtain ⟨-, -, -, hτX, hτK⟩ := fzbs_tau_facts h
  have hqK : q ∈ twoCore t := by rw [← hq]; exact Subgroup.mem_zpowers q
  have hq_mem : q ∈ T₂ := by
    rw [hS.gen]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hs_mem : s ∈ T₂ := by
    rw [hS.gen]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hlam_mem : lam ∈ T₂ := by
    rw [hS.gen]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hq4 : q ^ 4 = 1 := by rw [← hq_ord]; exact pow_orderOf_eq_one q
  have hlam2 : lam ^ 2 = 1 := by
    rw [← h.wreath.ord_lam]; exact pow_orderOf_eq_one lam
  have hrho3 : rho ^ 3 = 1 := by rw [← h.ord_rho]; exact pow_orderOf_eq_one rho
  have hlamL : lam ∈ L := by
    have hw : lam ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
    rw [← h.inf_eq] at hw
    exact hw.2
  have hq_cent : q ∈ Subgroup.centralizer (L : Set G) := by
    have hmem : q ∈ Subgroup.centralizer (L : Set G) ⊓ invCent t := by
      rw [h.hyp.centralizer_eq]; exact hqK
    exact hmem.1
  have hq_comm : ∀ y ∈ L, y * q = q * y :=
    fun y hy => (Subgroup.mem_centralizer_iff.mp hq_cent) y hy
  have hlam_q : lam * q = q * lam := hq_comm lam hlamL
  have hrho_q : rho * q = q * rho := hq_comm rho h.rho_mem
  have hs_q : s * q * s⁻¹ = q ∨ s * q * s⁻¹ = q⁻¹ := by
    rcases hS.s_cases with rfl | rfl
    · exact fzbs_tau_q h hK hq
    · rcases fzbs_tau_q h hK hq with hc | hc
      · left
        calc (q * tau) * q * (q * tau)⁻¹ = q * (tau * q * tau⁻¹) * q⁻¹ := by group
          _ = q * q * q⁻¹ := by rw [hc]
          _ = q := by group
      · right
        calc (q * tau) * q * (q * tau)⁻¹ = q * (tau * q * tau⁻¹) * q⁻¹ := by group
          _ = q * q⁻¹ * q⁻¹ := by rw [hc]
          _ = q⁻¹ := by group
  have hs_sq_mem : s ^ 2 ∈ twoCore t := by
    rcases hS.s_cases with rfl | rfl
    · exact h.tau_sq_mem
    · have hsq : (q * tau) ^ 2 = q * (tau * q * tau⁻¹) * tau ^ 2 := by
        rw [pow_two]; group
      rw [hsq]
      exact (twoCore t).mul_mem ((twoCore t).mul_mem hqK (hτK q hqK)) h.tau_sq_mem
  have hs_sq : ∃ j : ℕ, s ^ 2 = q ^ j := by
    have hmem : s ^ 2 ∈ zpowers q := by rw [hq]; exact hs_sq_mem
    have hpow : s ^ 2 ∈ Submonoid.powers q := mem_powers_iff_mem_zpowers.mpr hmem
    rw [Submonoid.mem_powers_iff] at hpow
    obtain ⟨j, hj⟩ := hpow
    exact ⟨j, hj.symm⟩
  have hlam_s : lam * s = s * lam := by
    rcases hS.s_cases with rfl | rfl
    · exact h.tau_lam.symm
    · calc lam * (q * tau) = (lam * q) * tau := by group
        _ = (q * lam) * tau := by rw [hlam_q]
        _ = q * (lam * tau) := by group
        _ = q * (tau * lam) := by rw [h.tau_lam]
        _ = (q * tau) * lam := by group
  have hrho_s : rho * s = s * rho := by
    rcases hS.s_cases with rfl | rfl
    · exact h.tau_rho.symm
    · calc rho * (q * tau) = (rho * q) * tau := by group
        _ = (q * rho) * tau := by rw [hrho_q]
        _ = q * (rho * tau) := by group
        _ = q * (tau * rho) := by rw [h.tau_rho]
        _ = (q * tau) * rho := by group
  have hcard_cent : Nat.card ↥(P ⊓ Subgroup.centralizer ({t} : Set G)) = 16 := by
    rw [hS.cent_t]
    exact (WreathRel.baseGrp_eq h.wreath).2.2
  have hs_inv : ∀ e ∈ P ⊓ Subgroup.centralizer ({t} : Set G), s * e * s⁻¹ = e⁻¹ := by
    intro e he
    have heE : e ∈ baseGrp x₁ x₂ := by rwa [hS.cent_t] at he
    have heX : e ∈ fzbsX t x₁ x₂ := (fzbs_X_le h).2.2.1 heE
    rcases hS.s_cases with rfl | rfl
    · exact hτX e heX
    · have hτe : tau * e * tau⁻¹ = e⁻¹ := hτX e heX
      have hqe : q * e = e * q := by
        have hqW : q ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_left hqK
        have heW : e ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_right heE
        exact congrArg Subtype.val
          (isMulCommutative_iff.mp h.abelian_W ⟨q, hqW⟩ ⟨e, heW⟩)
      have hqe' : q * e⁻¹ = e⁻¹ * q :=
        (Commute.inv_right (show Commute q e from hqe)).eq
      calc (q * tau) * e * (q * tau)⁻¹ = q * (tau * e * tau⁻¹) * q⁻¹ := by group
        _ = q * e⁻¹ * q⁻¹ := by rw [hτe]
        _ = e⁻¹ := by rw [hqe']; group
  exact ⟨hq_mem, hs_mem, hlam_mem, hq4, hq_sq, hs_sq, hs_q, hlam2, hlam_q,
    hlam_s, hrho3, hrho_q, hrho_s, h.lam_rho, hcard_cent, hs_inv⟩

theorem fzb_Z_facts (h : Ctx t L S x₁ x₂ lam rho tau)
    (hS : FzbStruct t S x₁ x₂ lam rho tau T₂ P q s) :
    x₁ ∈ P ∧ x₂ ∈ P ∧ fourGrp x₁ x₂ ≤ P ∧ Nat.card ↥(fourGrp x₁ x₂) = 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hS.E_le_P (Subgroup.subset_closure (by simp))
  · exact hS.E_le_P (Subgroup.subset_closure (by simp))
  · exact (fzbs_X_le h).2.1.trans hS.E_le_P
  · exact fzl_card_Z h

theorem fzb_s_comm_Z (hS : FzbStruct t S x₁ x₂ lam rho tau T₂ P q s) {p : G} (hp : p ∈ P) :
    s * p * s⁻¹ * p⁻¹ ∈ fourGrp x₁ x₂ := by
  simpa only [commutatorElement_def] using hS.s_comm_P p hp

end Rel

end CFSG.OddStandard.SmallF3.FritzII
