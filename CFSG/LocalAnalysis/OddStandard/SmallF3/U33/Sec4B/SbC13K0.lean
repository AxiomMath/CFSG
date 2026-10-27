module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13M
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP12h
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13KKlein
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

@[expose] def c13KTp (t tau x₁ x₂ rho : G) : Set G :=
  InvIn (t • (ctxQ t tau x₁ x₂ rho : Set G)) ∪ InvIn ((t * tau) • (ctxQ t tau x₁ x₂ rho : Set G))

private lemma c13K_ttau_sq (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    (t * tau) * (t * tau) = 1 := by
  have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
  have h1 : (om * t * om⁻¹) * (om * t * om⁻¹) = 1 := by
    calc (om * t * om⁻¹) * (om * t * om⁻¹) = om * (t * t) * om⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  rwa [hc.t_om] at h1

theorem c13K_rel (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    t ^ 2 = 1 ∧ t ≠ 1 ∧ om ^ 2 = 1 ∧ tau ^ 2 = 1 ∧ tau ≠ 1 ∧ t * tau = tau * t ∧
      tau * om = om * tau ∧ om * t * om⁻¹ = t * tau := by
  have ht2 : t ^ 2 = 1 := by
    rw [← hc.hyp.ord_t]
    exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h
    have hord := hc.hyp.ord_t
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hom2 : om ^ 2 = 1 := by rw [pow_two, hc.om_sq]
  have htau2 : tau ^ 2 = 1 := hc.l44.1
  have htau1 : tau ≠ 1 := by
    intro h
    exact hc.tau_not_mem (by rw [h]; exact (twoCore t ⊔ L).one_mem)
  have httau : t * tau = tau * t :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hc.le_invCent hc.tau_mem)).symm
  have htauCO : tau ∈ ctxCO t tau x₁ x₂ rho ⊓
      centralizer ((ctxCO t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    le_of_eq hc.CO_center.symm (Subgroup.mem_zpowers tau)
  have htauom : tau * om = om * tau :=
    (Subgroup.mem_centralizer_iff.mp htauCO.2 om hc.om_mem).symm
  exact ⟨ht2, ht1, hom2, htau2, htau1, httau, htauom, hc.t_om⟩

theorem c13K_rho_comm (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    rho * t = t * rho ∧ rho * tau = tau * rho ∧ rho * om = om * rho := by
  have hrt : rho * t = t * rho :=
    Subgroup.mem_centralizer_iff.mp hc.hyp.mem_centralizer rho hc.rho_mem
  have hrtau : rho * tau = tau * rho := hc.tau_rho.symm
  have hrom : rho * om = om * rho :=
    (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc.om_mem).2).symm
  exact ⟨hrt, hrtau, hrom⟩

theorem c13K_mem_M (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    t ∈ ctxM t tau x₁ x₂ ∧ tau ∈ ctxM t tau x₁ x₂ ∧ om ∈ ctxM t tau x₁ x₂ ∧
      rho ∈ ctxM t tau x₁ x₂ ∧ lam ∈ ctxM t tau x₁ x₂ := by
  obtain ⟨ht, htau, -, -, hrho, hlam⟩ := p0_gens_mem_M hc.toCtx4
  have homO : om ∈ ctxO t tau x₁ x₂ := (Subgroup.mem_inf.mp hc.om_mem).1
  exact ⟨ht, htau, p0_O_le_M t tau x₁ x₂ homO, hrho, hlam⟩

theorem c13K_not_mem_Q (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    t ∉ ctxQ t tau x₁ x₂ rho ∧ tau ∉ ctxQ t tau x₁ x₂ rho ∧
      t * tau ∉ ctxQ t tau x₁ x₂ rho := by
  obtain ⟨ht2, ht1, -, htau2, htau1, -, -, -⟩ := c13K_rel hc
  obtain ⟨hrt, hrtau, hrom⟩ := c13K_rho_comm hc
  refine ⟨?_, ?_, ?_⟩
  · intro htQ
    have hconj : rho * t * rho⁻¹ = t := by rw [hrt, mul_assoc, mul_inv_cancel, mul_one]
    exact ht1 (hc.fpf_QY.fix t htQ hconj)
  · intro htauQ
    have hconj : rho * tau * rho⁻¹ = tau := by rw [hrtau, mul_assoc, mul_inv_cancel, mul_one]
    exact htau1 (hc.fpf_QY.fix tau htauQ hconj)
  · intro hQ
    have hconj : rho * (t * tau) * rho⁻¹ = t * tau := by
      calc rho * (t * tau) * rho⁻¹ = (rho * t * rho⁻¹) * (rho * tau * rho⁻¹) := by group
        _ = t * tau := by
            rw [show rho * t * rho⁻¹ = t by rw [hrt, mul_assoc, mul_inv_cancel, mul_one],
              show rho * tau * rho⁻¹ = tau by rw [hrtau, mul_assoc, mul_inv_cancel, mul_one]]
    have h1 : t * tau = 1 := hc.fpf_QY.fix (t * tau) hQ hconj
    exact hc.tau_not_mem (by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact (twoCore t ⊔ L).inv_mem (Subgroup.mem_sup_left hc.hyp.mem_twoCore))

theorem c13K_lemma4_12a (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    Lemma4_12aConcl t tau x₁ x₂ rho :=
  l12_a hc.toCtx11

theorem c13K_mem_R_cases (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {r : G}
    (hr : r ∈ ctxR t tau x₁ x₂) :
    ∃ q ∈ ctxQ t tau x₁ x₂ rho, r = q ∨ r = t * q ∨ r = tau * q ∨ r = t * tau * q := by
  obtain ⟨ht2, -, -, htau2, -, httau, -, -⟩ := c13K_rel hc
  obtain ⟨htM, htauM, -, -, -⟩ := c13K_mem_M hc
  have hR : ctxR t tau x₁ x₂ = ctxQ t tau x₁ x₂ rho ⊔ closure {t, tau} :=
    (c13K_lemma4_12a hc).2.2.2.2.1
  rw [hR] at hr
  have hBleM : closure ({t, tau} : Set G) ≤ ctxM t tau x₁ x₂ := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact htM
    · exact htauM
  have hnorm : ∀ k ∈ closure ({t, tau} : Set G), ∀ h ∈ ctxQ t tau x₁ x₂ rho,
      k * h * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
    intro k hk h hh
    exact hc.normal_Q.2 k (hBleM hk) h hh
  obtain ⟨q, hq, k, hk, hqk⟩ := (mem_sup_iff_of_normalizes hnorm).mp hr
  have ht2' : t * t = 1 := by simpa [pow_two] using ht2
  have htau2' : tau * tau = 1 := by simpa [pow_two] using htau2
  obtain hk1 | hkt | hktau | hktt := c13K_mem_closure_pair ht2' htau2' httau hk
  · exact ⟨q, hq, Or.inl (by rw [hqk, hk1, mul_one])⟩
  · refine ⟨t⁻¹ * q * t,
      by simpa using hc.normal_Q.2 t⁻¹ ((ctxM t tau x₁ x₂).inv_mem htM) q hq, ?_⟩
    right; left
    rw [hqk, hkt]; group
  · refine ⟨tau⁻¹ * q * tau,
      by simpa using hc.normal_Q.2 tau⁻¹ ((ctxM t tau x₁ x₂).inv_mem htauM) q hq, ?_⟩
    right; right; left
    rw [hqk, hktau]; group
  · refine ⟨(t * tau)⁻¹ * q * (t * tau),
      by simpa using
        hc.normal_Q.2 (t * tau)⁻¹ ((ctxM t tau x₁ x₂).inv_mem (mul_mem htM htauM)) q hq, ?_⟩
    right; right; right
    rw [hqk, hktt]; group

theorem c13K_mem_Tp_iff (hc : Ctx13M t L S x₁ x₂ lam rho tau om) (s : G) :
    s ∈ c13KTp t tau x₁ x₂ rho ↔
      (∃ c ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G), s = t * c) ∨
      (∃ d ∈ baseGrp x₁ x₂, s = t * tau * d) := by
  obtain ⟨ht2, ht1, -, htau2, htau1, httau, -, htom⟩ := c13K_rel hc
  have ht2' : t * t = 1 := by simpa [pow_two] using ht2
  have htau2' : tau * tau = 1 := by simpa [pow_two] using htau2
  have hbase : ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) = baseGrp x₁ x₂ :=
    (c13K_lemma4_12a hc).2.2.1
  have hx2 : (t * tau) * (t * tau) = 1 := c13K_ttau_sq hc
  have hxinv : (t * tau)⁻¹ = t * tau := inv_eq_of_mul_eq_one_right hx2
  constructor
  · intro hs
    rw [c13KTp, Set.mem_union] at hs
    rcases hs with hs | hs
    · obtain ⟨hsQ, hs2, hs1⟩ := hs
      obtain ⟨q, hq, hqs⟩ := Set.mem_smul_set.mp hsQ
      rw [smul_eq_mul] at hqs
      have hsq : s = t * q := hqs.symm
      have h2 : (t * q * t) * q = 1 := by
        have h := hs2
        rw [hsq, pow_two] at h
        simpa [mul_assoc] using h
      have hinv : t * q * t = q⁻¹ := eq_inv_of_mul_eq_one_left h2
      have hconj : (t * tau) * q * (t * tau)⁻¹ = q := by
        calc (t * tau) * q * (t * tau)⁻¹
            = t * (tau * q * tau⁻¹) * t⁻¹ := by group
          _ = t * q⁻¹ * t⁻¹ := by rw [hc.tau_inv_Q q hq]
          _ = (t * q * t)⁻¹ := by
              rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right ht2']
              group
          _ = (q⁻¹)⁻¹ := by rw [hinv]
          _ = q := inv_inv q
      have hcomm : (t * tau) * q = q * (t * tau) := by
        calc (t * tau) * q = ((t * tau) * q * (t * tau)⁻¹) * (t * tau) := by group
          _ = q * (t * tau) := by rw [hconj]
      exact Or.inl ⟨q, Subgroup.mem_inf.mpr ⟨hq,
        Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩, hsq⟩
    · obtain ⟨hsQ, hs2, hs1⟩ := hs
      obtain ⟨q, hq, hqs⟩ := Set.mem_smul_set.mp hsQ
      rw [smul_eq_mul] at hqs
      have hsq : s = (t * tau) * q := hqs.symm
      have h2 : ((t * tau) * q * (t * tau)) * q = 1 := by
        have h := hs2
        rw [hsq, pow_two] at h
        simpa [mul_assoc] using h
      have h3 : (t * tau) * q * (t * tau) = q⁻¹ := eq_inv_of_mul_eq_one_left h2
      have h4 : (t * tau) * q * (t * tau)⁻¹ = q⁻¹ := by rw [hxinv]; exact h3
      have h6 : t * q⁻¹ * t⁻¹ = q⁻¹ := by
        calc t * q⁻¹ * t⁻¹ = t * (tau * q * tau⁻¹) * t⁻¹ := by rw [hc.tau_inv_Q q hq]
          _ = (t * tau) * q * (t * tau)⁻¹ := by group
          _ = q⁻¹ := h4
      have h5 : t * q⁻¹ * t = q⁻¹ := by
        rwa [show t⁻¹ = t from inv_eq_of_mul_eq_one_right ht2'] at h6
      have h7 : t * q * t = q := by
        have h8 := congrArg Inv.inv h5
        have h8' : t * (q * t) = q := by
          simpa [mul_inv_rev, inv_inv, inv_eq_of_mul_eq_one_right ht2'] using h8
        simpa [mul_assoc] using h8'
      have hcomm : q * t = t * q := by
        calc q * t = (t * q * t) * t := by rw [h7]
          _ = t * q := by rw [mul_assoc, mul_assoc, ht2', mul_one]
      have hmem : q ∈ baseGrp x₁ x₂ := by
        rw [← hbase]
        exact Subgroup.mem_inf.mpr ⟨hq, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
      exact Or.inr ⟨q, hmem, hsq⟩
  · rintro (⟨c, hcC, rfl⟩ | ⟨d, hdD, rfl⟩)
    · rw [c13KTp]
      have hcQ : c ∈ ctxQ t tau x₁ x₂ rho := (Subgroup.mem_inf.mp hcC).1
      have hcCent : c ∈ centralizer ({t * tau} : Set G) := (Subgroup.mem_inf.mp hcC).2
      refine Or.inl ⟨?_, ?_, ?_⟩
      · rw [Set.mem_smul_set]; exact ⟨c, hcQ, by rw [smul_eq_mul]⟩
      · have hccomm : c * (t * tau) = (t * tau) * c :=
          Subgroup.mem_centralizer_singleton_iff.mp hcCent
        have htc : t * c * t = c⁻¹ := by
          have h1 : tau * c = t * c * t * tau := by
            calc tau * c = (t * t) * (tau * c) := by rw [ht2', one_mul]
              _ = t * (t * tau * c) := by group
              _ = t * (c * (t * tau)) := by rw [← hccomm]
              _ = t * c * t * tau := by group
          have h2 : tau * c * tau = t * c * t * (tau * tau) := by
            calc tau * c * tau = (tau * c) * tau := by group
              _ = (t * c * t * tau) * tau := by rw [h1]
              _ = t * c * t * (tau * tau) := by group
          have h3 : tau * c * tau = t * c * t := by rw [htau2', mul_one] at h2; exact h2
          rw [← h3]
          calc tau * c * tau = tau * c * tau⁻¹ := by
                rw [show tau⁻¹ = tau from inv_eq_of_mul_eq_one_right htau2']
            _ = c⁻¹ := hc.tau_inv_Q c hcQ
        rw [pow_two]
        calc (t * c) * (t * c) = (t * c * t) * c := by group
          _ = c⁻¹ * c := by rw [htc]
          _ = 1 := inv_mul_cancel c
      · intro h1
        refine (c13K_not_mem_Q hc).1 ?_
        have ht_eq : t = c⁻¹ := eq_inv_of_mul_eq_one_left h1
        simpa [ht_eq] using (ctxQ t tau x₁ x₂ rho).inv_mem hcQ
    · rw [c13KTp]
      have hdQC : d ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) := by
        rw [hbase]; exact hdD
      have hdQ : d ∈ ctxQ t tau x₁ x₂ rho := (Subgroup.mem_inf.mp hdQC).1
      have hdC : d * t = t * d :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hdQC).2
      refine Or.inr ⟨?_, ?_, ?_⟩
      · rw [Set.mem_smul_set]; exact ⟨d, hdQ, by rw [smul_eq_mul]⟩
      · have htdt : t * d * t = d := by
          calc t * d * t = (d * t) * t := by rw [← hdC]
            _ = d := by rw [mul_assoc, ht2', mul_one]
        have hxc : (t * tau) * d * (t * tau)⁻¹ = d⁻¹ := by
          calc (t * tau) * d * (t * tau)⁻¹ = t * (tau * d * tau⁻¹) * t⁻¹ := by group
            _ = t * d⁻¹ * t⁻¹ := by rw [hc.tau_inv_Q d hdQ]
            _ = d⁻¹ := by
              calc t * d⁻¹ * t⁻¹ = (t * d * t)⁻¹ := by
                    rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right ht2']
                    group
                _ = d⁻¹ := by rw [htdt]
        rw [pow_two]
        calc ((t * tau) * d) * ((t * tau) * d)
            = ((t * tau) * d * (t * tau)⁻¹) * d := by rw [hxinv]; group
          _ = d⁻¹ * d := by rw [hxc]
          _ = 1 := inv_mul_cancel d
      · intro h1
        exact (c13K_not_mem_Q hc).2.2 (by
          rw [eq_inv_of_mul_eq_one_left h1]
          exact (ctxQ t tau x₁ x₂ rho).inv_mem hdQ)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
