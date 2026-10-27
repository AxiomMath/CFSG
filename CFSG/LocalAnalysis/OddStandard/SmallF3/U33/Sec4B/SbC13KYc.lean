module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13KUc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13KChar
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0f1c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma c13K_sq_w_ne_one (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    (x₁ * x₂) ^ 2 ≠ 1 := by
  obtain ⟨V', v₁, v₂, hV⟩ := hc.data_V
  obtain ⟨-, -, hQsplit, hinf, -, -, -, -, hv1_mem, hv1_ne, ht_v1, -⟩ := hV
  intro hz
  have hv1Q : v₁ ∈ ctxQ t tau x₁ x₂ rho :=
    hQsplit ▸ Subgroup.mem_sup_right hv1_mem
  have ht_fix : t * v₁ * t⁻¹ = v₁ := by rw [ht_v1, hz, mul_one]
  have ht_comm : v₁ * t = t * v₁ := by
    have h := ht_fix
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hv1base : v₁ ∈ baseGrp x₁ x₂ := by
    have hmem : v₁ ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hv1Q, Subgroup.mem_centralizer_singleton_iff.mpr ht_comm⟩
    rwa [(c13K_lemma4_12a hc).2.2.1] at hmem
  have hv1bot : v₁ ∈ (⊥ : Subgroup G) := by
    have h : v₁ ∈ baseGrp x₁ x₂ ⊓ V' := Subgroup.mem_inf.mpr ⟨hv1base, hv1_mem⟩
    rwa [hinf] at h
  exact hv1_ne (Subgroup.mem_bot.mp hv1bot)

private lemma c13K_s_eq_one (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {s : G}
    (hs : s ∈ closure ({tau, om} : Set G))
    (hsw : s * (x₁ * x₂) = (x₁ * x₂) * s) : s = 1 := by
  have hwQ : x₁ * x₂ ∈ ctxQ t tau x₁ x₂ rho :=
    (ctxQ t tau x₁ x₂ rho).mul_mem
      (hc.base_le_Q (Subgroup.subset_closure (by simp)))
      (hc.base_le_Q (Subgroup.subset_closure (by simp)))
  have htau2 : tau * tau = 1 := by simpa [pow_two] using (c13K_rel hc).2.2.2.1
  have hom2 : om * om = 1 := by simpa [pow_two] using (c13K_rel hc).2.2.1
  have htauom : tau * om = om * tau := (c13K_rel hc).2.2.2.2.2.2.1
  have hz := c13K_sq_w_ne_one hc
  rcases c13K_mem_closure_pair htau2 hom2 htauom hs with h | h | h | h
  · exact h
  · exfalso
    apply hz
    have hcomm : tau * (x₁ * x₂) = (x₁ * x₂) * tau := by
      rw [h] at hsw
      exact hsw
    have hinv : tau * (x₁ * x₂) * tau⁻¹ = (x₁ * x₂)⁻¹ := hc.tau_inv_Q _ hwQ
    have hw_eq : (x₁ * x₂) = (x₁ * x₂)⁻¹ := by
      rw [← hinv, hcomm]
      group
    have hw2 : (x₁ * x₂) ^ 2 = 1 := by
      rw [pow_two]
      exact mul_eq_one_iff_inv_eq.mpr hw_eq.symm
    exact hw2
  · exfalso
    apply hz
    have hcomm : om * (x₁ * x₂) = (x₁ * x₂) * om := by
      rw [h] at hsw
      exact hsw
    have hmem : x₁ * x₂ ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({om} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hwQ, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    rw [hc.Q_om.2.2.2.1] at hmem
    exact ((mem_ctxYq_iff hc.q_iso _).mp hmem).2
  · exfalso
    apply hz
    have hcomm : (tau * om) * (x₁ * x₂) = (x₁ * x₂) * (tau * om) := by
      rw [h] at hsw
      exact hsw
    have hmem : x₁ * x₂ ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({tau * om} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hwQ, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    rw [htauom] at hmem
    rw [hc.Q_omtau.2.2.2.1] at hmem
    exact ((mem_ctxYq_iff hc.q_iso _).mp hmem).2

theorem c13K_cent_U' (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    ctxU t tau x₁ x₂ lam ⊓
        centralizer ((⁅ctxU t tau x₁ x₂ lam, ctxU t tau x₁ x₂ lam⁆ : Subgroup G) : Set G) =
      ctxYq t tau x₁ x₂ rho := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgU, hgC⟩ := Subgroup.mem_inf.mp hg
    have hKnorm : ∀ k ∈ closure ({tau, om} : Set G), ∀ h ∈ ctxQ t tau x₁ x₂ rho,
        k * h * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
      fun k hk h hh => c13K_normal_Q_QQ hc k (Subgroup.mem_sup_right hk) h hh
    have hgB : g ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) := by
      rw [← c13K_B_eq_cent hc]
      refine Subgroup.mem_inf.mpr ⟨hgU, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp hgC) y ((c13K_U_comm_ge hc).2.2 hy)
    obtain ⟨q, hq, s, hs, hgs⟩ :=
      (mem_sup_iff_of_normalizes (H := ctxQ t tau x₁ x₂ rho)
        (K := closure ({tau, om} : Set G)) hKnorm).mp hgB
    have htauom : tau * om = om * tau := (c13K_rel hc).2.2.2.2.2.2.1
    have hs_tau : s * tau = tau * s := by
      have hle : closure ({tau, om} : Set G) ≤ centralizer ({tau} : Set G) := by
        refine (Subgroup.closure_le (K := centralizer ({tau} : Set G))).mpr ?_
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (by group)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr htauom.symm
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hs)
    have htauU' : tau ∈ ⁅ctxU t tau x₁ x₂ lam, ctxU t tau x₁ x₂ lam⁆ :=
      (c13K_U_comm_ge hc).1
    have hg_tau : tau * g = g * tau := (Subgroup.mem_centralizer_iff.mp hgC) tau htauU'
    have hq_tau : tau * q = q * tau := by
      have h' : (tau * q) * s = (q * tau) * s := by
        calc (tau * q) * s = tau * (q * s) := by group
          _ = tau * g := by rw [hgs]
          _ = g * tau := hg_tau
          _ = (q * s) * tau := by rw [hgs]
          _ = q * (s * tau) := by group
          _ = q * (tau * s) := by rw [hs_tau]
          _ = (q * tau) * s := by group
      exact mul_right_cancel h'
    have hq_inv : q⁻¹ = q := by
      rw [← hc.tau_inv_Q q hq]
      rw [hq_tau]
      group
    have hq2 : q ^ 2 = 1 := by
      rw [pow_two]
      exact mul_eq_one_iff_inv_eq.mpr hq_inv
    have hqY : q ∈ ctxYq t tau x₁ x₂ rho := (mem_ctxYq_iff hc.q_iso q).mpr ⟨hq, hq2⟩
    have hwU' : x₁ * x₂ ∈ ⁅ctxU t tau x₁ x₂ lam, ctxU t tau x₁ x₂ lam⁆ :=
      (c13K_U_comm_ge hc).2.1
    have hg_w : (x₁ * x₂) * g = g * (x₁ * x₂) :=
      (Subgroup.mem_centralizer_iff.mp hgC) (x₁ * x₂) hwU'
    have hq_w : q * (x₁ * x₂) = (x₁ * x₂) * q := by
      have hwB : x₁ * x₂ ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) :=
        c13K_U_comm_le hc hwU'
      have hwC : x₁ * x₂ ∈ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
        have hmem : x₁ * x₂ ∈ ctxU t tau x₁ x₂ lam ⊓
            centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
          rw [c13K_B_eq_cent hc]
          exact hwB
        exact hmem.2
      exact (Subgroup.mem_centralizer_iff.mp hwC) q hqY
    have hsw : s * (x₁ * x₂) = (x₁ * x₂) * s := by
      have h' : q * (s * (x₁ * x₂)) = q * ((x₁ * x₂) * s) := by
        calc q * (s * (x₁ * x₂)) = g * (x₁ * x₂) := by rw [hgs]; group
          _ = (x₁ * x₂) * g := hg_w.symm
          _ = (x₁ * x₂) * (q * s) := by rw [hgs]
          _ = ((x₁ * x₂) * q) * s := by group
          _ = (q * (x₁ * x₂)) * s := by rw [hq_w]
          _ = q * ((x₁ * x₂) * s) := by group
      exact mul_left_cancel h'
    have hs1 : s = 1 := c13K_s_eq_one hc hs hsw
    simpa [hgs, hs1] using hqY
  · intro y hy
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (c13K_Q_B_le_O hc).1.trans ((c13K_O_le_U_le_M hc).1) (ctxYq_le_ctxQ hy)
    · rw [Subgroup.mem_centralizer_iff]
      intro u' hu'
      have hu'C : u' ∈ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
        have hmem : u' ∈ ctxU t tau x₁ x₂ lam ⊓
            centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
          rw [c13K_B_eq_cent hc]
          exact c13K_U_comm_le hc hu'
        exact hmem.2
      exact ((Subgroup.mem_centralizer_iff.mp hu'C) y hy).symm

theorem c13K_charIn_Y_U (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    CharIn (ctxYq t tau x₁ x₂ rho) (ctxU t tau x₁ x₂ lam) := by
  have h := L34Z.charIn_inf_centralizer (c13K_charIn_commutator (ctxU t tau x₁ x₂ lam))
  rw [c13K_cent_U' hc] at h
  exact h

theorem c13K_charIn_B_U (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    CharIn (ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)) (ctxU t tau x₁ x₂ lam) := by
  have h := L34Z.charIn_inf_centralizer (c13K_charIn_Y_U hc)
  rw [c13K_B_eq_cent hc] at h
  exact h

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
