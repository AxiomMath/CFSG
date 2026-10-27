module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FMonoAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FEven

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

private lemma sec4FCore_sec4MV_pair (a b : Fin 7) :
    sec4MV (some a) + sec4MV (some b) = Pi.single a (1 : ZMod 2) + Pi.single b 1 := by
  decide +kernel +revert

private lemma sec4FCore_comm_of_cases (h : Sec4FSetup t L S z A B φ) {μ x b : G}
    (hμt : μ * t = t * μ) (hxμ : x * μ = μ * x) (hx : x = b ∨ x = b * t) :
    b * μ = μ * b := by
  rcases hx with hxb | hxbt
  · rw [← hxb]; exact hxμ
  · have hb : b = x * t := by rw [hxbt, mul_assoc, h.t_sq, mul_one]
    rw [hb]
    calc (x * t) * μ = x * (t * μ) := by group
      _ = x * (μ * t) := by rw [← hμt]
      _ = (x * μ) * t := by group
      _ = (μ * x) * t := by rw [hxμ]
      _ = μ * (x * t) := by group

private lemma sec4FCore_type_of_cases (h : Sec4FSetup t L S z A B φ) {μ x b : G}
    (h6 : InducesTypeSome L (μ * x) 7 1 6 1) (hx : x = b ∨ x = b * t) :
    InducesTypeSome L (μ * b) 7 1 6 1 := by
  rcases hx with hxb | hxbt
  · rwa [hxb] at h6
  · have h6' : InducesTypeSome L ((μ * b) * t) 7 1 6 1 := by
      rw [hxbt, ← mul_assoc] at h6
      exact h6
    exact (sec4F_type_mul_cent_iff h.omega7 h.t_mem_cent (Or.inr (Or.inr rfl))).mp h6'

theorem Sec4FSetup.fiber_core_cent (h : Sec4FSetup t L S z A B φ) {μ x : G} {i j : Fin 7}
    (hij : i ≠ j) (hμ : ∃ g : G, μ = g⁻¹ * t * g) (hμN : μ ∈ normalizer (A : Set G))
    (hμt : μ * t = t * μ) (hμr : Sec4MRealizes t φ μ (Equiv.swap (some i) (some j)))
    (hμ6 : InducesTypeSome L μ 7 1 6 1) (hxA : x ∈ A) (hxμ : x * μ = μ * x)
    (hμx : ∃ g : G, μ * x = g⁻¹ * t * g) :
    x = 1 ∨ x = sec4MPt t φ (some i) * sec4MPt t φ (some j) := by
  classical
  set pτ : G := sec4MPt t φ (some i) with hpτ
  set qτ : G := sec4MPt t φ (some j) with hqτ
  have hμ2 : orderOf μ = 2 := by
    obtain ⟨g, hg⟩ := hμ
    rw [hg, orderOf_conjugate_eq]
    exact h.ctx.involution
  have hμc : μ ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hμt
  have hμL : μ ∈ normalizer (L : Set G) := h.cent_le_normalizer hμc
  have h6μx : InducesTypeSome L (μ * x) 7 1 6 1 := by
    have hreal : Sec4MRealizes t φ (μ * x) (Equiv.swap (some i) (some j)) := by
      simpa using Sec4MRealizes.mul hμr (h.realizes_of_mem_A hxA)
    have hmuxN : μ * x ∈ normalizer (A : Set G) :=
      (normalizer (A : Set G)).mul_mem hμN (Subgroup.le_normalizer hxA)
    have hmux_t : (μ * x) * t = t * (μ * x) := by
      rw [mul_assoc, h.A_comm hxA h.t_mem_A, ← mul_assoc, hμt, mul_assoc]
    exact h.outer_of_odd hμx hmuxN hmux_t hreal (Equiv.Perm.sign_swap (by simpa using hij))
  obtain ⟨b, hbB, hxcase⟩ := h.mem_A_cases hxA
  have hbμ : μ * b = b * μ := (sec4FCore_comm_of_cases h hμt hxμ hxcase).symm
  have h6μb : InducesTypeSome L (μ * b) 7 1 6 1 := sec4FCore_type_of_cases h h6μx hxcase
  obtain ⟨v, hv, hφv⟩ := (h.data.bdata.perm.2.2.1 b).mp hbB
  have hcomm : μ * φ v = φ v * μ := by rw [hφv]; exact hbμ
  have h6φv : InducesTypeSome L (μ * φ v) 7 1 6 1 := by rw [hφv]; exact h6μb
  have hmono := h.inputs.hMono G L (S ⊓ L) B φ h.omega7 h.data.bdata μ i j hij hμ2 hμL hμ6
    (h.conj_phi_of_realizes_swap hμr) v hv hcomm h6φv
  have hb_cases : b = 1 ∨ b = pτ * qτ := by
    rcases hmono with hv0 | hvpair
    · left
      rw [← hφv, hv0]
      exact IsPermModuleVia.map_zero h.data.bdata.perm
    · right
      rw [← hφv, hvpair, ← sec4FCore_sec4MV_pair,
        ← sec4MPt_mul h.data (some i) (some j)]
  rcases hxcase with hxb | hxbt
  · rcases hb_cases with hb1 | hbpq
    · left; rw [hxb, hb1]
    · right; rw [hxb, hbpq]
  · exfalso
    have hμxt : ∃ g : G, μ * t = g⁻¹ * t * g := by
      rcases hb_cases with hb1 | hbpq
      · rw [hxbt, hb1, one_mul] at hμx
        exact hμx
      · obtain ⟨g, hg⟩ := hμx
        have hxp : x = pτ * qτ * t := by rw [hxbt, hbpq]
        have hpμ : μ * pτ = qτ * μ := by
          have h1 : μ * pτ * μ⁻¹ = qτ := by
            have h2 := hμr (some i)
            rw [Equiv.swap_apply_left] at h2
            exact h2
          rw [← h1]; group
        have hqμ : μ * qτ = pτ * μ := by
          have h1 : μ * qτ * μ⁻¹ = pτ := by
            have h2 := hμr (some j)
            rw [Equiv.swap_apply_right] at h2
            exact h2
          rw [← h1]; group
        have htp : t * pτ = pτ * t := h.A_comm h.t_mem_A (sec4MPt_mem_A h.data (some i))
        have hμxeq : μ * x = qτ * pτ * (μ * t) := by
          rw [hxp]
          calc μ * (pτ * qτ * t) = (μ * pτ) * (qτ * t) := by group
            _ = (qτ * μ) * (qτ * t) := by rw [hpμ]
            _ = qτ * (μ * qτ) * t := by group
            _ = qτ * (pτ * μ) * t := by rw [hqμ]
            _ = qτ * pτ * (μ * t) := by group
        have hpt : μ * t * pτ = qτ * μ * t := by
          calc μ * t * pτ = μ * (t * pτ) := by group
            _ = μ * (pτ * t) := by rw [htp]
            _ = (μ * pτ) * t := by group
            _ = (qτ * μ) * t := by rw [hpμ]
        have hpqp : pτ * qτ * pτ = qτ := by
          rw [h.A_comm (sec4MPt_mem_A h.data (some i)) (sec4MPt_mem_A h.data (some j))]
          calc qτ * pτ * pτ = qτ * (pτ * pτ) := by group
            _ = qτ := by rw [sec4MPt_mul_self h.data (some i), mul_one]
        have hqq : qτ * qτ = 1 := sec4MPt_mul_self h.data (some j)
        have hkey : pτ * (μ * x) * pτ = μ * t := by
          rw [hμxeq]
          calc pτ * (qτ * pτ * (μ * t)) * pτ
              = (pτ * qτ * pτ) * (μ * t * pτ) := by group
            _ = (pτ * qτ * pτ) * (qτ * μ * t) := by rw [hpt]
            _ = qτ * (qτ * μ * t) := by rw [hpqp]
            _ = μ * t := by
                rw [show qτ * (qτ * μ * t) = (qτ * qτ) * (μ * t) by group, hqq, one_mul]
        refine ⟨g * pτ, ?_⟩
        have hpτinv : pτ⁻¹ = pτ :=
          inv_eq_of_mul_eq_one_left (sec4MPt_mul_self h.data (some i))
        calc μ * t = pτ * (μ * x) * pτ := hkey.symm
          _ = pτ * (g⁻¹ * t * g) * pτ := by rw [hg]
          _ = (g * pτ)⁻¹ * t * (g * pτ) := by
              rw [mul_inv_rev, hpτinv]
              group
    exact sec4_no_triangle h.inputs.h36 h.inputs.h39 h.inputs.hk6 h.inputs.hD h.inputs.hABC
      h.ctx hμ hμxt hμc hμ6

end CFSG.OddStandard.SmallF3.Omega
