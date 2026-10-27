module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB3I
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB3G

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t q tau lam rho u : G} {Z E X W R T : Subgroup G}

private lemma fzbs_3j_y_mem (hS : FzbsStr t q tau lam rho u Z E X W R T) {r₃ y : G}
    (hy : y = 1 ∨ y = r₃ ∨ y = rho * r₃ * rho⁻¹ ∨ y = rho ^ 2 * r₃ * (rho ^ 2)⁻¹)
    (hr₃ : r₃ ∈ ⁅R, zpowers rho⁆) : y ∈ ⁅R, zpowers rho⁆ := by
  rcases hy with h | h | h | h
  · rw [h]; exact one_mem _
  · rw [h]; exact hr₃
  · rw [h]; exact fzbs_P_rho hS hr₃
  · rw [h]
    have hh : rho ^ 2 * r₃ * (rho ^ 2)⁻¹ = rho * (rho * r₃ * rho⁻¹) * rho⁻¹ := by
      simp only [pow_two, mul_inv_rev]; group
    rw [hh]
    exact fzbs_P_rho hS (fzbs_P_rho hS hr₃)

private lemma fzbs_3j_conj_of_comm {s r x : G} (hsr : s * r = r * s)
    (hsx : s * x * s⁻¹ = x) : s * (r * x * r⁻¹) * s⁻¹ = r * x * r⁻¹ := by
  have hsrinv : r⁻¹ * s⁻¹ = s⁻¹ * r⁻¹ := by
    have h := congrArg Inv.inv hsr
    simpa [mul_inv_rev] using h
  calc s * (r * x * r⁻¹) * s⁻¹
      = (s * r) * x * (r⁻¹ * s⁻¹) := by group
    _ = (r * s) * x * (s⁻¹ * r⁻¹) := by rw [hsr, hsrinv]
    _ = r * (s * x * s⁻¹) * r⁻¹ := by group
    _ = r * x * r⁻¹ := by rw [hsx]

private lemma fzbs_3j_s_inv_X (hS : FzbsStr t q tau lam rho u Z E X W R T) {s m : G}
    (hs : s = tau ∨ s = q * tau) (hm : m ∈ X) : s * m * s⁻¹ = m⁻¹ := by
  rcases hs with rfl | rfl
  · exact hS.tau_X m hm
  · calc (q * tau) * m * (q * tau)⁻¹
        = q * (tau * m * tau⁻¹) * q⁻¹ := by group
      _ = q * m⁻¹ * q⁻¹ := by rw [hS.tau_X m hm]
      _ = m⁻¹ := by
            rw [hS.W_comm q hS.q_mem m⁻¹ (Subgroup.inv_mem _ (hS.XW hm))]
            group

theorem fzbs_s_comm (hS : FzbsStr t q tau lam rho u Z E X W R T) {s r₃ : G}
    (hs : s = tau ∨ s = q * tau) (hr₃ : r₃ ∈ ⁅R, zpowers rho⁆)
    (hr₃t : r₃ * t * r₃⁻¹ = t * u ^ 2) (hr₃s : s * r₃ * s⁻¹ = r₃) {p : G}
    (hp : p ∈ ⁅R, zpowers rho⁆) : ⁅s, p⁆ ∈ Z := by
  obtain ⟨y, m, hy, hmX, _, hpm⟩ := fzbs_P_decomp hS hr₃ hr₃t hp
  have hyP : y ∈ ⁅R, zpowers rho⁆ := fzbs_3j_y_mem hS hy hr₃
  have hyR : y ∈ R := fzbs_P_le_R hS hyP
  have hsr : s * rho = rho * s := by
    rcases hs with rfl | rfl
    · exact hS.tau_rho
    · have hrq : rho * q = q * rho := by
        calc rho * q = (rho * q * rho⁻¹) * rho := by group
          _ = q * rho := by rw [hS.rho_q]
      calc (q * tau) * rho = q * (tau * rho) := by group
        _ = q * (rho * tau) := by rw [hS.tau_rho]
        _ = (q * rho) * tau := by group
        _ = (rho * q) * tau := by rw [hrq]
        _ = rho * (q * tau) := by group
  have hy_comm : s * y * s⁻¹ = y := by
    rcases hy with h | h | h | h
    · rw [h]; group
    · rw [h]; exact hr₃s
    · rw [h]; exact fzbs_3j_conj_of_comm hsr hr₃s
    · rw [h]
      have hsr2 : s * rho ^ 2 = rho ^ 2 * s := by
        rw [pow_two]
        calc s * (rho * rho) = (s * rho) * rho := by group
          _ = (rho * s) * rho := by rw [hsr]
          _ = rho * (s * rho) := by group
          _ = rho * (rho * s) := by rw [hsr]
          _ = (rho * rho) * s := by group
      exact fzbs_3j_conj_of_comm hsr2 hr₃s
  have hm_inv : s * m * s⁻¹ = m⁻¹ := fzbs_3j_s_inv_X hS hs hmX
  have hm2Z : m ^ 2 ∈ Z := (hS.X_iff m (hS.XW hmX)).mp hmX
  have hcomm : ⁅s, p⁆ = y * (m ^ 2)⁻¹ * y⁻¹ := by
    rw [commutatorElement_def, hpm]
    calc s * (y * m) * s⁻¹ * (y * m)⁻¹
        = (s * y * s⁻¹) * (s * m * s⁻¹) * (m⁻¹ * y⁻¹) := by group
      _ = y * m⁻¹ * (m⁻¹ * y⁻¹) := by rw [hy_comm, hm_inv]
      _ = y * (m⁻¹ * m⁻¹) * y⁻¹ := by group
      _ = y * (m ^ 2)⁻¹ * y⁻¹ := by
            rw [show (m ^ 2)⁻¹ = m⁻¹ * m⁻¹ by rw [pow_two, mul_inv_rev]]
  rw [hcomm, hS.R_Z y hyR (m ^ 2)⁻¹ (Z.inv_mem hm2Z)]
  exact Z.inv_mem hm2Z

theorem fzbs_cent_R_rho (hS : FzbsStr t q tau lam rho u Z E X W R T) {s : G}
    (hs : s = tau ∨ s = q * tau) {c : G} (hc : c ∈ R) (hcr : rho * c * rho⁻¹ = c) :
    c ∈ closure {q, s} := by
  have hq_mem : q ∈ closure ({q, s} : Set G) := Subgroup.subset_closure (by simp)
  have hs_mem : s ∈ closure ({q, s} : Set G) := Subgroup.subset_closure (by simp)
  have htau_mem : tau ∈ closure ({q, s} : Set G) := by
    rcases hs with rfl | rfl
    · exact hs_mem
    · have hmem : q⁻¹ * (q * tau) ∈ closure ({q, q * tau} : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hq_mem) hs_mem
      have h : tau = q⁻¹ * (q * tau) := by group
      rw [← h] at hmem
      exact hmem
  have hzZ : t * (c * t * c⁻¹) ∈ Z := hS.R_t c hc
  have hz_fix : rho * (t * (c * t * c⁻¹)) * rho⁻¹ = t * (c * t * c⁻¹) := by
    have h := fzbs_chi_conj (g := rho) (r := c) hS.rho_t
    rw [hcr] at h
    exact h.symm
  have hz1 : t * (c * t * c⁻¹) = 1 := by
    by_contra hne
    exact (hS.rho_Z_fpf _ hzZ hne) hz_fix
  have hct : c * t * c⁻¹ = t := by
    have h := congrArg (fun x => t * x) hz1
    rw [mul_one] at h
    rw [← mul_assoc, ← pow_two, hS.t_sq, one_mul] at h
    exact h
  rcases hS.R_fix_t c hc hct with hcW | hcW
  · exact (Subgroup.zpowers_le.mpr hq_mem) (hS.rho_W_fix c hcW hcr)
  · have hw_fix : rho * (c * tau⁻¹) * rho⁻¹ = c * tau⁻¹ := by
      calc rho * (c * tau⁻¹) * rho⁻¹
          = (rho * c * rho⁻¹) * (rho * tau * rho⁻¹)⁻¹ := by group
        _ = c * (rho * tau * rho⁻¹)⁻¹ := by rw [hcr]
        _ = c * tau⁻¹ := by
              have hrt : rho * tau * rho⁻¹ = tau := by
                calc rho * tau * rho⁻¹ = (rho * tau) * rho⁻¹ := by group
                  _ = (tau * rho) * rho⁻¹ := by rw [← hS.tau_rho]
                  _ = tau := by group
              rw [hrt]
    have hw_mem : c * tau⁻¹ ∈ closure ({q, s} : Set G) :=
      (Subgroup.zpowers_le.mpr hq_mem) (hS.rho_W_fix (c * tau⁻¹) hcW hw_fix)
    rw [show c = (c * tau⁻¹) * tau by group]
    exact Subgroup.mul_mem _ hw_mem htau_mem

theorem fzbs_gen (hS : FzbsStr t q tau lam rho u Z E X W R T) {s : G}
    (hs : s = tau ∨ s = q * tau) : T = ⁅R, zpowers rho⁆ ⊔ closure {q, s, lam} := by
  have hsub : ({q, s} : Set G) ⊆ {q, s, lam} := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  refine le_antisymm ?_ ?_
  · intro g hg
    rcases hS.T_cases g hg with hgR | hgR
    · obtain ⟨c, hcR, hc_fix, hcm⟩ :=
        fzl_coprime_decomp hS.pgroup_R hS.rho_cube hS.rho_R hgR
      have hc_mem : c ∈ closure ({q, s, lam} : Set G) :=
        Subgroup.closure_mono hsub (fzbs_cent_R_rho hS hs hcR hc_fix)
      rw [show g = c * (c⁻¹ * g) by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc_mem) (Subgroup.mem_sup_left hcm)
    · obtain ⟨c, hcR, hc_fix, hcm⟩ :=
        fzl_coprime_decomp hS.pgroup_R hS.rho_cube hS.rho_R hgR
      have hc_mem : c ∈ closure ({q, s, lam} : Set G) :=
        Subgroup.closure_mono hsub (fzbs_cent_R_rho hS hs hcR hc_fix)
      have hlam_mem : lam ∈ closure ({q, s, lam} : Set G) :=
        Subgroup.subset_closure (by simp)
      have hlc_mem : lam⁻¹ * c ∈ closure ({q, s, lam} : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hlam_mem) hc_mem
      rw [show g = (lam⁻¹ * c) * (c⁻¹ * (lam * g)) by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hlc_mem) (Subgroup.mem_sup_left hcm)
  · refine sup_le ((fzbs_P_le_R hS).trans hS.RT) ?_
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hS.RT (hS.WR hS.q_mem)
    · rcases hs with rfl | rfl
      · exact hS.RT hS.tau_R
      · exact hS.RT (R.mul_mem (hS.WR hS.q_mem) hS.tau_R)
    · exact hS.lam_T

theorem fzbs_out (hS : FzbsStr t q tau lam rho u Z E X W R T) :
    ∃ (P : Subgroup G) (s : G), FzbsOut t q tau lam rho Z E T P s := by
  obtain ⟨s, r₃, hs, hr₃, hr₃t, hr₃l, hr₃s⟩ := fzbs_r3 hS
  have hsq : ∀ p ∈ ⁅R, zpowers rho⁆, p ^ 2 ∈ E := fun p hp =>
    fzbs_P_sq hS hr₃ hr₃t (fzbs_r3_sq hS hs hr₃ hr₃t hr₃l hr₃s) hp
  have htP := fzbs_t_notin_P hS hsq
  exact ⟨⁅R, zpowers rho⁆, s,
    { P_le := (fzbs_P_le_R hS).trans hS.RT
      P_norm := fun g hg p hp => fzbs_P_T hS hg hp
      card_P := fzbs_card_P hS htP
      P_iso := fzbs_P_iso hS htP
      E_le_P := fzbs_E_le_P hS
      rho_norm := fun p hp => fzbs_P_rho hS hp
      rho_fpf := fun p hp hfix => fzbs_P_fpf hS htP hp hfix
      cent_t := fzbs_P_cent_t hS htP
      s_cases := hs
      s_comm_P := fun p hp => fzbs_s_comm hS hs hr₃ hr₃t hr₃s hp
      gen := fzbs_gen hS hs }⟩

end CFSG.OddStandard.SmallF3.FritzII
