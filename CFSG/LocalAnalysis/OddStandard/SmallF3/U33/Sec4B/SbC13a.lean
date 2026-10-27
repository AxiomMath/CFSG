module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARem
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0i

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem ctx8e_of_ctx11 (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    Ctx8e t L S x₁ x₂ lam rho tau := by
  have c8 : Ctx8 t L S x₁ x₂ lam rho tau := { toCtx10 := hc.toCtx10, tM := hc.tM }
  have c8a : Ctx8a t L S x₁ x₂ lam rho tau :=
    { toCtx8 := c8, card_M := hc.card_M, normal_N := hc.normal_N, normal_V := hc.normal_V }
  have c8b : Ctx8b t L S x₁ x₂ lam rho tau :=
    { toCtx8a := c8a, O_eq_C := p0_O_eq_C c8a, card_O := hc.card_O,
      lam_not_mem_O := p0_lam_not_mem_O c8a }
  have c8c : Ctx8c t L S x₁ x₂ lam rho tau :=
    { toCtx8b := c8b, M_eq := hc.M_eq, S_le_U := hc.S_le_U, U_sylow := hc.U_sylow }
  have c8d : Ctx8d t L S x₁ x₂ lam rho tau :=
    { toCtx8c := c8c, X_le_R := hc.X_le_R, R_le_O := hc.R_le_O, card_R := hc.card_R,
      normal_R := hc.normal_R, R_quot := hc.R_quot, coset := p0_coset c8c }
  exact
    { toCtx8d := c8d, CR_rho := hc.CR_rho, tR := hc.tR, ttauR := hc.ttauR, tauR := hc.tauR,
      tM_O := hc.tM_O, tauM := hc.tauM, tauO := hc.tauO }

theorem c13_O_cent (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    ctxO t tau x₁ x₂ =
      ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
  (ctx8e_of_ctx11 hc).O_eq_C

private lemma c13_T_le_R (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    closure {t, tau} ≤ ctxR t tau x₁ x₂ := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact hc.X_le_R (Subgroup.subset_closure (by simp))
  · exact hc.X_le_R (Subgroup.subset_closure (by simp))

private lemma c13_t_mem_CO (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    t ∈ ctxCO t tau x₁ x₂ rho := by
  refine ⟨?_, ?_⟩
  · exact hc.R_le_O (hc.X_le_R (Subgroup.subset_closure (by simp)))
  · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    exact (S4A.mem_invCent_iff.mp (S4A.L_le_invCent hc.hyp hc.rho_mem)).symm

theorem c13_exists_om (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    ∃ om : G, om ∈ ctxCO t tau x₁ x₂ rho ∧ om * om = 1 ∧ om ∉ closure {t, tau} ∧
      om * t * om⁻¹ = t * tau := by
  obtain ⟨g, hgCO, hgR, hgt, -, hg2, -⟩ := p0_CO_outer (ctx8e_of_ctx11 hc)
  have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
  have hτ2 : tau * tau = 1 := by simpa [pow_two] using hc.l44.1
  have hTleR := c13_T_le_R hc
  rcases hg2 with hg2 | hg2
  · refine ⟨g, hgCO, ?_, ?_, hgt⟩
    · simpa [pow_two] using hg2
    · exact fun h => hgR (hTleR h)
  · refine ⟨g * t, mul_mem hgCO (c13_t_mem_CO hc), ?_, ?_, ?_⟩
    · have hg2' : g * g = tau := by simpa [pow_two] using hg2
      have h1 : (g * t) * (g * t) = (g * t * g⁻¹) * (g * g) * t := by group
      rw [h1, hgt, hg2']
      rw [mul_assoc t tau tau, hτ2, mul_one, ht2]
    · intro hmem
      apply hgR
      apply hTleR
      have htinv : t⁻¹ ∈ closure {t, tau} :=
        (closure {t, tau}).inv_mem (Subgroup.subset_closure (by simp))
      have h2 := (closure {t, tau}).mul_mem hmem htinv
      simpa using h2
    · have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
      calc (g * t) * t * (g * t)⁻¹
          = g * t * t * (t⁻¹ * g⁻¹) := by rw [mul_inv_rev]
        _ = g * (t * t) * (t⁻¹ * g⁻¹) := by group
        _ = g * t * g⁻¹ := by rw [ht2, htinv]; group
        _ = t * tau := hgt

theorem c13_CO_eq (hc : Ctx11 t L S x₁ x₂ lam rho tau) {om : G}
    (hmem : om ∈ ctxCO t tau x₁ x₂ rho) (hsq : om * om = 1) (hnot : om ∉ closure {t, tau})
    (hto : om * t * om⁻¹ = t * tau) : ctxCO t tau x₁ x₂ rho = closure {t, om} := by
  have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
  have htCO := c13_t_mem_CO hc
  have hE_CO : closure {t, om} ≤ ctxCO t tau x₁ x₂ rho := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact htCO
    · exact hmem
  have htauE : tau ∈ closure {t, om} := by
    have h1 : t * (om * t * om⁻¹) ∈ closure {t, om} :=
      (closure {t, om}).mul_mem (Subgroup.subset_closure (by simp))
        ((closure {t, om}).mul_mem
          ((closure {t, om}).mul_mem (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp)))
          ((closure {t, om}).inv_mem (Subgroup.subset_closure (by simp))))
    have heq : t * (om * t * om⁻¹) = tau := by
      rw [hto, ← mul_assoc, ht2, one_mul]
    rwa [heq] at h1
  have hT_E : closure {t, tau} ≤ closure {t, om} := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact htauE
  have hT4 : Nat.card ↥(closure {t, tau}) = 4 :=
    (Ctx4.centralizer_t_tau hc.toCtx10.toCtx4).2.2.1
  have homE : om ∈ closure {t, om} := Subgroup.subset_closure (by simp)
  have hne : closure {t, tau} ≠ closure {t, om} :=
    fun h => hnot (h.symm ▸ homE)
  have hCO8 : Nat.card ↥(ctxCO t tau x₁ x₂ rho) = 8 := by
    obtain ⟨e⟩ := hc.CO_dihedral
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hE8 : Nat.card ↥(closure {t, om}) = 8 := by
    have hnpos : 0 < Nat.card ↥(closure {t, om}) := Nat.card_pos
    have hdvdE : Nat.card ↥(closure {t, om}) ∣ 8 := by
      have h := Subgroup.card_dvd_of_le hE_CO
      rwa [hCO8] at h
    have hdvd4 : 4 ∣ Nat.card ↥(closure {t, om}) := by
      have h := Subgroup.card_dvd_of_le hT_E
      rwa [hT4] at h
    have hne4 : Nat.card ↥(closure {t, om}) ≠ 4 := by
      intro h4
      exact hne (Subgroup.eq_of_le_of_card_ge hT_E (by rw [h4, hT4]))
    obtain ⟨k, hk⟩ := hdvd4
    have hk_le : k ≤ 2 := by
      have h : 4 * k ∣ 8 := hk ▸ hdvdE
      have := Nat.le_of_dvd (by norm_num) h
      omega
    have hk_cases : k = 1 ∨ k = 2 := by omega
    rcases hk_cases with rfl | rfl
    · omega
    · omega
  have hcard : Nat.card ↥(ctxCO t tau x₁ x₂ rho) ≤ Nat.card ↥(closure {t, om}) := by
    omega
  exact (Subgroup.eq_of_le_of_card_ge hE_CO hcard).symm

theorem ctx13a_exists (hc : Ctx11 t L S x₁ x₂ lam rho tau)
    (hq : IsZ4Z4E4 (ctxQ t tau x₁ x₂ rho)) :
    ∃ om : G, Ctx13A t L S x₁ x₂ lam rho tau om := by
  obtain ⟨om, hmem, hsq, hnot, hto⟩ := c13_exists_om hc
  refine ⟨om, ?_⟩
  exact
    { toCtx11 := hc, q_iso := hq, om_mem := hmem, om_sq := hsq, om_not_mem := hnot,
      t_om := hto, CO_eq := c13_CO_eq hc hmem hsq hnot hto, O_cent := c13_O_cent hc }

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
