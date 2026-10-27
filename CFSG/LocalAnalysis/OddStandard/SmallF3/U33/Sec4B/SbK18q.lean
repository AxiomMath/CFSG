module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18p
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Cm

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma k18_mul_tau_mul_eq (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {q : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) :
    (t * tau) * q⁻¹ = t * (q * tau) := by
  obtain ⟨-, -, -, htau2, -, -, -⟩ := ctx13_relations hc
  have htau2' : tau * tau = 1 := by simpa [pow_two] using htau2
  have htauinv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right htau2'
  have hconj : tau * q * tau = q⁻¹ := by
    have h := hc.tau_inv_Q q hq
    rwa [htauinv] at h
  calc (t * tau) * q⁻¹
      = (t * tau) * (tau * q * tau) := by rw [← hconj]
    _ = t * (tau * tau) * q * tau := by group
    _ = t * q * tau := by rw [htau2', mul_one]
    _ = t * (q * tau) := by group

private lemma k18_not_mem_C_of_mul_eq_one (hc : Ctx13 t L S x₁ x₂ lam rho tau om)
    {e : G} (he : e ∈ ctxCY t tau x₁ x₂ rho) (h : t * e = 1) : False := by
  have ht2 : t * t = 1 := by
    simpa [pow_two] using (ctx13_relations hc).1
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have he_eq : e = t := by
    have h1 : e = t⁻¹ := eq_inv_of_mul_eq_one_right h
    rwa [htinv] at h1
  exact (l18_not_mem_C hc).1 (by simpa [he_eq] using he)

theorem k18_F3A (hc : Ctx18A t L S x₁ x₂ lam rho tau om 𝒮) {e : G}
    (he : e ∈ ctxCY t tau x₁ x₂ rho) (h2 : (t * e) * (t * e) = 1) :
    ∃ s ∈ 𝒮, t * e = s * t * s⁻¹ := by
  have hc13 := hc.toCtx13
  have hc18S := hc.toCtx18S
  obtain ⟨ht2, -, hom2, htau2, -, httau, homt⟩ := ctx13_relations hc13
  have hXK : closure ({tau, om} : Set G) ≤ ctxK t tau x₁ x₂ rho := by
    rw [Subgroup.closure_le]
    rintro a (ha : a ∈ ({tau, om} : Set G))
    rcases ha with rfl | rfl
    · exact (l17_mem_K hc13).2.1
    · exact (l17_mem_K hc13).2.2.1
  have hNorm : ∀ k ∈ closure ({tau, om} : Set G), ∀ h ∈ ctxQ t tau x₁ x₂ rho,
      k * h * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    fun k hk h hh => hc.normal_Q_K.2 k (hXK hk) h hh
  have heC : e ∈ ctxCY t tau x₁ x₂ rho := he
  rw [k18A_C_eq hc] at he
  obtain ⟨q, hq, a, ha, heq⟩ := (mem_sup_iff_of_normalizes hNorm).mp he
  have htau2' : tau * tau = 1 := by simpa [pow_two] using htau2
  have hom2' : om * om = 1 := by simpa [pow_two] using hom2
  have hcomm : tau * om = om * tau := (om_tau_comm ht2 hom2 htau2 httau homt).symm
  have ha_list := (mem_closure_pair_of_invol htau2' hom2' hcomm).mp ha
  have hmem : t * e ∈ conjIn (ctxK t tau x₁ x₂ rho) t := by
    rw [hc.tK]
    rcases ha_list with ha1 | hat | haom | haomtau
    · left
      have he1 : e = q := by rw [ha1, mul_one] at heq; exact heq
      refine ⟨?_, ?_, ?_⟩
      · refine Set.mem_smul_set.mpr ⟨q, hq, ?_⟩
        rw [smul_eq_mul, he1]
      · simpa [pow_two] using h2
      · intro hone
        exact k18_not_mem_C_of_mul_eq_one hc13 heC hone
    · right
      have he2 : e = q * tau := by rw [hat] at heq; exact heq
      refine ⟨?_, ?_, ?_⟩
      · refine Set.mem_smul_set.mpr
          ⟨q⁻¹, Subgroup.inv_mem (ctxQ t tau x₁ x₂ rho) hq, ?_⟩
        rw [smul_eq_mul, he2]
        exact k18_mul_tau_mul_eq hc13 hq
      · simpa [pow_two] using h2
      · intro hone
        exact k18_not_mem_C_of_mul_eq_one hc13 heC hone
    · exfalso
      rw [haom] at heq
      rw [heq] at h2
      exact k18_te_sq_ne hc13 hq (Or.inl rfl) h2
    · exfalso
      rw [haomtau] at heq
      rw [heq] at h2
      exact k18_te_sq_ne hc13 hq (Or.inr rfl) h2
  obtain ⟨k, hkK, hk⟩ := hmem
  obtain ⟨m, hm, hcase⟩ := k18_t_conj_decomp hc13 hkK
  have hmS : m ∈ 𝒮 := l18_Xi_le_sylow hc18S hm
  rcases hcase with hcase | hcase
  · exact ⟨m, hmS, hk.symm.trans hcase⟩
  · refine ⟨m * om, Subgroup.mul_mem 𝒮 hmS (l18_T_le_sylow hc18S).2.2.1, ?_⟩
    calc t * e = k * t * k⁻¹ := hk.symm
      _ = m * (t * tau) * m⁻¹ := hcase
      _ = m * (om * t * om⁻¹) * m⁻¹ := by rw [homt]
      _ = (m * om) * t * (m * om)⁻¹ := by group

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
