module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18f

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem k18_D_invol_cases (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {δ : G}
    (hδ : δ ∈ closure ({t, om} : Set G)) (h2 : δ * δ = 1) :
    δ = 1 ∨ δ = tau ∨ δ = om ∨ δ = tau * om ∨ δ = t ∨ δ = t * tau := by
  obtain ⟨ht2, -, hom2, htau2, htau_t, ht_tau, hom_t⟩ := ctx13_relations hc
  have htau1 : tau ≠ 1 := fun h => htau_t (h.symm ▸ Subgroup.one_mem (zpowers t))
  have homtau : om * tau = tau * om := om_tau_comm ht2 hom2 htau2 ht_tau hom_t
  rcases eq_or_ne δ 1 with h1 | hδ1
  · exact Or.inl h1
  · have h2pow : δ ^ 2 = 1 := by rw [pow_two]; exact h2
    rcases invol_closure_t_om ht2 hom2 htau2 htau1 ht_tau hom_t hδ h2pow hδ1 with
      h | h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [h, homtau]))))

theorem k18_coset_decomp (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {e : G}
    (he : e ∈ ctxOK t tau x₁ x₂ rho) :
    ∃ ξ ∈ ctxXi t tau x₁ x₂ rho, ∃ δ ∈ closure ({t, om} : Set G),
      e * (lam * t) = ξ * (lam * δ) := by
  have hXinorm : ∀ g ∈ closure ({t, om} : Set G), ∀ x ∈ ctxXi t tau x₁ x₂ rho,
      g * x * g⁻¹ ∈ ctxXi t tau x₁ x₂ rho := by
    intro g hg x hx
    have hgK : g ∈ ctxK t tau x₁ x₂ rho := by
      have hKmem := l17_mem_K hc
      have hle : closure ({t, om} : Set G) ≤ ctxK t tau x₁ x₂ rho :=
        (Subgroup.closure_le _).mpr (by
          intro y hy
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl
          · exact hKmem.1
          · exact hKmem.2.2.1)
      exact hle hg
    exact (l18_Xi_normal hc).2 g hgK x hx
  have he' : e ∈ ctxXi t tau x₁ x₂ rho ⊔ closure ({t, om} : Set G) := by
    rw [← k18_OK_eq_Xi_tom hc]
    exact he
  obtain ⟨ξ, hξ, d, hd, heq⟩ := (mem_sup_iff_of_normalizes hXinorm).mp he'
  refine ⟨ξ, hξ, d * t, ?_, ?_⟩
  · exact (closure ({t, om} : Set G)).mul_mem hd (Subgroup.subset_closure (by simp))
  · have hcomm : d * lam = lam * d := (ctx13_lam_facts hc).2 d hd
    rw [heq]
    calc (ξ * d) * (lam * t) = ξ * (d * lam) * t := by group
      _ = ξ * (lam * d) * t := by rw [hcomm]
      _ = ξ * (lam * (d * t)) := by group

theorem k18_sq_cond (hc : Ctx18 t L S x₁ x₂ lam rho tau om 𝒮) {ξ δ : G}
    (hξ : ξ ∈ ctxXi t tau x₁ x₂ rho) (hδ : δ ∈ closure ({t, om} : Set G))
    (h2 : (ξ * (lam * δ)) * (ξ * (lam * δ)) = 1) : δ * δ = 1 := by
  have hc13 : Ctx13 t L S x₁ x₂ lam rho tau om := hc.toCtx13
  obtain ⟨hlam2pow, hlam_comm⟩ := ctx13_lam_facts hc13
  have hlam2 : lam * lam = 1 := by rw [pow_two] at hlam2pow; exact hlam2pow
  have hcommD : δ * lam = lam * δ := hlam_comm δ hδ
  have htK := l17_mem_K hc13
  have hδK : δ ∈ ctxK t tau x₁ x₂ rho := by
    have hle : closure ({t, om} : Set G) ≤ ctxK t tau x₁ x₂ rho :=
      (Subgroup.closure_le _).mpr (by
        intro y hy
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact htK.1
        · exact htK.2.2.1)
    exact hle hδ
  have hlamK : lam ∈ ctxK t tau x₁ x₂ rho := htK.2.2.2.1
  have hξXinorm := l18_Xi_normal hc13
  set ξ' : G := δ * ξ * δ⁻¹ with hξ'def
  set ξ'' : G := lam * ξ' * lam⁻¹ with hξ''def
  have hξ'_mem : ξ' ∈ ctxXi t tau x₁ x₂ rho := by
    rw [hξ'def]
    exact hξXinorm.2 δ hδK ξ hξ
  have hξ''_mem : ξ'' ∈ ctxXi t tau x₁ x₂ rho := by
    rw [hξ''def]
    exact hξXinorm.2 lam hlamK ξ' hξ'_mem
  have e1 : δ * ξ = ξ' * δ := by rw [hξ'def]; group
  have e2 : lam * ξ' = ξ'' * lam := by rw [hξ''def]; group
  have hlamd : (lam * δ) * (lam * δ) = δ * δ := by
    calc (lam * δ) * (lam * δ) = lam * (δ * lam) * δ := by group
      _ = lam * (lam * δ) * δ := by rw [hcommD]
      _ = (lam * lam) * (δ * δ) := by group
      _ = δ * δ := by rw [hlam2, one_mul]
  have hsquare : (ξ * (lam * δ)) * (ξ * (lam * δ)) = ξ * ξ'' * (δ * δ) := by
    calc (ξ * (lam * δ)) * (ξ * (lam * δ))
        = ξ * (lam * (δ * ξ * (lam * δ))) := by group
      _ = ξ * (lam * (ξ' * δ * (lam * δ))) := by rw [e1]
      _ = ξ * (lam * ξ' * δ * (lam * δ)) := by group
      _ = ξ * (ξ'' * lam * δ * (lam * δ)) := by rw [e2]
      _ = (ξ * ξ'') * ((lam * δ) * (lam * δ)) := by group
      _ = (ξ * ξ'') * (δ * δ) := by rw [hlamd]
  have hprod : (ξ * ξ'') * (δ * δ) = 1 := by
    rw [← hsquare]
    exact h2
  have hδδ_eq : δ * δ = (ξ * ξ'')⁻¹ := eq_inv_of_mul_eq_one_right hprod
  have hδδ_mem_Xi : δ * δ ∈ ctxXi t tau x₁ x₂ rho := by
    rw [hδδ_eq]
    exact inv_mem (mul_mem hξ hξ''_mem)
  have hδδ_mem_closure : δ * δ ∈ closure ({t, om} : Set G) :=
    (closure ({t, om} : Set G)).mul_mem hδ hδ
  have hbot : δ * δ ∈ (⊥ : Subgroup G) := by
    have hinf : δ * δ ∈ ctxXi t tau x₁ x₂ rho ⊓ closure ({t, om} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hδδ_mem_Xi, hδδ_mem_closure⟩
    rw [k18_Xi_cap_tom hc] at hinf
    exact hinf
  exact Subgroup.mem_bot.mp hbot

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
