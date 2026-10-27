module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18s
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18l

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem k18_Fu_of_classes (hc : Ctx18A t L S x₁ x₂ lam rho tau om 𝒮)
    (hA : ∀ {g ξ : G}, ξ ∈ ctxXi t tau x₁ x₂ rho → g * t * g⁻¹ = ξ * lam → False)
    (hB : ∀ {g ξ : G}, ξ ∈ ctxXi t tau x₁ x₂ rho → g * t * g⁻¹ = ξ * (lam * tau) → False)
    (hD : ∀ {g ξ : G}, ξ ∈ ctxXi t tau x₁ x₂ rho → g * t * g⁻¹ = ξ * (lam * om) → False)
    (hC : ∀ {g ξ : G}, ξ ∈ ctxXi t tau x₁ x₂ rho → g * t * g⁻¹ = ξ * (lam * t) →
      ∃ η ∈ ctxXi t tau x₁ x₂ rho, ξ * (lam * t) = η * (lam * t) * η⁻¹)
    {g e : G} (he : e ∈ ctxOK t tau x₁ x₂ rho) (hg : g * t * g⁻¹ = e * (lam * t)) :
    ∃ o ∈ ctxOK t tau x₁ x₂ rho, e * (lam * t) = o * (lam * t) * o⁻¹ := by
  have hc13 : Ctx13 t L S x₁ x₂ lam rho tau om := hc.toCtx13
  have hc18 : Ctx18 t L S x₁ x₂ lam rho tau om 𝒮 := hc.toCtx18
  obtain ⟨ξ, hξ, δ, hδ, hx⟩ := k18_coset_decomp hc13 he
  have hgt : g * t * g⁻¹ = ξ * (lam * δ) := hg.trans hx
  have hsq : (ξ * (lam * δ)) * (ξ * (lam * δ)) = 1 := by
    rw [← hgt]
    have ht2 : t * t = 1 := by
      have h := (ctx13_relations hc13).1
      rw [pow_two] at h; exact h
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hδ2 : δ * δ = 1 := k18_sq_cond hc18 hξ hδ hsq
  rcases k18_D_invol_cases hc13 hδ hδ2 with h | h | h | h | h | h
  ·
    subst h
    exact (hA hξ (by simpa using hgt)).elim
  ·
    subst h
    exact (hB hξ hgt).elim
  ·
    subst h
    exact (hD hξ hgt).elim
  ·
    subst h
    have htK : t ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc13).1
    set ξ₁ : G := t⁻¹ * ξ * t with hξ₁
    have hξ₁mem : ξ₁ ∈ ctxXi t tau x₁ x₂ rho := by
      rw [hξ₁]
      simpa using (l18_Xi_normal hc13).2 t⁻¹ ((ctxK t tau x₁ x₂ rho).inv_mem htK) ξ hξ
    have hξ' : t * ξ₁ * t⁻¹ = ξ := by rw [hξ₁]; group
    have hlam' : t * lam * t⁻¹ = lam := by
      have h := (l17_lam_comm hc13).1
      rw [← h]; group
    have hom' : t * om * t⁻¹ = om * tau := k18_t_om hc13
    have hcomm : om * tau = tau * om := by
      obtain ⟨ht2, -, hom2, htau2, -, ht_tau, hom_t⟩ := ctx13_relations hc13
      exact om_tau_comm ht2 hom2 htau2 ht_tau hom_t
    have hconj : t * (ξ₁ * (lam * om)) * t⁻¹ = ξ * (lam * (tau * om)) := by
      calc t * (ξ₁ * (lam * om)) * t⁻¹
          = (t * ξ₁ * t⁻¹) * (t * lam * t⁻¹) * (t * om * t⁻¹) := by group
        _ = ξ * lam * (om * tau) := by rw [hξ', hlam', hom']
        _ = ξ * (lam * (tau * om)) := by rw [hcomm]; group
    have hEq : (t⁻¹ * g) * t * (t⁻¹ * g)⁻¹ = ξ₁ * (lam * om) := by
      have h1 : t * (ξ₁ * (lam * om)) * t⁻¹ = g * t * g⁻¹ := by rw [hconj, ← hgt]
      calc (t⁻¹ * g) * t * (t⁻¹ * g)⁻¹
          = t⁻¹ * (g * t * g⁻¹) * t := by group
        _ = t⁻¹ * (t * (ξ₁ * (lam * om)) * t⁻¹) * t := by rw [← h1]
        _ = ξ₁ * (lam * om) := by group
    exact (hD hξ₁mem hEq).elim
  ·
    subst h
    obtain ⟨η, hη, hηeq⟩ := hC hξ hgt
    refine ⟨η, (l18_Xi_le_OK hc13) hη, ?_⟩
    rw [hx, hηeq]
  ·
    subst h
    have homK : om ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc13).2.2.1
    set ξ₁ : G := om⁻¹ * ξ * om with hξ₁
    have hξ₁mem : ξ₁ ∈ ctxXi t tau x₁ x₂ rho := by
      rw [hξ₁]
      simpa using (l18_Xi_normal hc13).2 om⁻¹ ((ctxK t tau x₁ x₂ rho).inv_mem homK) ξ hξ
    have hξ' : om * ξ₁ * om⁻¹ = ξ := by rw [hξ₁]; group
    have hlam' : om * lam * om⁻¹ = lam := by
      have h := (l17_lam_comm hc13).2.2
      rw [← h]; group
    have homt' : om * t * om⁻¹ = t * tau := (ctx13_relations hc13).2.2.2.2.2.2
    have hconj : om * (ξ₁ * (lam * t)) * om⁻¹ = ξ * (lam * (t * tau)) := by
      calc om * (ξ₁ * (lam * t)) * om⁻¹
          = (om * ξ₁ * om⁻¹) * (om * lam * om⁻¹) * (om * t * om⁻¹) := by group
        _ = ξ * lam * (t * tau) := by rw [hξ', hlam', homt']
        _ = ξ * (lam * (t * tau)) := by group
    have hEq : (om⁻¹ * g) * t * (om⁻¹ * g)⁻¹ = ξ₁ * (lam * t) := by
      have h1 : om * (ξ₁ * (lam * t)) * om⁻¹ = g * t * g⁻¹ := by rw [hconj, ← hgt]
      calc (om⁻¹ * g) * t * (om⁻¹ * g)⁻¹
          = om⁻¹ * (g * t * g⁻¹) * om := by group
        _ = om⁻¹ * (om * (ξ₁ * (lam * t)) * om⁻¹) * om := by rw [← h1]
        _ = ξ₁ * (lam * t) := by group
    obtain ⟨η, hη, hηeq⟩ := hC hξ₁mem hEq
    refine ⟨om * η, Subgroup.mul_mem _ ((l18_tau_om_mem_OK hc13).2.2)
      ((l18_Xi_le_OK hc13) hη), ?_⟩
    calc e * (lam * t) = ξ * (lam * (t * tau)) := hx
      _ = om * (ξ₁ * (lam * t)) * om⁻¹ := hconj.symm
      _ = om * (η * (lam * t) * η⁻¹) * om⁻¹ := by rw [hηeq]
      _ = (om * η) * (lam * t) * (om * η)⁻¹ := by group

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
