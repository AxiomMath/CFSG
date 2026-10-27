module

public import CFSG.CGT.Stroth77.Stroth3VCaseX

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

@[expose] def KillFact (τ : StrothTypeIndex) : Prop :=
  ∀ ruv rt d0 : Torus τ.k, ruv + τ.action.φuv ruv = 0 → rt + τ.action.φt rt = 0 →
    ruv + τ.action.φuv rt = rt + τ.action.φt ruv →
    τ.action.φρ (ruv + τ.action.φuv rt) = ruv - d0 + τ.action.φuv d0 →
    τ.action.φρ ruv = rt - d0 + τ.action.φt d0 →
    ∃ d : Torus τ.k, InW (ruv - d + τ.action.φuv d) ∧ InW (rt - d + τ.action.φt d)

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem mem_of_proj_rho_of_kill (h : F.IsD D dD) (hτ : VFacts τ) (hK : KillFact τ)
    (hS : Local.Setting (F.S : Subgroup G) D) {e d₀ : G} (he : e ∈ hS.R)
    (huv : e⁻¹ * dD.uv * e * dD.uv⁻¹ ∈ D) (ht : e⁻¹ * dD.t * e * dD.t⁻¹ ∈ D) (hd₀ : d₀ ∈ D)
    (hp : hS.proj dD.ρ e = e * d₀) : e ∈ D := by
  obtain ⟨c1, c2, c3⟩ := cocycle_uv_t dD.e dD.uv_sq dD.t_sq dD.uv_comm_t dD.uv_mem dD.t_mem
    dD.uv_conj dD.t_conj huv ht
  obtain ⟨s1, s2⟩ := h.rho_stable_crd hS he huv ht hd₀ hp
  obtain ⟨d, w1, w2⟩ := hK _ _ _ c1 c2 c3 s1 s2
  obtain ⟨dG, hdG, hcdG⟩ := exists_crdT_eq dD.e d
  obtain ⟨huv', cuv'⟩ := crdT_conj_mul dD.e dD.uv_mem dD.uv_sq dD.uv_conj huv hdG
  obtain ⟨ht', ct'⟩ := crdT_conj_mul dD.e dD.t_mem dD.t_sq dD.t_conj ht hdG
  obtain ⟨x2, x0, xρ, hE⟩ := h.crd_x1
  have hxW : InW (crdT dD.e (((F.dA.a : F.A) : G) ^ 2)) := ⟨hτ.sq_W _ x2 xρ, x2⟩
  have hR : e * dG ∈ hS.R := mul_mem he (hS.D_le_R hdG)
  have key : e * dG ∈ D := by
    refine h.mem_of_conj_mem_E (hS.R_le_S hR) (hS.R_le_centralizer_omega hR) ?_ ?_
    · refine hE _ huv' ?_
      rw [cuv', hcdG]
      exact hτ.W_orbit _ _ hxW x0 w1
    · refine hE _ ht' ?_
      rw [ct', hcdG]
      exact hτ.W_orbit _ _ hxW x0 w2
  have := mul_mem key (inv_mem hdG)
  simpa using this

theorem stroth_form_ii (h : F.IsD D dD) (hτ : VFacts τ) (hK : KillFact τ)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G))) :
    (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      ∃ X : Subgroup G, IsMulCommutative X ∧ F.A ≤ X ∧ X ≤ (F.S : Subgroup G) ∧
        F.dA.L ≤ Subgroup.normalizer
          ((X ⊔ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) ∧
        Nat.card D < Nat.card X := by
  have hS := h.setting hns
  have hDR : D ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) := hS.D_le_R
  by_cases hRD : (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D
  · exact Or.inl hRD
  · refine Or.inr (h.exists_X_of_vcase hτ hns (fun e he huv ht hc => ?_)
      (lt_of_le_of_ne hDR (Ne.symm hRD)))
    obtain ⟨d₀, hd₀, hp⟩ := exists_proj_rho_eq hS he hc
    exact h.mem_of_proj_rho_of_kill hτ hK hS he huv ht hd₀ hp

end StrothFrame.IsD

end CFSG.CGT.Stroth77
