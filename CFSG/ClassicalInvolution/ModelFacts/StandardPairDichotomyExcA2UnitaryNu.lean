module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryEmbed
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2F4Levi

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal CFSG.LieType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Data

@[expose] def l0F4 : List (Fin (Tag.rank .F4)) :=
  [idxF4 1, idxF4 2, idxF4 3, idxF4 1, idxF4 2, idxF4 1]

theorem l0F4_mem_J : ∀ j ∈ l0F4, j ∈ JF4 := by
  unfold l0F4 JF4 idxF4
  decide +kernel

theorem simpleWordAct_l0F4_theta : simpleWordAct .F4 l0F4 thetaF4' = thetaF4' := by
  unfold l0F4 simpleWordAct idxF4
  decide +kernel

theorem simpleWordAct_l0F4_delta : simpleWordAct .F4 l0F4 deltaF4 = -thetaF4' - deltaF4 := by
  unfold l0F4 simpleWordAct idxF4
  decide +kernel

theorem simpleWordAct_l0F4_neg_theta : simpleWordAct .F4 l0F4 (-thetaF4') = -thetaF4' := by
  rw [simpleWordAct_neg, simpleWordAct_l0F4_theta]

end Data

section Nu

variable {k : Type} [Field k]

variable (k) in
@[expose] noncomputable def nu0F4 : ModGL .F4 k :=
  simpleWordElt .F4 k l0F4 * rootSL2 .F4 k thetaF4 WSL

theorem nu0F4_mem_monomialSubgroup : nu0F4 k ∈ monomialSubgroup .F4 k :=
  mul_mem (simpleWordElt_mem_monomialSubgroup _) (rootSL2_WSL_mem_monomialSubgroup isRoot_thetaF4)

theorem nu0F4_conj_pinnedX {γ γ'' : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (h : simpleWordAct .F4 l0F4
      (γ - (2 * iform thetaF4 γ / iform thetaF4 thetaF4) • thetaF4) = γ'') :
    ∃ μ : kˣ, ∀ c : k,
      nu0F4 k * pinnedX .F4 k γ c * (nu0F4 k)⁻¹ = pinnedX .F4 k γ'' (μ * c) := by
  obtain ⟨μ, hμ⟩ := rootSL2_WSL_conj_pinnedX (K := k) isRoot_thetaF4 hγ
  have hγ₁ : IsRoot .F4 (γ - (2 * iform thetaF4 γ / iform thetaF4 thetaF4) • thetaF4) := by
    have := IsRoot.smul hγ (rootReflection thetaF4)
    rwa [((exceptional_Lang_root_rank_one_torus_transport .F4 k isRoot_thetaF4).2.2.2.1 γ).1]
      at this
  obtain ⟨ε, hε, hε'⟩ := simpleWordElt_conj_pinnedX (F := k) l0F4 hγ₁
  have hε0 : ε ≠ 0 := fun h0 => by simp [h0] at hε
  refine ⟨Units.mk0 ε hε0 * μ, fun c => ?_⟩
  rw [h] at hε'
  calc nu0F4 k * pinnedX .F4 k γ c * (nu0F4 k)⁻¹ =
      simpleWordElt .F4 k l0F4 * (rootSL2 .F4 k thetaF4 WSL * pinnedX .F4 k γ c *
        (rootSL2 .F4 k thetaF4 WSL)⁻¹) * (simpleWordElt .F4 k l0F4)⁻¹ := by
        rw [nu0F4]; group
    _ = _ := by
        rw [hμ, hε']
        simp [mul_assoc]

theorem nu0F4_conj_theta : ∃ μ : kˣ, ∀ c : k,
    nu0F4 k * pinnedX .F4 k thetaF4 c * (nu0F4 k)⁻¹ = pinnedX .F4 k (-thetaF4) (μ * c) :=
  nu0F4_conj_pinnedX isRoot_thetaF4 (by
    rw [thetaF4_eq]
    unfold l0F4 simpleWordAct idxF4
    decide +kernel)

theorem nu0F4_conj_neg_theta : ∃ μ : kˣ, ∀ c : k,
    nu0F4 k * pinnedX .F4 k (-thetaF4) c * (nu0F4 k)⁻¹ = pinnedX .F4 k thetaF4 (μ * c) :=
  nu0F4_conj_pinnedX (IsRoot.neg isRoot_thetaF4) (by
    rw [thetaF4_eq]
    unfold l0F4 simpleWordAct idxF4
    decide +kernel)

theorem nu0F4_conj_delta : ∃ μ : kˣ, ∀ c : k,
    nu0F4 k * pinnedX .F4 k deltaF4 c * (nu0F4 k)⁻¹ = pinnedX .F4 k (-deltaF4) (μ * c) :=
  nu0F4_conj_pinnedX isPartnerF4_deltaF4.1 (by
    rw [thetaF4_eq]
    unfold l0F4 simpleWordAct idxF4
    decide +kernel)

theorem nu0F4_conj_neg_delta : ∃ μ : kˣ, ∀ c : k,
    nu0F4 k * pinnedX .F4 k (-deltaF4) c * (nu0F4 k)⁻¹ = pinnedX .F4 k deltaF4 (μ * c) :=
  nu0F4_conj_pinnedX (IsRoot.neg isPartnerF4_deltaF4.1) (by
    rw [thetaF4_eq]
    unfold l0F4 simpleWordAct idxF4
    decide +kernel)

theorem nu0F4_comm_signDiagF4 :
    signDiagF4 k deltaF4 * nu0F4 k = nu0F4 k * signDiagF4 k deltaF4 := by
  have hw : MapsRootLines (nu0F4 k)
      ((coxeterSystem .F4).wordProd l0F4 * rootReflection thetaF4) :=
    (mapsRootLines_list_prod l0F4).mul (mapsRootLines_rootSL2_WSL isRoot_thetaF4)
  refine monomial_comm_rootDiagUnit (a := corootDiagF4 deltaF4 (-1 : kˣ))
    nu0F4_mem_monomialSubgroup hw ?_
  set w₀ := (coxeterSystem .F4).wordProd l0F4 * rootReflection thetaF4 with hw₀
  have h1 : w₀ • deltaF4 = -deltaF4 := by
    rw [hw₀, mul_smul,
      ((exceptional_Lang_root_rank_one_torus_transport .F4 k isRoot_thetaF4).2.2.2.1 deltaF4).1,
      wordProd_smul_eq_simpleWordAct, thetaF4_eq]
    unfold l0F4 simpleWordAct idxF4
    decide +kernel
  have h2 : w₀⁻¹ • deltaF4 = -deltaF4 := by
    have h : w₀⁻¹ • (w₀ • deltaF4) = w₀⁻¹ • (-deltaF4) := by rw [h1]
    rw [inv_smul_smul, smul_neg] at h
    exact (neg_eq_iff_eq_neg.1 h.symm)
  have h3 : ∀ v : Fin (Tag.rank .F4) → ℤ, iform deltaF4 (w₀ • v) = -iform deltaF4 v := fun v => by
    have := iform_smul_smul (τ := .F4) w₀ (w₀⁻¹ • deltaF4) v
    rw [smul_inv_smul, h2, iform_neg_left] at this
    exact this
  intro v
  rw [rootChar_corootDiagF4 isPartnerF4_deltaF4.1 isPartnerF4_deltaF4.2.1,
    rootChar_corootDiagF4 isPartnerF4_deltaF4.1 isPartnerF4_deltaF4.2.1, h3]
  obtain ⟨m, hm⟩ := even_iform_of_long_F4 isPartnerF4_deltaF4.1 isPartnerF4_deltaF4.2.1 v
  rw [hm, show -(m + m) / 2 = -m by omega, show (m + m) / 2 = m by omega]
  rcases Int.even_or_odd m with h | h
  · rw [h.neg.neg_one_zpow, h.neg_one_zpow]
  · rw [h.neg.neg_one_zpow, h.neg_one_zpow]

end Nu

end CFSG.ClassicalInvolution.ModelFacts.Levi
