module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.QGroup

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement MatrixGroups

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne



section Core

variable {τ : Tag} {K : Type} [Field K]

theorem core_f2 (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Finite K] [CharP K 2] {k : Subfield K}
    (hk : Nat.card k = 2) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hK : Nat.card K = Nat.card k ^ d)
    (H : Subgroup ↥(adjointGroup τ K))
    (hR : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ H)
    {q : ↥(adjointGroup τ K)} (hq : q ∈ Qgrp τ K) {μ : K} (hμ : μ ∉ k)
    (hy : q * xPar (rootOperatorFamily τ) (-hiRoot τ) μ * q⁻¹ ∈ H) :
    ∃ s : K, s ∉ k ∧ xPar (rootOperatorFamily τ) (hiRoot τ) s ∈ H := by
  obtain ⟨φ, h12, h23, h13, h31⟩ := exists_a2Hom hτ (K := K)
  have hθ := (hiRoot_isMax hτ).1
  obtain ⟨c₁, hc₁⟩ := Q_conj_delta hτ (Subgroup.inv_mem _ hq) (isRoot_delta1 τ) (lvl_delta1 τ)
  obtain ⟨c₂, hc₂⟩ := Q_conj_delta hτ (Subgroup.inv_mem _ hq) (isRoot_delta2 hτ) (lvl_delta2 hτ)
  let H₁ : Subgroup SL(3, K) := (H.comap (MulAut.conj q).toMonoidHom).comap φ
  have hmem : ∀ g : SL(3, K), g ∈ H₁ ↔ q * φ g * q⁻¹ ∈ H := fun g => Iff.rfl
  have hsub : A2Gen μ c₁ c₂ ≤ H₁ := by
    rw [A2Gen, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl | rfl)
    · show q * φ (t13 1) * q⁻¹ ∈ H
      rw [h13, ((commute_Q_hiRoot hτ hq 1).eq), mul_inv_cancel_right]
      exact hR _ hθ 1 k.one_mem
    · show q * φ (t31 μ) * q⁻¹ ∈ H
      rw [h31]
      exact hy
    · show q * φ (t12 1 * t13 c₁) * q⁻¹ ∈ H
      have h := hc₁ 1
      rw [inv_inv, mul_one] at h
      rw [map_mul, h12, h13, ← h]
      have e : q * (q⁻¹ * xPar (rootOperatorFamily τ) (delta1 τ) 1 * q) * q⁻¹ =
          xPar (rootOperatorFamily τ) (delta1 τ) 1 := by group
      rw [e]
      exact hR _ (isRoot_delta1 τ) 1 k.one_mem
    · show q * φ (t23 1 * t13 c₂) * q⁻¹ ∈ H
      have h := hc₂ 1
      rw [inv_inv, mul_one] at h
      rw [map_mul, h23, h13, ← h]
      have e : q * (q⁻¹ * xPar (rootOperatorFamily τ) (delta2 τ) 1 * q) * q⁻¹ =
          xPar (rootOperatorFamily τ) (delta2 τ) 1 := by group
      rw [e]
      exact hR _ (isRoot_delta2 hτ) 1 k.one_mem
  obtain ⟨s, hs, hts⟩ := a2_lemma hk hd hd2 hK hμ c₁ c₂
  refine ⟨s, hs, ?_⟩
  have h1 := (hmem _).1 (hsub hts)
  rwa [h13, ((commute_Q_hiRoot hτ hq s).eq), mul_inv_cancel_right] at h1

end Core

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
