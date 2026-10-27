module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4F2Group
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4F2Hom

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.SeitzGeneration.ExcOuterLeOne
open scoped commutatorElement MatrixGroups


section Core

theorem d4F2_core {K : Type} [Field K] [Finite K] [CharP K 2] {k : Subfield K}
    (hk : Nat.card k = 2) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hK : Nat.card K = Nat.card k ^ d)
    (H : Subgroup ↥(adjointGroup Tag.D4 K))
    (hR : ∀ γ : Fin Tag.D4.rank → ℤ, IsRoot Tag.D4 γ → ∀ c ∈ k,
      xPar (rootOperatorFamily Tag.D4) γ c ∈ H)
    {q : ↥(adjointGroup Tag.D4 K)} (hq : q ∈ d4F2_Qgrp K) {μ : K} (hμ : μ ∉ k)
    (hy : q * xPar (rootOperatorFamily Tag.D4) (-d4F2Theta) μ * q⁻¹ ∈ H) :
    ∃ s : K, s ∉ k ∧ xPar (rootOperatorFamily Tag.D4) d4F2Theta s ∈ H := by
  obtain ⟨φ, h12, h23, h13, h31⟩ := d4F2_exists_a2Hom (K := K)
  obtain ⟨c₁, hc₁⟩ := d4F2_Q_conj_delta (Subgroup.inv_mem _ hq) d4F2_isRoot_delta1 d4F2_lvl_delta1
  obtain ⟨c₂, hc₂⟩ := d4F2_Q_conj_delta (Subgroup.inv_mem _ hq) d4F2_isRoot_delta2 d4F2_lvl_delta2
  let H₁ : Subgroup SL(3, K) := (H.comap (MulAut.conj q).toMonoidHom).comap φ
  have hmem : ∀ g : SL(3, K), g ∈ H₁ ↔ q * φ g * q⁻¹ ∈ H := fun g => Iff.rfl
  have hsub : A2Gen μ c₁ c₂ ≤ H₁ := by
    rw [A2Gen, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl | rfl)
    · show q * φ (t13 1) * q⁻¹ ∈ H
      rw [h13, ((d4F2_commute_Q_theta hq 1).eq), mul_inv_cancel_right]
      exact hR _ d4F2_isRoot_theta 1 k.one_mem
    · show q * φ (t31 μ) * q⁻¹ ∈ H
      rw [h31]
      exact hy
    · show q * φ (t12 1 * t13 c₁) * q⁻¹ ∈ H
      have h := hc₁
      rw [inv_inv] at h
      rw [map_mul, h12, h13, ← h]
      have e : q * (q⁻¹ * xPar (rootOperatorFamily Tag.D4) d4F2Delta1 1 * q) * q⁻¹ =
          xPar (rootOperatorFamily Tag.D4) d4F2Delta1 1 := by group
      rw [e]
      exact hR _ d4F2_isRoot_delta1 1 k.one_mem
    · show q * φ (t23 1 * t13 c₂) * q⁻¹ ∈ H
      have h := hc₂
      rw [inv_inv] at h
      rw [map_mul, h23, h13, ← h]
      have e : q * (q⁻¹ * xPar (rootOperatorFamily Tag.D4) d4F2Delta2 1 * q) * q⁻¹ =
          xPar (rootOperatorFamily Tag.D4) d4F2Delta2 1 := by group
      rw [e]
      exact hR _ d4F2_isRoot_delta2 1 k.one_mem
  obtain ⟨s, hs, hts⟩ := a2_lemma hk hd hd2 hK hμ c₁ c₂
  refine ⟨s, hs, ?_⟩
  have h1 := (hmem _).1 (hsub hts)
  rwa [h13, ((d4F2_commute_Q_theta hq s).eq), mul_inv_cancel_right] at h1

end Core

end CFSG.LieType.SeitzGeneration.ExcWideThree
