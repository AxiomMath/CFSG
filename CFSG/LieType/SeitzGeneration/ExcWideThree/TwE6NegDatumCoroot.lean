module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Cont

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.SeitzGeneration.ExcHighThree


theorem twE6_corootLine_trivial (K : Type) [Field K] (σ : K ≃+* K)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    {β₁ β₂ δ : Fin TwistTag.E6.tag.rank → ℤ} (hβ₁ : IsRoot TwistTag.E6.tag β₁)
    (hβ₂ : IsRoot TwistTag.E6.tag β₂) (hβ₁₂ : IsRoot TwistTag.E6.tag (β₁ + β₂))
    (h3 : TwKills K σ E₀ g0 ((3 : ℤ) • β₁)) (hδ : TwKills K σ E₀ g0 δ)
    (hδθ : ¬ (3 : ℤ) ∣ iform δ (β₁ + β₂)) :
    ∀ x ∈ E₀, ∀ c : (AlgebraicClosure K)ˣ,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) =
        g0 * rootDiagUnit TwistTag.E6.tag (fun i => c ^ iform (β₁ + β₂) (Pi.single i 1)) * g0⁻¹ →
      x = 1 := by
  intro x hx c hxc
  have hn : ∀ {γ : Fin TwistTag.E6.tag.rank → ℤ}, IsRoot TwistTag.E6.tag γ → iform γ γ = 2 := by
    intro γ hγ
    obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
    have hs : TwistTag.E6.tag.symmetrizer j j = 1 := by
      change (1 : Matrix (Fin 6) (Fin 6) ℤ) j j = 1
      exact Matrix.one_apply_eq j
    rw [hj, hs, mul_one]
  have h1 : iform (β₁ + β₂) β₁ = 1 := by
    have e1 := hn hβ₁
    have e2 := hn hβ₂
    have e12 := hn hβ₁₂
    rw [iform_add_left, iform_add_right, iform_add_right, iform_comm β₂ β₁] at e12
    rw [iform_add_left, iform_comm β₂ β₁]
    linarith
  have hdiag : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) * g0 =
      rootDiagUnit TwistTag.E6.tag (fun i => c ^ iform (β₁ + β₂) (Pi.single i 1)) := by
    rw [hxc]
    group
  have hchar : ∀ v : Fin TwistTag.E6.tag.rank → ℤ, TwKills K σ E₀ g0 v →
      c ^ iform (β₁ + β₂) v = 1 := by
    intro v hv
    obtain ⟨b, hb, hbv⟩ := hv x hx
    have hba : b = fun i => c ^ iform (β₁ + β₂) (Pi.single i 1) :=
      CFSG.LieType.Chevalley.rootDiagUnit_injective (hb.trans hdiag)
    rw [hba] at hbv
    rw [← CFSG.ClassicalInvolution.ModelFacts.Levi.rootChar_thetaDiag]
    exact hbv
  have hc3 : c ^ (3 : ℤ) = 1 := by
    have h := hchar _ h3
    rwa [iform_smul_right, h1, mul_one] at h
  have hcδ : c ^ iform (β₁ + β₂) δ = 1 := hchar _ hδ
  have hcop : IsCoprime (3 : ℤ) (iform (β₁ + β₂) δ) := by
    rw [iform_comm]
    exact Int.prime_three.irreducible.coprime_iff_not_dvd.2 hδθ
  obtain ⟨u, w, huw⟩ := hcop
  have hc1 : c = 1 := by
    calc c = c ^ (u * 3 + w * iform (β₁ + β₂) δ) := by rw [huw, zpow_one]
      _ = (c ^ (3 : ℤ)) ^ u * (c ^ iform (β₁ + β₂) δ) ^ w := by
        rw [zpow_add, mul_comm u, mul_comm w, zpow_mul, zpow_mul]
      _ = 1 := by rw [hc3, hcδ, one_zpow, one_zpow, one_mul]
  have hx1 : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) 1 := by
    rw [hxc, hc1, map_one]
    have h1' : (fun i => (1 : (AlgebraicClosure K)ˣ) ^ iform (β₁ + β₂) (Pi.single i 1)) =
        (1 : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ) := by
      funext i
      exact one_zpow _
    rw [h1', rootDiagUnit_one, mul_one, mul_inv_cancel]
  exact Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) hx1)

end CFSG.LieType.SeitzGeneration.ExcWideThree

end
