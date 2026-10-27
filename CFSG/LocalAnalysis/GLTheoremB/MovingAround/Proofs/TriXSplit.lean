module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311t2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.TriXPlus

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.Fischer CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartTwo.Sec19 CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c

@[expose] def TriXNoGCentUniPlanesAt
    (r : ℕ) : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 3 → 1 ≤ f → (ℓ ^ f) % 3 = r →
    ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ (E : Subgroup (MulAut (C0 σ))) (x : C0 σ), CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → ¬ E ≤ innerAut (C0 σ) → ¬ TriOddHasGLine σ E →
      (∀ γ : MulAut (C0 σ), TriOddIsGLine σ γ → ¬ ∀ α ∈ E, α * γ = γ * α) →
      x ^ 3 = 1 → x ≠ 1 → MulAut.conj x ∈ E → TriOddIsClassX σ x →
      (∀ ψ : MulAut (C0 σ), ¬ ∀ φ ∈ E.map (MulAut.congr ψ).toMonoidHom,
        ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.toMonoidHom =
          (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∧
        ((graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.toMonoidHom =
          (graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) →
      uniPlaneClosure ℓ E = ⊤

theorem triXNoGCentUniPlanes_of_at
    (h1 : TriXNoGCentUniPlanesAt 1) (h2 : TriXNoGCentUniPlanesAt 2) :
    Inputs2311t.TriXNoGCentUniPlanes := by
  intro ℓ f hℓ hℓ2 hℓ3 hf K _ _ hK σ hσ E x hE hcard hout hnG hncent hx3 hx1 hcx hX hbp
  have hnot : ¬ 3 ∣ ℓ := fun h => hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1 h).symm
  have hpow : ¬ 3 ∣ ℓ ^ f := fun h => hnot (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
  have hlt : ℓ ^ f % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hne : ℓ ^ f % 3 ≠ 0 := fun h => hpow (Nat.dvd_of_mod_eq_zero h)
  have hcases : ℓ ^ f % 3 = 1 ∨ ℓ ^ f % 3 = 2 := by omega
  rcases hcases with h | h
  · exact h1 ℓ f hℓ hℓ2 hℓ3 hf h K hK σ hσ E x hE hcard hout hnG hncent hx3 hx1 hcx hX hbp
  · exact h2 ℓ f hℓ hℓ2 hℓ3 hf h K hK σ hσ E x hE hcard hout hnG hncent hx3 hx1 hcx hX hbp

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.TriXPlus
