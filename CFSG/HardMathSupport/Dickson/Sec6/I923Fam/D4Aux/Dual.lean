module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Two
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Odd
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Three
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Duality
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.D4Aux

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual
open CFSG.HardMathSupport.Dickson.Sec6.I923

set_option linter.unusedSectionVars false

section Dual


theorem noL2Layer_three_D4_outer (hA2 : TriD4Aux.TriD4A2NoL2) (hC3 : TriD4Aux.TriD4C3NoL2)
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) : NoL2Layer φ := by
  by_cases h2 : ℓ = 2
  · subst h2
    exact TriD4Aux.noL2Layer_three_D4_outer_two hf hK σ hσ φ hφ3 hφ
  · by_cases h3 : ℓ = 3
    · subst h3
      haveI : CharP K 3 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
          (by omega) (by rw [hK, ← pow_mul, mul_comm] : Nat.card K = 3 ^ (3 * f))
      exact TriD4Aux.noL2Layer_three_D4_outer_three hC3 hf hK σ hσ φ hφ3 hφ
    · exact TriD4Aux.noL2Layer_three_D4_outer_odd hA2 hℓ h2 h3 hf hK σ hσ φ hφ3 hφ

theorem noL2Layer_of_graphType (hA2 : TriD4Aux.TriD4A2NoL2) (hC3 : TriD4Aux.TriD4C3NoL2)
    {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) : NoL2Layer α := by
  obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨e⟩⟩ :=
    exists_dual_fixEquiv hf K hK α hα3 g a hε hαeq
  haveI := TriD4Aux.finite_graphFixedRootGroup_D4 Fr
  exact TriD4Aux.noL2Layer_of_fixEquiv e
    (noL2Layer_three_D4_outer hA2 hC3 Fact.out hf hK₃ Fr hFr φ hφ3 hφout)

end Dual

end CFSG.HardMathSupport.Dickson.Sec6.I923.D4Aux
