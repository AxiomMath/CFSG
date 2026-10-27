module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Two
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Odd
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Three

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.CrossChar (exists_catEquiv_trialityD4)
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

set_option linter.unusedSectionVars false

section Final


theorem exists_graphFixed_of_chevalleyExceptional {T : Type} [Group T] {ℓ f : ℕ}
    (hm : ChevalleyExceptionalModel T .trialityD4 ℓ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = (ℓ ^ f) ^ 3 ∧
      (∀ c, σ c = c ^ (ℓ ^ f)) ∧ Nonempty (T ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨hadm, hmod⟩ := hm
  obtain ⟨K, _, _, σ₀, hK, hσ₀, ⟨e⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_graphFixedRootGroup_of_twisted_prime hadm.1 hadm.2.1
      hmod
  have hbij : Function.Bijective σ₀ := ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩
  let σ : K ≃+* K := RingEquiv.ofBijective σ₀ hbij
  have hσ : ∀ c, σ c = c ^ (ℓ ^ f) := hσ₀
  have hK3 : Nat.card K = (ℓ ^ f) ^ 3 := hK
  let e' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* T := e
  exact ⟨K, inferInstance, inferInstance, σ, hK3, hσ, ⟨e'.symm⟩⟩

theorem noL2OuterAt_triD4 (hA2 : TriD4Aux.TriD4A2NoL2) (hC3 : TriD4Aux.TriD4C3NoL2) :
    NoL2OuterAt FamTriD4 := by
  intro P _ _ t n p f hadm ht hF hm ψ hψ3 hninn
  obtain rfl := hF
  have hexc : ChevalleyExceptionalModel P .trialityD4 p f := by
    rcases hm with ⟨hcl, -⟩ | ⟨-, -, hexc⟩ | ⟨-, hree, -⟩ | ⟨-, h, -⟩
    · exact absurd hcl (by decide)
    · exact hexc
    · exact absurd hree (by decide)
    · exact absurd h (by decide)
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_graphFixed_of_chevalleyExceptional hexc
  obtain ⟨hp, hf, -⟩ := hadm
  haveI := TriD4Aux.finite_graphFixedRootGroup_D4 σ
  refine OrthAux.noL2Layer_of_congr e ?_
  have hφ3 : (MulAut.congr e ψ) ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hφ : MulAut.congr e ψ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
    rintro ⟨c, hc⟩
    apply hninn
    refine ⟨e.symm c, (MulAut.congr e).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
    exact hc
  by_cases h2 : p = 2
  · subst h2
    exact TriD4Aux.noL2Layer_three_D4_outer_two hf hK σ hσ _ hφ3 hφ
  · by_cases h3 : p = 3
    · subst h3
      haveI : CharP K 3 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_three (by omega) (by rw [hK, ← pow_mul, mul_comm] : Nat.card K = 3 ^ (3 * f))
      exact TriD4Aux.noL2Layer_three_D4_outer_three hC3 hf hK σ hσ _ hφ3 hφ
    · exact TriD4Aux.noL2Layer_three_D4_outer_odd hA2 hp h2 h3 hf hK σ hσ _ hφ3 hφ

theorem y923_triD4_of_residuals (hA2 : TriD4Aux.TriD4A2NoL2) (hC3 : TriD4Aux.TriD4C3NoL2) :
    Y923_TriD4 :=
  y923_lieRestAt_of_noL2Outer (noL2OuterAt_triD4 hA2 hC3)

end Final

end CFSG.HardMathSupport.Dickson.Sec6.I923
