module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOutF4
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Field
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Lang.Coordinator
open CFSG.HardMathSupport.Dickson.Sec6.I923
open scoped commutatorElement

set_option linter.unusedSectionVars false

section TwE6


theorem excres_innAutDerived_le_inner_twE6 {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (h3 : ¬ 3 ∣ p ^ f + 1) :
    innAutDerived (twistedE6RootGroup K σ) ≤ twistedE6Inn K σ := by
  refine sup_le le_rfl ?_
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, -, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hp hf K hK σ hσ
  have hg : Nat.gcd 3 (p ^ f + 1) = 1 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have hΔ : twistedE6Diag K σ ≤ twistedE6Inn K σ := by
    rintro _ ⟨u, rfl⟩
    exact compatDiagAutHom_mem_inner hK hσ hg u
  rw [sup_eq_left.2 hΔ] at hker
  exact (excres_commutator_le_ker Θ fun a b =>
    CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K a b).trans hker.le

theorem outDerived3_twE6Good : OutDerived3At FamTwE6Good := by
  intro P _ _ t n p f hadm ht hF hm τ hτ hτ3
  obtain ⟨rfl, h3q⟩ := hF
  have hf : 1 ≤ f := hadm.2.1
  have hE : ChevalleyExceptionalModel P .twistedE6 p f := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_twistedE6RootGroup_equiv hadm.1 hf hE.2
  let θ : P ≃* twistedE6RootGroup K σ := e.symm
  have h1 : MulAut.congr θ τ ∈ innAutDerived (twistedE6RootGroup K σ) :=
    (mem_innAutDerived_congr θ).2 hτ
  exact (isInnerAut_congr θ τ).1
    (excres_innAutDerived_le_inner_twE6 hadm.1 hf hK σ hσ h3q h1)

end TwE6

end CFSG.HardMathSupport.Dickson.Sec6.I1431
