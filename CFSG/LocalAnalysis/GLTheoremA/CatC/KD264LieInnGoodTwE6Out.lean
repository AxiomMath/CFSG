module

public import CFSG.LieType.Chevalley.TwistedE6NormalForm
import CFSG.LieType.Chevalley.TwistedE6RootGroupPerfect
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.ComponentInitial


theorem mem_inndiag_of_mem_innAutDerived_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {α : MulAut (twistedE6RootGroup K σ)}
    (hα : α ∈ innAutDerived (twistedE6RootGroup K σ)) :
    α ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
  have hC : commutator (twistedE6RootGroup K σ) = ⊤ :=
    commutator_twistedE6RootGroup_eq_top hℓ hf hK σ hσ
  rw [innAutDerived_eq_commutator_of_perfect hC] at hα
  have hKf : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hring := card_ringAut_and_isCyclic hℓ K hKf
  haveI : IsCyclic (RingAut K) := hring.2
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, hsurj, hker, -, -, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  rw [← hker, MonoidHom.mem_ker]
  have h1 : Θ α ∈ (commutator (MulAut (twistedE6RootGroup K σ))).map Θ := ⟨α, hα, rfl⟩
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hsurj,
    ← commutator_def, commutator_eq_bot] at h1
  exact h1

theorem mem_inner_of_mem_innAutDerived_of_pow_eq_one_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {α : MulAut (twistedE6RootGroup K σ)} (hα : α ∈ innAutDerived (twistedE6RootGroup K σ))
    (hαp : α ^ p = 1) : α ∈ inner (twistedE6RootGroup K σ) := by
  have hx := mem_inndiag_of_mem_innAutDerived_twistedE6 hℓ hf hK σ hσ hα
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, hcube, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  set J := twistedE6Inn K σ ⊔ twistedE6Diag K σ with hJ
  have hcop : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)
  have hxp' : (⟨α, hx⟩ : J) ^ p = 1 := Subtype.ext (by simpa using hαp)
  have ha : (QuotientGroup.mk ⟨α, hx⟩ : J ⧸ (twistedE6Inn K σ).subgroupOf J) = 1 :=
    (pow_eq_one_iff_of_coprime hcop).1
      ⟨hcube _, by rw [← QuotientGroup.mk_pow, hxp', QuotientGroup.mk_one]⟩
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 ha)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
