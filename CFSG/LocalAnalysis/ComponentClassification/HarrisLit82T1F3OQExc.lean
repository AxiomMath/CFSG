module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQGen
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

section Families


variable {K : Type} [Field K]

theorem outNoA4_adjointGroup_G2_three {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f) :
    OutNoA4 (adjointGroup .G2 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 3 := finite_field_prime_power_characteristic Nat.prime_three hf hK
  have : CharP K CFSG.LieType.Ree.ReeTag.G2.prime := this
  obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  exact outNoA4_of_ker_le_inner Θ mul_comm hker.le

theorem outNoA4_adjointGroup_odd_F4_G2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {τ : Tag} (hτ : τ = .F4 ∨ (τ = .G2 ∧ p ≠ 3)) :
    OutNoA4 (adjointGroup τ K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  have : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic hp K hK).2
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 hf K hK τ hτ
  exact outNoA4_of_ker_le_inner Θ mul_comm_of_isCyclic hker.le

theorem outNoA4_graphFixedRootGroup_D4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    OutNoA4 (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  exact outNoA4_of_ker_le_inner Θ mul_comm_of_isCyclic hker.le

theorem outNoA4_twistedE6RootGroup {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    OutNoA4 (twistedE6RootGroup K σ) := by
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic hp K hK').2
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, hcube, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hp hf K hK σ hσ
  exact outNoA4_of_ker_cube Θ mul_comm_of_isCyclic hker hcube

theorem outNoA4_adjointGroup_E {p f : ℕ} (hp : p.Prime) (hK : Nat.card K = p ^ f) {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : OutNoA4 (adjointGroup τ K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  have : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic hp K hK).2
  obtain ⟨Φ, -, -, hdvd⟩ := exists_outer_hom_E (K := K) hτ
  have hcyc : IsCyclic Φ.ker := by
    rcases hτ with rfl | rfl | rfl
    · rw [det_cartan_E6] at hdvd
      exact isCyclic_of_card_dvd_prime Nat.prime_three (by simpa using hdvd)
    · rw [det_cartan_E7] at hdvd
      exact isCyclic_of_card_dvd_prime Nat.prime_two (by simpa using hdvd)
    · rw [det_cartan_E8] at hdvd
      exact isCyclic_of_card_dvd_prime Nat.prime_two
        ((by simpa using hdvd : Nat.card Φ.ker ∣ 1).trans (one_dvd 2))
  exact outNoA4_of_outer_hom Φ fun a b => Prod.ext (mul_comm_of_isCyclic _ _) (mul_comm _ _)

theorem outNoA4_of_chevalleyExceptionalModel {T : Type} [Group T] {t : StatedLieTag} {p f : ℕ}
    (hT : ChevalleyExceptionalModel T t p f) (hp2 : p ≠ 2) : OutNoA4 T := by
  obtain ⟨⟨hpp, hf, -⟩, hm⟩ := hT
  cases t
  case G2 =>
    have hm' : UntwistedChevalleyModel T .G2 (p ^ f) := hm
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm'
    refine OutNoA4.of_mulEquiv e.symm ?_
    by_cases h3 : p = 3
    · subst h3
      exact outNoA4_adjointGroup_G2_three hf hK
    · exact outNoA4_adjointGroup_odd_F4_G2 hpp hp2 hf hK (Or.inr ⟨rfl, h3⟩)
  case F4 =>
    have hm' : UntwistedChevalleyModel T .F4 (p ^ f) := hm
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hm'
    exact OutNoA4.of_mulEquiv e.symm (outNoA4_adjointGroup_odd_F4_G2 hpp hp2 hf hK (Or.inl rfl))
  case E6 =>
    have hm' : UntwistedChevalleyModel T .E6 (p ^ f) := hm
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm'
    exact OutNoA4.of_mulEquiv e.symm (outNoA4_adjointGroup_E hpp hK (Or.inl rfl))
  case E7 =>
    have hm' : UntwistedChevalleyModel T .E7 (p ^ f) := hm
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 hm'
    exact OutNoA4.of_mulEquiv e.symm (outNoA4_adjointGroup_E hpp hK (Or.inr (Or.inl rfl)))
  case E8 =>
    have hm' : UntwistedChevalleyModel T .E8 (p ^ f) := hm
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E8 hm'
    exact OutNoA4.of_mulEquiv e.symm (outNoA4_adjointGroup_E hpp hK (Or.inr (Or.inr rfl)))
  case twistedE6 =>
    have hm' : TwistedChevalleyModel T .E6 (p ^ f) := hm
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .E6 hpp hf hm'
    exact OutNoA4.of_mulEquiv e.symm (outNoA4_twistedE6RootGroup hpp hf hK σ hσ)
  case trialityD4 =>
    have hm' : TwistedChevalleyModel T .D4 (p ^ f) := hm
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hpp hf hm'
    exact OutNoA4.of_mulEquiv e.symm (outNoA4_graphFixedRootGroup_D4 hpp hp2 hf hK σ hσ)
  all_goals exact (hm : False).elim

end Families

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
