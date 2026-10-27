module

public import CFSG.LocalAnalysis.GL83PartI.I713.Basic
public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.GL83PartI.I713.ExceptionalCoprime
import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms

public section

namespace GL83.I713

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Chevalley CFSG.ComponentClassification.OuterAutomorphisms

set_option linter.unusedSectionVars false


theorem isCyclic_outer_adjointGroup_G2_of_card {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (h3 : 3 ≤ p ^ f) {K : Type} [Field K] (hK : Nat.card K = p ^ f) :
    IsCyclic (Outer (adjointGroup .G2 K)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  have : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic hp K hK).2
  by_cases hp2 : p = 2
  · subst hp2
    have hf2 : 2 ≤ f := by
      by_contra hlt
      obtain rfl : f = 1 := by omega
      norm_num at h3
    obtain ⟨Θ, -, -, hker, -⟩ :=
      (CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
        hf2 K hK).2
    exact isCyclic_outer_of_ker_eq_inner Θ hker
  · by_cases hp3 : p = 3
    · subst hp3
      have : CharP K 3 := finite_field_prime_power_characteristic Nat.prime_three hf hK
      have : CharP K CFSG.LieType.Ree.ReeTag.G2.prime := this
      obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
      exact isCyclic_outer_of_ker_eq_inner Θ hker
    · obtain ⟨-, Θ, -, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2
        hf K hK .G2 (Or.inr ⟨rfl, hp3⟩)
      exact isCyclic_outer_of_ker_eq_inner Θ hker

theorem isCyclic_outer_of_untwistedModel_G2 {S : Type} [Group S] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (h3 : 3 ≤ p ^ f) (hm : UntwistedChevalleyModel S .G2 (p ^ f)) :
    IsCyclic (Outer S) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm
  have := isCyclic_outer_adjointGroup_G2_of_card hp hf h3 hK
  exact isCyclic_outer_congr e

theorem isCyclic_outer_adjointGroup_F4_of_card {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = p ^ f) :
    IsCyclic (Outer (adjointGroup .F4 K)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  by_cases hp2 : p = 2
  · subst hp2
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
    have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := this
    obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
    exact isCyclic_outer_of_ker_eq_inner Θ hker
  · have : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic hp K hK).2
    obtain ⟨-, Θ, -, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2
      hf K hK .F4 (Or.inl rfl)
    exact isCyclic_outer_of_ker_eq_inner Θ hker

theorem isCyclic_outer_of_untwistedModel_F4 {S : Type} [Group S]
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hm : UntwistedChevalleyModel S .F4 (p ^ f)) :
    IsCyclic (Outer S) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hm
  have := isCyclic_outer_adjointGroup_F4_of_card hp hf hK
  exact isCyclic_outer_congr e

theorem isCyclic_outer_of_trialityModel {S : Type} [Group S] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hm : TwistedChevalleyModel S .D4 (p ^ f)) : IsCyclic (Outer S) := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf hm
  have hK' : Nat.card K = (p ^ f) ^ 3 := hK
  have : IsCyclic (Outer (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, -⟩ :=
        even_triality_exact_automorphism_normal_form hf K hK' σ hσ
      have := hcyc
      exact isCyclic_outer_of_ker_eq_inner Θ hker
    · obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, -⟩ :=
        odd_triality_exact_automorphism_normal_form hp hp2 hf K hK' σ hσ
      have := hcyc
      exact isCyclic_outer_of_ker_eq_inner Θ hker
  exact isCyclic_outer_congr e

theorem pRank_outer_le_one_of_untwistedModel_E {S : Type} [Group S] [Finite S] {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p f : ℕ} (hp : p.Prime)
    (hm : UntwistedChevalleyModel S τ (p ^ f)) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : τ = .E6 → ℓ ≠ 3) : pRank ℓ (⊤ : Subgroup (Outer S)) ≤ 1 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hm
  have : Finite (adjointGroup τ K) := Finite.of_equiv S e.toEquiv
  rw [pRank_outer_eq_of_mulEquiv hℓ.one_lt e]
  obtain ⟨Φ, -, -, hdvd⟩ := exists_outer_hom_E (K := K) hτ
  have : IsCyclic (RingAut K) := (card_ringAut_and_isCyclic hp K hK).2
  have : Finite (RingAut K) := Finite.of_injective (fun σ : RingAut K => (σ : K → K))
    DFunLike.coe_injective
  have : NeZero (exactE τ) := ⟨(exactE_pos τ).ne'⟩
  have hB : ¬ ℓ ∣ Nat.card (Multiplicative (ZMod (exactE τ))) := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rcases hτ with rfl | rfl | rfl
    · exact fun h => hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h)
    · exact hℓ.not_dvd_one
    · exact hℓ.not_dvd_one
  have hker : ¬ ℓ ∣ Nat.card Φ.ker := by
    intro hd
    have h1 := hd.trans hdvd
    rcases hτ with rfl | rfl | rfl
    · rw [det_cartan_E6] at h1
      exact hℓ3 rfl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h1)
    · rw [det_cartan_E7] at h1
      exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h1)
    · rw [det_cartan_E8] at h1
      exact hℓ.not_dvd_one h1
  exact (pRank_top_le_of_coprime_ker hℓ Φ hker).trans (pRank_top_le_one_of_prod hℓ hB)

theorem pRank_outer_le_one_of_twistedE6Model {S : Type} [Group S] [Finite S] {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hm : TwistedChevalleyModel S .E6 (p ^ f)) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) : pRank ℓ (⊤ : Subgroup (Outer S)) ≤ 1 := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .E6 hp hf hm
  have hK' : Nat.card K = (p ^ f) ^ 2 := hK
  have hK2 : Nat.card K = p ^ (2 * f) := by rw [hK', ← pow_mul, mul_comm]
  have : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic hp K hK2).2
  have : Finite (K ≃+* K) := Finite.of_injective (fun σ : K ≃+* K => (σ : K → K))
    DFunLike.coe_injective
  have : Finite (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := Finite.of_equiv S e.toEquiv
  rw [pRank_outer_eq_of_mulEquiv hℓ.one_lt e]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, hcube, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hp hf K hK' σ hσ
  exact pRank_outer_le_one_of_ker_cube_quotient Θ hker le_sup_left hcube hℓ hℓ3

end GL83.I713
