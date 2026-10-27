module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLTwE6B
import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6OddField
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalTwistedE6Main
import CFSG.SignalizerFunctorTheorem.NonLocal.TwistedE6Small

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized
  exists_le_subgroup_card_not_dvd_factorial exists_subgroup_card_not_dvd_factorial
  not_dvd_factorial_of_lt not_pow_dvd_factorial_seventyeight pow_pow_add_mul_eq
  nonLocalized_twisted_of_simple prime_dvd_card_graphFixedRootGroup_E6
  pow_dvd_card_graphFixedRootGroup_E6)
open CFSG.SignalizerFunctorTheorem.NonLocal (nonLocalized_twisted_of_no_small_action
  no_small_faithful_action_E6 exists_pow_ne_self)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic
  finite_field_automorphism_fixed_field_cardinality)
open CFSG.RankThree.Chevalley (subfieldRootGroupImage
  twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer)

section NonLocal

set_option linter.unusedSectionVars false


theorem twE6NonLocalized {ℓ d p : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) (hp : p.Prime) (hp3 : 3 ≤ p)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ (2 * d * p)) (κ σ : K ≃+* K)
    (σ₀ : fixSubfield κ ≃+* fixSubfield κ) (hκ : ∀ c, κ c = c ^ ℓ ^ (2 * d))
    (hσ : ∀ c, σ c = c ^ ℓ ^ (d * p)) (hσ₀ : ∀ c, (σ₀ c : K) = (c : K) ^ ℓ ^ d) :
    NonLocalized ((subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) := by
  classical
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hpos : 0 < 2 * d * p := Nat.mul_pos (Nat.mul_pos (by norm_num) hd) hp.pos
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hpos hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨fr, hfr, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ hpos hK
  obtain ⟨ε, hε⟩ : ∃ ε : K ≃+* K, ∀ c, ε c = c ^ ℓ ^ (d * (p + 1)) :=
    ⟨fr ^ (d * (p + 1)), fun c => ringAut_pow_apply_of_frobenius hfr (d * (p + 1)) c⟩
  obtain ⟨-, hk, hJC, -, -, hsJ, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer hℓ hd hp3 hpodd K hK
      κ hκ σ hσ σ₀ hσ₀ ε hε
  have : Finite (fixSubfield κ) := Subtype.finite
  set C := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hCdef
  set J := subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀ with hJdef
  have hk2 : Nat.card (fixSubfield κ) = (ℓ ^ d) ^ 2 := by rw [hk, ← pow_mul, mul_comm]
  have hσ₀k : ∀ c : fixSubfield κ, σ₀.toRingHom c = c ^ (ℓ ^ d) := fun c =>
    Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hσ₀ c)
  have hsimple : IsSimpleGroup (J.subgroupOf C) :=
    (Subgroup.subgroupOfEquivOfLe hJC).isSimpleGroup
  have hσι : ∀ c : fixSubfield κ, σ.toRingHom ((fixSubfield κ).subtype c) =
      (fixSubfield κ).subtype (σ₀.toRingHom c) := fun c => by
    have hpe : d * p = 2 * d * (p / 2) + d := by
      have h2 := Nat.div_add_mod p 2
      have h3 : p % 2 = 1 := Nat.odd_iff.1 hpodd
      nlinarith [h2, h3]
    have h1 := pow_pow_add_mul_eq (ℓ := ℓ) (m := 2 * d) (k := fixSubfield κ) hk (p / 2) d c
    rw [← hpe] at h1
    have h2 := congrArg Subtype.val h1
    rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow] at h2
    change σ (c : K) = ((σ₀ c : fixSubfield κ) : K)
    rw [hσ, hσ₀]
    exact h2
  have h78 : TwistTag.E6.tag.rank + TwistTag.E6.tag.rootCount = 78 := by decide
  by_cases hsmall : (ℓ = 2 ∨ ℓ = 3) ∧ d = 1
  ·
    obtain ⟨hℓ23, hd1⟩ := hsmall
    subst hd1
    have : CharP (fixSubfield κ) ℓ :=
      (RingHom.charP_iff (fixSubfield κ).subtype (fixSubfield κ).subtype.injective ℓ).mpr
        ‹CharP K ℓ›
    have hk2' : Nat.card (fixSubfield κ) = ℓ ^ 2 := by rw [hk2, pow_one]
    have hσ₀k' : ∀ c : fixSubfield κ, σ₀.toRingHom c = c ^ ℓ := fun c => by
      rw [hσ₀k, pow_one]
    have hσ₀2 : ∀ c : fixSubfield κ, σ₀.toRingHom (σ₀.toRingHom c) = c := fun c => by
      rw [hσ₀k', hσ₀k', ← pow_mul]
      have hmem : (c : K) ∈ fixSubfield κ := c.2
      have h1 : (c : K) ^ ℓ ^ (2 * 1) = c := by rw [← hκ]; exact hmem
      refine Subtype.ext ?_
      rw [SubmonoidClass.coe_pow, show ℓ * ℓ = ℓ ^ (2 * 1) by ring]
      exact h1
    have hne : ∃ u : fixSubfield κ, σ₀.toRingHom u ≠ u := by
      obtain ⟨u, hu⟩ := exists_pow_ne_self (k := fixSubfield κ) hℓ.one_lt hk2'
      exact ⟨u, fun h => hu (by rw [← hσ₀k' u]; exact h)⟩
    have hcases : 78 < Nat.card (fixSubfield κ) ^ 3 ∨
        ((2 : fixSubfield κ) = 0 ∧ 78 < 2 * Nat.card (fixSubfield κ) ^ 3) := by
      rw [hk2']
      rcases hℓ23 with rfl | rfl
      · right
        exact ⟨CharTwo.two_eq_zero, by norm_num⟩
      · left
        norm_num
    exact nonLocalized_twisted_of_no_small_action TwistTag.E6 ℓ (fixSubfield κ).subtype
      σ.toRingHom σ₀.toRingHom σ₀.surjective hσι hsimple
      (fun Λ _ hΛ π hπ => no_small_faithful_action_E6 σ₀.toRingHom hσ₀2 hne hcases
        (by rw [h78] at hΛ; exact hΛ) π hπ)
  ·
    have hcardJ : Nat.card (J.subgroupOf C) = Nat.card (graphFixedRootGroup TwistTag.E6
        (fixSubfield κ) σ₀.toRingHom) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJC).toEquiv).trans
        (Nat.card_congr (Equiv.symm ((graphFixedRootGroup TwistTag.E6 (fixSubfield κ)
          σ₀.toRingHom).equivMapOfInjective
            (baseChangeGL (τ := TwistTag.E6.tag) (fixSubfield κ).subtype)
            (baseChangeGL_injective _)).toEquiv))
    have hR : ∃ R : Subgroup C, R ≤ J.subgroupOf C ∧ ¬ Nat.card R ∣ (78).factorial := by
      refine exists_le_subgroup_card_not_dvd_factorial (J := J.subgroupOf C) ?_
      by_cases h22 : ℓ = 2 ∧ d = 2
      · obtain ⟨rfl, rfl⟩ := h22
        refine exists_subgroup_card_not_dvd_factorial (s := 257) (e := 1) hcardJ (by norm_num)
          ?_ ?_
        · rw [pow_one]
          exact prime_dvd_card_graphFixedRootGroup_E6 hℓ hd (fixSubfield κ) hk2 σ₀.toRingHom
            hσ₀k (by norm_num) (by norm_num) (by decide)
        · rw [pow_one]
          exact not_dvd_factorial_of_lt (by norm_num) (by norm_num)
      · refine exists_subgroup_card_not_dvd_factorial (s := ℓ) (e := 36 * d) hcardJ hℓ
          (pow_dvd_card_graphFixedRootGroup_E6 hℓ hd (fixSubfield κ) hk2 σ₀.toRingHom hσ₀k)
          (not_pow_dvd_factorial_seventyeight hℓ hd (fun h2 => ?_) (fun h3 => ?_))
        · by_contra h
          have hd2 : d = 1 ∨ d = 2 := by omega
          rcases hd2 with h1 | h1
          · exact hsmall ⟨Or.inl h2, h1⟩
          · exact h22 ⟨h2, h1⟩
        · by_contra h
          exact hsmall ⟨Or.inr h3, by omega⟩
    obtain ⟨R, hRJ, hR⟩ := hR
    exact nonLocalized_twisted_of_simple TwistTag.E6 ℓ (fixSubfield κ).subtype σ.toRingHom
      σ₀.toRingHom σ₀.surjective hσι hsimple R hRJ (by rw [h78]; exact hR)

end NonLocal

section Family

set_option linter.unusedSectionVars false


theorem i2015NLResTwE6_holds : I2015NLResTwE6 := by
  intro lab hlab ht
  obtain ⟨t, r, n⟩ := lab
  dsimp only at ht
  subst ht
  have hn : 1 ≤ n := hlab.1
  refine atLabelWhen_of_witness hlab ?_ (fun p _ => by simp)
  intro p hp hp2 _ _ hC Q hQ
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
  have hp3 : p = 3 := hC
  subst hp3
  exact ⟨K, hF, hfin, hK, hQ', fun _ _ _ f hf hord _ _ =>
    nlWitness_twE6_of_nl hn hK hp hp2 le_rfl
      (fun d hd L _ _ hL κ σ σ₀ hκ hσ hσ₀ =>
        twE6NonLocalized Nat.prime_two hd hp le_rfl L hL κ σ σ₀ hκ hσ hσ₀) hf hord⟩

end Family

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
