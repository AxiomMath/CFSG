module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenOuterBase
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Diag
public import CFSG.LieType.Chevalley.TwistedE6RootGroupPerfect
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Descent
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6OddField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (fixSubgroup_pow_eq_of_pow_pow')
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived commutator_le_innAutDerived
  mem_innAutDerived_congr)
open CFSG.RankThree.Chevalley
  (twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer subfieldRootGroupImage)


theorem compsNormal_twE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (β : MulAut (twistedE6RootGroup K σ)) (hβ : β ^ p = 1)
    (hout : β ∉ innAutDerived (twistedE6RootGroup K σ)) : CompsNormal ↥(fixSubgroup β) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  have hη1 : Θ β ≠ 1 := by
    intro h1
    have hmem : β ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
      rw [← hker, MonoidHom.mem_ker]
      exact h1
    exact hout (commutator_le_innAutDerived _
      (CFSG.HardMathSupport.Dickson.Sec6.I923.twistedE6Inndiag_le_commutator σ hK hσ
        (commutator_twistedE6RootGroup_eq_top hℓ hf hK σ hσ) hmem))
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨d, hd, hd1, r, s, T, ε, hT, hε, hrs, ψ, hψ, -⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_data_of_prime_order hℓ hf K hK'
      σ hσ Θ hΘ hp hp2 β hβ hη1
  have hdp : d * p = f := by rw [hd, mul_comm]
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 2 * f) hK'
  obtain ⟨κ, hκ⟩ : ∃ κ : K ≃+* K, ∀ c, κ c = c ^ ℓ ^ (2 * d) :=
    ⟨fr ^ (2 * d), fun c => ringAut_pow_apply_of_frobenius hfr (2 * d) c⟩
  have hKdp : Nat.card K = ℓ ^ (2 * d * p) := by rw [hK', mul_assoc, hdp]
  have hσdp : ∀ c, σ c = c ^ ℓ ^ (d * p) := fun c => by rw [hσ, hdp]
  have hσ₀ : ∀ c : fixSubfield κ, (fixSubfieldRestrict T κ c : K) = (c : K) ^ ℓ ^ d :=
    fun c => by rw [coe_fixSubfieldRestrict, hT]
  have hm3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨-, -, hJC, -, hder, hsimpleJ, hncJ, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer
      hℓ hd1 hm3 (hp.odd_of_ne_two hp2) K hKdp κ hκ σ hσdp (fixSubfieldRestrict T κ) hσ₀ ε hε
  set C := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hC
  set J := subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ)
    with hJdef
  haveI : Finite C := Subtype.finite
  have eJC : J.subgroupOf C ≃* J := Subgroup.subgroupOfEquivOfLe hJC
  haveI := hsimpleJ
  have hJs : IsSimpleGroup (J.subgroupOf C) := eJC.isSimpleGroup
  have hJn : ∃ x y : J.subgroupOf C, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    apply hncJ
    intro a b
    have h := hcon (eJC.symm a) (eJC.symm b)
    apply eJC.symm.injective
    rw [map_mul, map_mul]
    exact h
  have hδ : CompsNormal ↥(fixSubgroup (fieldActor (t := TwistTag.E6) σ ε)) :=
    compsNormal_fixSubgroup_of_derived_eq_simple hder hJs hJn
  have hr : CompsNormal ↥(fixSubgroup (β ^ r)) := by
    refine compsNormal_fixSubgroup_of_conj ψ (β ^ r) ?_
    rw [hψ]
    exact hδ
  exact compsNormal_fixSubgroup_of_eq (fixSubgroup_pow_eq_of_pow_pow' hrs) hr


theorem compsNormal_twE6_cat (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) {S : Type} [Group S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (β : MulAut S) (hβ : β ^ p = 1) (hout : β ∉ innAutDerived S) :
    CompsNormal ↥(fixSubgroup β) := by
  classical
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  let e' : S ≃* ↥(twistedE6RootGroup K σ) := e.trans eK
  refine compsNormal_fixSubgroup_of_congr e' ?_
  have hβ' : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hout' : MulAut.congr e' β ∉ innAutDerived ↥(twistedE6RootGroup K σ) := fun h =>
    hout ((mem_innAutDerived_congr e').1 h)
  exact compsNormal_twE6 q.prime_p q.exponent_pos hK σ hσ hp hp2 _ hβ' hout'

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
