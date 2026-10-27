module

public import CFSG.CharacterTheory.Wreathed.CentralSylowPowerQuotients
public import CFSG.CharacterTheory.Wreathed.FourPointCompleteModelCharacters

public noncomputable section

namespace CFSG.Wreathed.FourPointOrderFour

open CFSG.TwoRankLowerBound.Helpers
open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.FourPointCompleteModel

open scoped Classical

variable {G : Type} [Group G]

abbrev orderFourCentralizer (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : Subgroup G :=
  Subgroup.centralizer {wreathModelHom S e (Original.a (2 ^ n))}

theorem orderFourCentralizer_eq (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    orderFourCentralizer n S e = centralSylowPowerCentralizer n S e 1 := by
  rw [centralSylowPowerCentralizer, zpow_one]

theorem orderFourCentralizer_le (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    orderFourCentralizer n S e ≤ involutionCentralizer n S e := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  change g ∈ Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))}
  rw [Subgroup.mem_centralizer_singleton_iff, wreathModelHom_x_eq]
  exact (Commute.pow_right (show Commute g _ from hg) _).eq

@[expose] def orderFourMap (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    orderFourCentralizer n S e →* centralizerOddCoreQuotient n S e :=
  (centralizerOddCoreMap n S e).comp (Subgroup.inclusion (orderFourCentralizer_le n S e))

theorem orderFourMap_apply (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (c : orderFourCentralizer n S e) :
    orderFourMap n S e c =
      centralizerOddCoreMap n S e (Subgroup.inclusion (orderFourCentralizer_le n S e) c) :=
  rfl

theorem two_pow_not_dvd_one {n : ℕ} (hn : 1 ≤ n) : ¬ ((2 ^ n : ℕ) : ℤ) ∣ 1 := by
  intro h
  have h1 : ((2 ^ n : ℕ) : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h
  have h2 : 2 ^ n = 1 := by exact_mod_cast h1
  exact absurd h2 (Nat.one_lt_two_pow (by omega)).ne'

section Transfer

variable [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

include hn in
theorem orderFour_factorization (g : involutionCentralizer n S e) :
    ∃ r ∈ centralizerOddCore n S e, ∃ c : involutionCentralizer n S e,
      (c : G) ∈ orderFourCentralizer n S e ∧ g = r * c := by
  rw [orderFourCentralizer_eq]
  exact involutionCentralizer_eq_oddCore_mul_centralSylowPower n hn S e 1 g

include hn in
theorem orderFourMap_surjective : Function.Surjective (orderFourMap n S e) := by
  intro h
  obtain ⟨g, rfl⟩ := centralizerOddCoreMap_surjective n S e h
  obtain ⟨r, hr, c, hc, rfl⟩ := orderFour_factorization n hn S e g
  refine ⟨⟨c, hc⟩, ?_⟩
  have hr1 : centralizerOddCoreMap n S e r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
  rw [map_mul, hr1, one_mul]
  rfl

include hn in
theorem orderFourMap_ker :
    (orderFourMap n S e).ker = CFSG.oddCore (orderFourCentralizer n S e) := by
  have key : ∀ (C : Subgroup G), C = centralSylowPowerCentralizer n S e 1 →
      ∀ hCN : C ≤ involutionCentralizer n S e,
        ((centralizerOddCoreMap n S e).comp (Subgroup.inclusion hCN)).ker = CFSG.oddCore C := by
    rintro C rfl hCN
    exact centralSylowPowerMap_ker n hn S e 1 (two_pow_not_dvd_one (by omega))
  exact key _ (orderFourCentralizer_eq n S e) _

include hn in
theorem orderFour_oddCore_inf :
    (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓
        orderFourCentralizer n S e =
      (CFSG.oddCore (orderFourCentralizer n S e)).map (orderFourCentralizer n S e).subtype := by
  have key : ∀ (C : Subgroup G), C = centralSylowPowerCentralizer n S e 1 →
      (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓ C =
        (CFSG.oddCore C).map C.subtype := by
    rintro C rfl
    exact centralizerOddCore_inf_centralSylowPower n hn S e 1 (two_pow_not_dvd_one (by omega))
  exact key _ (orderFourCentralizer_eq n S e)

include hn in
theorem orderFourMap_ker_map :
    (orderFourMap n S e).ker.map (orderFourCentralizer n S e).subtype =
      (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓
        orderFourCentralizer n S e := by
  rw [orderFourMap_ker n hn S e, orderFour_oddCore_inf n hn S e]

include hn in
theorem orderFourMap_ker_odd : Odd (Nat.card (orderFourMap n S e).ker) := by
  rw [orderFourMap_ker n hn S e]
  exact CFSG.ComponentClassification.OddCore.odd_card _

include hn in
theorem exists_orderFour_quotient_equiv :
    ∃ η : orderFourCentralizer n S e ⧸ CFSG.oddCore (orderFourCentralizer n S e) ≃*
        centralizerOddCoreQuotient n S e,
      ∀ c : orderFourCentralizer n S e, η c = orderFourMap n S e c :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (orderFourMap_ker n hn S e).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (orderFourMap_surjective n hn S e)),
    fun _ => rfl⟩

omit [Finite G] in
theorem card_involutionCentralizer_eq :
    Nat.card (involutionCentralizer n S e) =
      Nat.card (centralizerOddCoreQuotient n S e) * Nat.card (centralizerOddCore n S e) :=
  Subgroup.card_eq_card_quotient_mul_card_subgroup (centralizerOddCore n S e)

include hn in
theorem card_orderFourCentralizer_eq :
    Nat.card (orderFourCentralizer n S e) = Nat.card (centralizerOddCoreQuotient n S e) *
      Nat.card ((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓
        orderFourCentralizer n S e : Subgroup G) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (orderFourMap n S e).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (orderFourMap_surjective n hn S e)).toEquiv,
    ← orderFourMap_ker_map n hn S e,
    Subgroup.card_map_of_injective (orderFourCentralizer n S e).subtype_injective]

end Transfer

section Element

variable (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

theorem orderOf_centralizerModelHom_a :
    orderOf (wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
      (Original.a (2 ^ n))) = 2 ^ n := by
  rw [← Subgroup.orderOf_coe, centralizerModelHom_coe, orderOf_wreathModelHom_a]

theorem centralizerModelHom_a_pow :
    wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
      (Original.a (2 ^ n)) ^ (2 ^ n / 2) = centralInvolution n S e := by
  rw [← map_pow]
  rfl

theorem centralizerModelHom_a_mem_fullCenterImage :
    centralizerOddCoreMap n S e (wreathModelHom (centralizerSylow n hn S e)
      (centralizerCoordinates n hn S e) (Original.a (2 ^ n))) ∈
        centralizerFullCenterImage n hn S e := by
  apply Subgroup.mem_map_of_mem
  rw [centralizerFullCenter_eq_zpowers]
  exact Subgroup.mem_zpowers _

theorem orderOf_centralizerOddCoreMap_a [Finite G] :
    orderOf (centralizerOddCoreMap n S e (wreathModelHom (centralizerSylow n hn S e)
      (centralizerCoordinates n hn S e) (Original.a (2 ^ n)))) = 2 ^ n := by
  rw [← Nat.card_zpowers, ← MonoidHom.map_zpowers, ← centralizerFullCenter_eq_zpowers]
  exact centralizerFullCenterImage_card n hn S e

include hn in
theorem not_isConj_a_inv [Finite G] :
    ¬ IsConj (wreathModelHom S e (Original.a (2 ^ n)))
      (wreathModelHom S e (Original.a (2 ^ n)))⁻¹ := by
  intro hconj
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  set aN := wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
    (Original.a (2 ^ n)) with haN
  have haG : (aN : G) = wreathModelHom S e (Original.a (2 ^ n)) := rfl
  have hord : orderOf (wreathModelHom S e (Original.a (2 ^ n))) = 2 ^ n :=
    orderOf_wreathModelHom_a n S e
  have hk : 2 ^ n / 2 + 2 ^ n / 2 = 2 ^ n := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    ring
  have hx : c * wreathModelHom S e (Original.x (2 ^ n)) * c⁻¹ =
      wreathModelHom S e (Original.x (2 ^ n)) := by
    have hpow : wreathModelHom S e (Original.a (2 ^ n)) ^ (2 ^ n) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hord)
    rw [wreathModelHom_x_eq, ← conj_pow, hc, inv_pow]
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, hk, hpow]
  have hcN : c ∈ involutionCentralizer n S e := by
    change c ∈ Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))}
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp hx
  set cN : involutionCentralizer n S e := ⟨c, hcN⟩
  have hcN' : cN * aN * cN⁻¹ = aN⁻¹ := Subtype.ext hc
  have hcent : centralizerOddCoreMap n S e aN ∈
      Subgroup.center (centralizerOddCoreQuotient n S e) := by
    rw [centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e]
    exact centralizerModelHom_a_mem_fullCenterImage n hn S e
  have himage := congrArg (centralizerOddCoreMap n S e) hcN'
  rw [map_mul, map_mul, map_inv, map_inv,
    (Subgroup.mem_center_iff.mp hcent (centralizerOddCoreMap n S e cN)), mul_inv_cancel_right]
    at himage
  have hsq : centralizerOddCoreMap n S e aN ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [himage]
    exact mul_inv_cancel _
  have hdvd := orderOf_dvd_of_pow_eq_one hsq
  rw [orderOf_centralizerOddCoreMap_a n hn S e] at hdvd
  have h4 : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 hn
  have := Nat.le_of_dvd (by norm_num) (h4.trans hdvd)
  norm_num at this

end Element

theorem eq_one_of_odd_of_dvd_two_pow {k d : ℕ} (hk : Odd k) (hdvd : k ∣ d) (j : ℕ)
    (hd : d = 2 ^ j) : k = 1 :=
  Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hk)) (hd ▸ hdvd)

theorem orderOf_eq_of_isConj {K : Type*} [Group K] {g h : K} (hgh : IsConj g h) :
    orderOf g = orderOf h := by
  obtain ⟨c, hc⟩ := hgh
  exact SemiconjBy.orderOf_eq _ hc

theorem fourPointModel_odd_classes :
    let U₀ := specialInclusion (ZMod 3) twoUnit 4 (by norm_num) (by decide)
      (CentralSL2.upperSL (ZMod 3) 1)
    orderOf U₀ = 3 ∧ (∀ g : CentralExtension (ZMod 3) twoUnit 4 (by norm_num) (by decide),
      g ≠ 1 → Odd (orderOf g) → IsConj g U₀) ∧
      Nat.card (Subgroup.centralizer {U₀}) = 12 := by
  intro U₀
  obtain ⟨y, hy⟩ := exists_unit_mul_frobenius_eq_neg_one
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hAcard, -, htypes, -, -, -, -, -, hcentU, -,
      hcomm, -, -, -, hTplus, -, -, hTminus, -⟩ :=
    CentralSL2.base_conjugacy_classes_and_centralizers (F := ZMod 3) Nat.prime_three ⟨1, rfl⟩
      le_rfl (by rw [Nat.card_zmod]; norm_num) twoUnit twoUnit_not_isSquare 4 (by norm_num)
      (by decide) (GaloisField 3 2) galoisBasis y hy
  rw [Nat.card_zmod] at hcentU hTplus hTminus
  have hU : U₀ = CentralSL2.unipotentElement (ZMod 3) twoUnit 4 (by norm_num) (by decide) 1 :=
    rfl
  have hU0 : CentralSL2.unipotentElement (ZMod 3) twoUnit 4 (by norm_num) (by decide) 0 = 1 :=
    CentralSL2.unipotentElement_zero _ _ _ _ _
  have hU3 : U₀ ^ 3 = 1 := by
    rw [hU, CentralSL2.unipotentElement_pow, show ((3 : ℕ) : ZMod 3) * 1 = 0 by decide, hU0]
  have hU1 : U₀ ≠ 1 := by
    intro h
    rw [hU, ← hU0] at h
    exact absurd (CentralSL2.unipotentElement_injective h) (by decide)
  have hord : orderOf U₀ = 3 := orderOf_eq_prime hU3 hU1
  refine ⟨hord, ?_, ?_⟩
  · intro g hg hodd
    rcases htypes g with hA | ⟨α, hα, hconj⟩ | ⟨t, ht, htA, hconj⟩ | ⟨t, ht, htA, hconj⟩
    · exfalso
      have hdvd := Subgroup.orderOf_dvd_natCard _ hA
      rw [hAcard] at hdvd
      exact hg (orderOf_eq_one_iff.mp (eq_one_of_odd_of_dvd_two_pow hodd hdvd 2 (by norm_num)))
    ·
      rw [← hU] at hconj
      have hcU : Commute α U₀ := hcomm α hα 1
      have hodd' : Odd (orderOf (α * U₀)) := by
        rw [← orderOf_eq_of_isConj hconj]
        exact hodd
      have hcube : (α * U₀) ^ 3 = α ^ 3 := by rw [hcU.mul_pow, hU3, mul_one]
      have hα3odd : Odd (orderOf (α ^ 3)) := by
        rw [← hcube]
        exact hodd'.of_dvd_nat (orderOf_pow_dvd 3)
      have hα3dvd := Subgroup.orderOf_dvd_natCard _ (Subgroup.pow_mem _ hα 3)
      rw [hAcard] at hα3dvd
      have hα3 : α ^ 3 = 1 :=
        orderOf_eq_one_iff.mp (eq_one_of_odd_of_dvd_two_pow hα3odd hα3dvd 2 (by norm_num))
      have hα4dvd := Subgroup.orderOf_dvd_natCard _ hα
      rw [hAcard] at hα4dvd
      have hα4 : α ^ 4 = 1 := orderOf_dvd_iff_pow_eq_one.mp hα4dvd
      have hα1 : α = 1 := by
        rw [show α ^ 4 = α ^ 3 * α from pow_succ α 3, hα3, one_mul] at hα4
        exact hα4
      rw [hα1, one_mul] at hconj
      exact hconj
    · exfalso
      have hodd' : Odd (orderOf t) := by
        rw [← orderOf_eq_of_isConj hconj]
        exact hodd
      have hdvd := Subgroup.orderOf_dvd_natCard _ ht
      rw [hTplus] at hdvd
      exact htA ((orderOf_eq_one_iff.mp (eq_one_of_odd_of_dvd_two_pow hodd' hdvd 3
        (by norm_num))) ▸ Subgroup.one_mem _)
    · exfalso
      have hodd' : Odd (orderOf t) := by
        rw [← orderOf_eq_of_isConj hconj]
        exact hodd
      have hdvd := Subgroup.orderOf_dvd_natCard _ ht
      rw [hTminus] at hdvd
      exact htA ((orderOf_eq_one_iff.mp (eq_one_of_odd_of_dvd_two_pow hodd' hdvd 4
        (by norm_num))) ▸ Subgroup.one_mem _)
  · have h := hcentU 1 (Subgroup.one_mem _)
    rw [one_mul] at h
    exact h

theorem card_centralizer_map_equiv {K L : Type*} [Group K] [Group L] (Φ : K ≃* L) (w : K) :
    Nat.card (Subgroup.centralizer {Φ w}) = Nat.card (Subgroup.centralizer {w}) := by
  have h : Subgroup.centralizer {Φ w} = (Subgroup.centralizer {w}).map Φ.toMonoidHom := by
    ext l
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map_equiv,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hl
      apply Φ.injective
      simp [hl]
    · intro hl
      have h2 := congrArg Φ hl
      simpa using h2
  rw [h, Subgroup.card_map_of_injective Φ.injective]

theorem odd_classes_of_equiv {K : Type*} [Group K]
    (Φ : CentralExtension (ZMod 3) twoUnit 4 (by norm_num) (by decide) ≃* K) :
    let v := Φ (specialInclusion (ZMod 3) twoUnit 4 (by norm_num) (by decide)
      (CentralSL2.upperSL (ZMod 3) 1))
    orderOf v = 3 ∧ (∀ g : K, g ≠ 1 → Odd (orderOf g) → IsConj g v) ∧
      Nat.card (Subgroup.centralizer {v}) = 12 := by
  intro v
  obtain ⟨hord, hconj, hcent⟩ := fourPointModel_odd_classes
  refine ⟨(MulEquiv.orderOf_eq Φ _).trans hord, fun g hg hodd => ?_,
    (card_centralizer_map_equiv Φ _).trans hcent⟩
  have hg' : Φ.symm g ≠ 1 := by
    rwa [Ne, map_eq_one_iff _ Φ.symm.injective]
  have hodd' : Odd (orderOf (Φ.symm g)) := by
    rwa [MulEquiv.orderOf_eq]
  have h := MonoidHom.map_isConj Φ.toMonoidHom (hconj _ hg' hodd')
  simpa using h

theorem coefficientBlock_eq_univ_of_equiv {K L : Type} [Group K] [Fintype K] [Group L]
    (η : K ≃* L) (Q : Subgroup L) [Q.Normal] (hQ : IsPGroup 2 Q)
    (hcent : Subgroup.centralizer (Q : Set L) ≤ Q) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis K) (label : basis.index) :
    coefficientBlock basis (localizedComplexIntegerRing ideal) label = Finset.univ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (Q.comap η.toMonoidHom).Normal := Subgroup.normal_comap _
  have hp : IsPGroup 2 (Q.comap η.toMonoidHom) := hQ.comap_of_injective _ η.injective
  have hc : Subgroup.centralizer ((Q.comap η.toMonoidHom : Subgroup K) : Set K) ≤
      Q.comap η.toMonoidHom := by
    intro g hg
    rw [Subgroup.mem_comap]
    apply hcent
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : η.symm q ∈ Q.comap η.toMonoidHom := by
      rw [Subgroup.mem_comap]
      simpa using hq
    have h := congrArg η (Subgroup.mem_centralizer_iff.mp hg _ hq')
    simpa using h
  exact (CFSG.Wreathed.selfcentralizing_unique_block 2 _ hp hc ideal basis).2.1 label

end CFSG.Wreathed.FourPointOrderFour
