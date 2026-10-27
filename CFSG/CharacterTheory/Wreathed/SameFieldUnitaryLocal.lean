module

public import CFSG.CharacterTheory.Wreathed.SameFieldUnitaryModel
public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchCore
public import CFSG.CharacterTheory.Semidihedral.SimpleLayerFrontierLinear
public import CFSG.CharacterTheory.Wreathed.ComponentCoverConfinement
public import CFSG.CharacterTheory.Wreathed.PrimewiseConfinedCentralCore

public section

open scoped Classical

namespace CFSG.Wreathed.SameFieldUnitary

open CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.OriginalStationarityCoverageCriterion
  CFSG.Wreathed.SmallerRecognitionOriginalField CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.Wreathed.CentralSL2 CFSG.Wreathed.PrimewiseConfinedCentralCore

section Transport

variable {G : Type*} [Group G] {N : Subgroup G} {R JS : Subgroup N} {W : Type*} [Group W]

noncomputable def productEmbedding (μ : R × JS ≃* N) (eH : JS ≃* W) : R × W →* G :=
  N.subtype.comp ((MulEquiv.prodCongr (MulEquiv.refl R) eH.symm).trans μ).toMonoidHom

theorem productEmbedding_injective (μ : R × JS ≃* N) (eH : JS ≃* W) :
    Function.Injective (productEmbedding μ eH) :=
  N.subtype_injective.comp (MulEquiv.injective _)

theorem productEmbedding_mem (μ : R × JS ≃* N) (eH : JS ≃* W) (z : R × W) :
    productEmbedding μ eH z ∈ N :=
  (((MulEquiv.prodCongr (MulEquiv.refl R) eH.symm).trans μ) z).2

theorem exists_productEmbedding_eq (μ : R × JS ≃* N) (eH : JS ≃* W) {g : G} (hg : g ∈ N) :
    ∃ z, productEmbedding μ eH z = g :=
  ⟨((MulEquiv.prodCongr (MulEquiv.refl R) eH.symm).trans μ).symm ⟨g, hg⟩, by
    simp [productEmbedding]⟩

theorem productEmbedding_apply (μ : R × JS ≃* N) (hμ : ∀ z : R × JS, μ z = (z.1 : N) * z.2)
    (eH : JS ≃* W) (z : R × W) :
    productEmbedding μ eH z = ((z.1 : N) : G) * ((eH.symm z.2 : JS) : N) := by
  simp [productEmbedding, hμ]
  rfl

theorem productEmbedding_center (μ : R × JS ≃* N) (eH : JS ≃* W) {x : G} (hx : x ∈ N)
    (hxc : ∀ g ∈ N, g * x = x * g) :
    ∃ z ∈ Subgroup.center (R × W), productEmbedding μ eH z = x := by
  obtain ⟨z, rfl⟩ := exists_productEmbedding_eq μ eH hx
  refine ⟨z, Subgroup.mem_center_iff.mpr fun w => ?_, rfl⟩
  apply productEmbedding_injective μ eH
  rw [map_mul, map_mul]
  exact hxc _ (productEmbedding_mem μ eH w)

end Transport

theorem card_eq_of_unitary_order {g r m q : ℕ} (hq : 1 ≤ q)
    (h : (g : ℤ) = r * m * (q : ℤ) ^ 3 * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 2 + -1 * q + 1)) :
    g = r * m * q ^ 3 * (q - 1) * (q ^ 3 + 1) := by
  zify [hq]
  rw [h]
  ring

theorem dvd_add_one_of_dvd_div {r n q : ℕ} (h2 : 2 ^ n ∣ q + 1)
    (h : (r : ℤ) ∣ ((q : ℕ) - (-1 : ℤ)) / ((2 ^ n : ℕ) : ℤ)) : r ∣ q + 1 := by
  obtain ⟨c, hc⟩ := h2
  have hq : ((q : ℕ) - (-1 : ℤ)) / ((2 ^ n : ℕ) : ℤ) = (c : ℤ) := by
    rw [sub_neg_eq_add, show ((q : ℤ) + 1) = ((q + 1 : ℕ) : ℤ) by push_cast; ring, hc]
    push_cast
    exact Int.mul_ediv_cancel_left _ (by positivity)
  rw [hq] at h
  rw [hc]
  exact Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mp h) _

theorem exists_centralizer_data
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrec : SmallerWreathedRecognition G)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq5 : 5 ≤ p ^ f)
    (hq3 : p ^ f % 4 = 3)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    (hst : OriginalAllPrimeStationarity n S e) (hcov : OriginalAllPrimeCoverage n S e) :
    let x : G := wreathModelHom S e (Original.x (2 ^ n))
    ∃ K : Subgroup G, Nat.card K = Nat.card (centralizerOddCore n S e) * 2 ^ n ∧ x ∈ K ∧
      (∀ r ∈ K, ∀ g ∈ Subgroup.centralizer {x}, g * r = r * g) ∧ ¬ p ∣ Nat.card K ∧
      (∀ r ∈ K, r ≠ 1 → Subgroup.centralizer {r} ≤ Subgroup.centralizer {x}) ∧
      (S : Subgroup G) ≤ Subgroup.centralizer {x} ∧
      Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ Subgroup.centralizer {x} ∧
      ∃ Q₀ : Subgroup G, Nat.card Q₀ = p ^ f ∧ (∀ a ∈ Q₀, ∀ b ∈ Q₀, a * b = b * a) ∧
        Q₀ ≤ Subgroup.centralizer {x} ∧ ¬ p ∣ Q₀.relIndex (Subgroup.centralizer {x}) ∧
      ∃ H : Subgroup G, H ≤ Subgroup.normalizer (Q₀ : Set G) ∧ IsCyclic H ∧ K ≤ H ∧
        Nat.card H = (p ^ f - 1) * Nat.card K ∧
        Nat.card G = Nat.card K * (p ^ f) ^ 3 * (p ^ f - 1) * ((p ^ f) ^ 3 + 1) := by
  intro x
  have hp2 : p ≠ 2 := fun h => by rw [h] at hpodd; exact (Nat.not_odd_iff_even.mpr even_two) hpodd
  have hconf :=
    ComponentCoverConfinement.stationarity_and_original_coverage_confine_all_odd_core_elements
      hnonab n hn S e hfour p f hp hpodd hf hq5 hmodel hrec hst hcov
  obtain ⟨-, -, -, -, hRcyc, hRcent, hRdvd, -, ⟨F, hF, hFfin, Sigma, b, hSigma, ρ, Ψ, hdata⟩, hall,
      hNcard, hGcard, -, JS, -, ⟨μ, hμ⟩, ⟨φ, hφ⟩⟩ :=
    original_primewise_coverage_and_confinement_give_central_cyclic_odd_core
      hnonab n hn S e hfour p f hp hp2 hf hmodel hcov (fun r hr hr1 => (hconf r hr hr1).1)
  have hSig : Nat.card Sigma = 1 := hall F Sigma b hSigma ρ Ψ hdata
  have : Subsingleton Sigma := (Nat.card_eq_one_iff_unique.mp hSig).1
  let eW := CFSG.Semidihedral.SimpleLayerFrontier.semidirectProductTrivialRightEquiv
    (fieldAction F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma)
  let eH := φ.trans (Ψ.symm.trans eW.symm)
  have hε : (if p ^ f % 4 = 1 then (1 : ℤ) else -1) = -1 := by simp [hq3]
  rw [hε] at hRdvd hGcard
  have htwo := NormalComponentLift.two_pow_eq_two_part (n := n) (hn := hn) (S := S) (e := e)
    hnonab hfour hp hp2 hf hmodel
  rw [hε] at htwo
  set q := p ^ f with hqdef
  have hq1 : 1 ≤ q := by omega
  have h2q : 2 ^ n ∣ q + 1 := by
    have h := padicValInt_dvd (p := 2) ((q : ℕ) - (-1 : ℤ))
    have h' : ((2 ^ n : ℕ) : ℤ) ∣ ((q + 1 : ℕ) : ℤ) := by
      rw [htwo]
      push_cast
      simpa using h
    exact Int.natCast_dvd_natCast.mp h'
  have hRq : Nat.card (centralizerOddCore n S e) ∣ q + 1 := dvd_add_one_of_dvd_div h2q hRdvd
  have hRodd : Odd (Nat.card (centralizerOddCore n S e)) := centralizerOddCore_card_odd n S e
  have hb : ¬ IsSquare b := hdata.nonsquare
  have hFq : Nat.card F = q := hdata.card
  have hF3 : Nat.card F % 4 = 3 := by rw [hFq]; exact hq3
  have h2F : (2 : F) ≠ 0 := two_ne_zero_of_not_isSquare hb
  let N := involutionCentralizer n S e
  let R := centralizerOddCore n S e
  let W := CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
  set Φ := productEmbedding μ eH with hΦ
  have hΦinj : Function.Injective Φ := productEmbedding_injective μ eH
  set ZW : Subgroup W := Subgroup.zpowers (cyclicGenerator F b (2 ^ n) (wreathModulus_pos n)
    (wreathModulus_even hn) ^ 2) with hZW
  set T : Subgroup W := splitTorus F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
    with hT
  set U : Subgroup W := unipotentSubgroup F b (2 ^ n) (wreathModulus_pos n)
    (wreathModulus_even hn) with hU
  have hZWcard : Nat.card ZW = 2 ^ n := by
    rw [hZW, Nat.card_zpowers, orderOf_cyclicGenerator_sq F b _ _ _ h2F]
  have hTcard : Nat.card T = 2 ^ n * (q - 1) := by rw [hT, card_splitTorus, hFq]
  have hUcard : Nat.card U = q := by rw [hU, card_unipotentSubgroup, hFq]
  have hZWT : ZW ≤ T := by
    rw [hZW, Subgroup.zpowers_le]
    exact cyclicGenerator_sq_mem_splitTorus F b _ _ _
  have hcenter : Subgroup.center W = ZW := CFSG.Wreathed.CentralSL2.center_eq_zpowers hb
  have hRcomm : ∀ a b : R, a * b = b * a := fun a b => IsCyclic.commGroup.mul_comm a b
  have hxN : x ∈ N := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hxord : orderOf x = 2 := CompatibleFamilies.orderOf_x S e hn
  set K₀ : Subgroup (R × W) := (⊤ : Subgroup R).prod ZW with hK₀
  have hK₀center : K₀ ≤ Subgroup.center (R × W) := by
    rintro z ⟨-, hz2⟩
    rw [Subgroup.center_prod]
    refine ⟨Subgroup.mem_center_iff.mpr fun a => hRcomm a z.1, ?_⟩
    rw [hcenter]
    exact hz2
  have hK₀card : Nat.card K₀ = Nat.card R * 2 ^ n := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_top,
      hZWcard]
  set K : Subgroup G := K₀.map Φ with hK
  have hKcard : Nat.card K = Nat.card R * 2 ^ n := by
    rw [hK, Subgroup.card_map_of_injective hΦinj, hK₀card]
  have hpq : ¬ p ∣ q + 1 := by
    intro h
    have hpq' : p ∣ q := dvd_pow_self p (by omega)
    have := (Nat.dvd_add_right hpq').mp h
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hp2n : ¬ p ∣ 2 ^ n := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hpR : ¬ p ∣ Nat.card R := fun h => hpq (h.trans hRq)
  have hRT : Nat.Coprime (Nat.card R) (2 ^ n * (q - 1)) := by
    apply Nat.Coprime.mul_right
    · exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hRodd)
    · rw [Nat.coprime_iff_gcd_eq_one]
      have h1 : Nat.gcd (Nat.card R) (q - 1) ∣ 2 := by
        have ha : Nat.gcd (Nat.card R) (q - 1) ∣ q + 1 := (Nat.gcd_dvd_left _ _).trans hRq
        have hb' : Nat.gcd (Nat.card R) (q - 1) ∣ q - 1 := Nat.gcd_dvd_right _ _
        have := Nat.dvd_sub ha hb'
        rwa [show q + 1 - (q - 1) = 2 by omega] at this
      have h2 : Odd (Nat.gcd (Nat.card R) (q - 1)) :=
        hRodd.of_dvd_nat (Nat.gcd_dvd_left _ _)
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact h
      · rw [h] at h2
        exact absurd h2 (by decide)
  have hxK : x ∈ K := by
    obtain ⟨z, hz, hzx⟩ := productEmbedding_center μ eH hxN
      (fun g hg => Subgroup.mem_centralizer_singleton_iff.mp hg)
    rw [Subgroup.center_prod, hcenter] at hz
    exact ⟨z, ⟨Subgroup.mem_top _, hz.2⟩, hzx⟩
  have hKcent : ∀ r ∈ K, ∀ g ∈ N, g * r = r * g := by
    rintro _ ⟨z, hz, rfl⟩ g hg
    obtain ⟨w, rfl⟩ := exists_productEmbedding_eq μ eH hg
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hK₀center hz) w]
  have hK₀cyc : IsCyclic K₀ := by
    have hprod : IsCyclic ((⊤ : Subgroup R) × ZW) := by
      rw [Group.isCyclic_prod_iff]
      refine ⟨?_, inferInstance, ?_⟩
      · exact isCyclic_of_surjective (Subgroup.topEquiv (G := R)).symm.toMonoidHom
          (Subgroup.topEquiv (G := R)).symm.surjective
      · rw [Subgroup.card_top, hZWcard]
        exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hRodd)
    exact isCyclic_of_surjective (Subgroup.prodEquiv _ _).symm.toMonoidHom
      (Subgroup.prodEquiv _ _).symm.surjective
  have hKcyc : IsCyclic K :=
    isCyclic_of_surjective (Subgroup.equivMapOfInjective K₀ Φ hΦinj).toMonoidHom
      (Subgroup.equivMapOfInjective K₀ Φ hΦinj).surjective
  have hKconf : ∀ r ∈ K, r ≠ 1 → Subgroup.centralizer {r} ≤ N := by
    intro r hr hr1
    by_cases hodd : Odd (orderOf r)
    · obtain ⟨z, hz, rfl⟩ := hr
      have hz2 : z.2 = 1 := by
        have h1 : orderOf z.2 ∣ orderOf z := by
          rw [Prod.orderOf]
          exact Nat.dvd_lcm_right _ _
        have h2 : orderOf z.2 ∣ 2 ^ n := by
          have h := orderOf_dvd_natCard (⟨z.2, hz.2⟩ : ZW)
          rw [hZWcard, Subgroup.orderOf_mk] at h
          exact h
        rw [orderOf_injective Φ hΦinj] at hodd
        have h3 : Odd (orderOf z.2) := hodd.of_dvd_nat h1
        obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
        rw [hi] at h3
        rcases i with _ | i
        · rw [pow_zero, orderOf_eq_one_iff] at hi
          exact hi
        · rw [pow_succ] at h3
          exact absurd h3 (Nat.not_odd_iff_even.mpr (even_two.mul_left _))
      have hzR : Φ z ∈ R.map N.subtype := by
        rw [productEmbedding_apply μ hμ eH z, hz2, map_one]
        simp only [OneMemClass.coe_one, mul_one]
        exact ⟨z.1, z.1.2, rfl⟩
      exact (hconf _ hzR hr1).2
    · set k := orderOf r with hk
      have hkpos : 0 < k := orderOf_pos r
      have hk2 : 2 ∣ k := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
      have hy : orderOf (r ^ (k / 2)) = 2 := orderOf_pow_orderOf_div hkpos.ne' hk2
      have hyK : r ^ (k / 2) ∈ K := K.pow_mem hr _
      have heq : (⟨r ^ (k / 2), hyK⟩ : K) = ⟨x, hxK⟩ := by
        apply CFSG.Semidihedral.UnitaryBranch.eq_of_sq_eq_one_of_isCyclic
        · apply Subtype.ext
          simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
          have h := pow_orderOf_eq_one (r ^ (k / 2))
          rwa [hy] at h
        · intro h
          have := congrArg Subtype.val h
          simp only [OneMemClass.coe_one] at this
          rw [this, orderOf_one] at hy
          exact absurd hy (by norm_num)
        · apply Subtype.ext
          simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
          have h := pow_orderOf_eq_one x
          rwa [hxord] at h
        · intro h
          have := congrArg Subtype.val h
          simp only [OneMemClass.coe_one] at this
          rw [this, orderOf_one] at hxord
          exact absurd hxord (by norm_num)
      have hxr : x = r ^ (k / 2) := (congrArg Subtype.val heq).symm
      intro g hg
      show g ∈ Subgroup.centralizer {x}
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      rw [hxr]
      exact ((Commute.pow_left (Commute.symm hg) (k / 2)).symm).eq
  have hSN : (S : Subgroup G) ≤ N := sylow_le_involutionCentralizer n hn S e
  have hxS : x ∈ (S : Subgroup G) := BrauerWong.wreathModelHom_mem S e _
  have hNS : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ N := by
    intro g hg
    obtain ⟨q', hq', c', hc', rfl⟩ := FlatTwistedBases.normalizer_eq_mul_centralizer S e hn g hg
    refine N.mul_mem (hSN hq') (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
    exact (Subgroup.mem_centralizer_iff.mp hc' _ hxS).symm
  set Q₀' : Subgroup (R × W) := (⊥ : Subgroup R).prod U with hQ₀'
  set Q₀ : Subgroup G := Q₀'.map Φ with hQ₀
  have hQ₀card : Nat.card Q₀ = q := by
    rw [hQ₀, Subgroup.card_map_of_injective hΦinj, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,
      Nat.card_prod, Subgroup.card_bot, hUcard, one_mul]
  have hQ₀comm : ∀ a ∈ Q₀, ∀ c ∈ Q₀, a * c = c * a := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    obtain ⟨hz1, hz2⟩ := Subgroup.mem_prod.mp hz
    obtain ⟨hw1, hw2⟩ := Subgroup.mem_prod.mp hw
    rw [Subgroup.mem_bot] at hz1 hw1
    exact Prod.ext (by simp [hz1, hw1]) (unipotentSubgroup_comm hz2 hw2)
  have hQ₀N : Q₀ ≤ N := by
    rintro _ ⟨z, -, rfl⟩
    exact productEmbedding_mem μ eH z
  have hrel : Nat.card Q₀ * Q₀.relIndex N = Nat.card N := by
    rw [Subgroup.relIndex, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ₀N).toEquiv,
      Subgroup.card_mul_index]
  have hrelp : ¬ p ∣ Q₀.relIndex N := by
    have hrel' : Q₀.relIndex N = Nat.card R * 2 ^ n * (q ^ 2 - 1) := by
      have h := hrel
      rw [hQ₀card, hNcard] at h
      have hq0 : 0 < q := by omega
      apply Nat.eq_of_mul_eq_mul_left hq0
      rw [h]
      ring
    rw [hrel']
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · exact hpR h
      · exact hp2n h
    · have hpq' : p ∣ q := dvd_pow_self p (by omega)
      have h1 : p ∣ q ^ 2 := dvd_pow hpq' two_ne_zero
      have h2 : p ∣ q ^ 2 - (q ^ 2 - 1) := Nat.dvd_sub h1 h
      rw [show q ^ 2 - (q ^ 2 - 1) = 1 by
        have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
        omega] at h2
      exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  set H' : Subgroup (R × W) := (⊤ : Subgroup R).prod T with hH'
  set H : Subgroup G := H'.map Φ with hH
  have hH'norm : H' ≤ Subgroup.normalizer (Q₀' : Set (R × W)) := by
    rintro z ⟨-, hz2⟩
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hTU := splitTorus_le_normalizer_unipotentSubgroup hz2
    rw [Subgroup.mem_normalizer_iff] at hTU
    simp only [hQ₀', Subgroup.mem_prod, Subgroup.mem_bot, Prod.fst_mul, Prod.snd_mul,
      Prod.fst_inv, Prod.snd_inv]
    rw [hRcomm z.1 w.1, mul_inv_cancel_right, ← hTU w.2]
  have hHnorm : H ≤ Subgroup.normalizer (Q₀ : Set G) :=
    (Subgroup.map_mono hH'norm).trans (Subgroup.le_normalizer_map Φ)
  have hH'cyc : IsCyclic H' := by
    have hTcyc : IsCyclic T := splitTorus_isCyclic hF3 hb rfl
    have hprod : IsCyclic ((⊤ : Subgroup R) × T) := by
      rw [Group.isCyclic_prod_iff]
      refine ⟨?_, hTcyc, ?_⟩
      · exact isCyclic_of_surjective (Subgroup.topEquiv (G := R)).symm.toMonoidHom
          (Subgroup.topEquiv (G := R)).symm.surjective
      · rw [Subgroup.card_top, hTcard]
        exact hRT
    exact isCyclic_of_surjective (Subgroup.prodEquiv _ _).symm.toMonoidHom
      (Subgroup.prodEquiv _ _).symm.surjective
  have hHcyc : IsCyclic H :=
    isCyclic_of_surjective (Subgroup.equivMapOfInjective H' Φ hΦinj).toMonoidHom
      (Subgroup.equivMapOfInjective H' Φ hΦinj).surjective
  have hKH : K ≤ H := Subgroup.map_mono (Subgroup.prod_mono le_rfl hZWT)
  have hHcard : Nat.card H = (q - 1) * Nat.card K := by
    rw [hH, Subgroup.card_map_of_injective hΦinj, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,
      Nat.card_prod, Subgroup.card_top, hTcard, hKcard]
    ring
  have hGq : Nat.card G = Nat.card K * q ^ 3 * (q - 1) * (q ^ 3 + 1) := by
    rw [hKcard]
    exact card_eq_of_unitary_order hq1 (by exact_mod_cast hGcard)
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hKcard]
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hpR h
    · exact hp2n h
  exact ⟨K, hKcard, hxK, hKcent, hpK, hKconf, hSN, hNS, Q₀, hQ₀card, hQ₀comm, hQ₀N, hrelp, H,
    hHnorm, hHcyc, hKH, hHcard, hGq⟩

end CFSG.Wreathed.SameFieldUnitary
