module

public import CFSG.CharacterTheory.Wreathed.SameFieldUnitaryCharacters
public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchCharacter
public import CFSG.CharacterTheory.BrauerLinearThree.QOneLemmaOne
public import CFSG.CharacterTheory.Wreathed.SameFieldUnitaryLocal

public section

open scoped Classical

namespace CFSG.Wreathed.SameFieldUnitary

open CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.OriginalStationarityCoverageCriterion
  CFSG.Wreathed.SmallerRecognitionOriginalField CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.Wreathed.CentralSL2 CFSG.TwoRankLowerBound.Helpers

theorem exists_conj_mem_of_card_eq {X : Type*} [Group X] [Finite X] {r : ℕ} [Fact r.Prime]
    (H : Subgroup X) (hH : Nat.card H = r ^ (Nat.card X).factorization r) {y : X}
    (hy : IsPGroup r (Subgroup.zpowers y)) : ∃ g : X, g⁻¹ * y * g ∈ H := by
  obtain ⟨Q, hQ⟩ := hy.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (Sylow.ofCard H hH) Q
  have hyQ : y ∈ (Q : Subgroup X) := hQ (Subgroup.mem_zpowers y)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyQ
  refine ⟨g, ?_⟩
  have hmem : (MulAut.conj g)⁻¹ • y ∈ H := hyQ
  rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv] at hmem
  exact hmem

section Model

variable {F : Type} [Field F] [Finite F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}

theorem card_centralizer_of_pElement {p f : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ f)
    (hpm : ¬ p ∣ m) (hb : ¬ IsSquare b) {w : CentralExtension F b m hm heven} (hw1 : w ≠ 1)
    {k : ℕ} (hwk : orderOf w = p ^ k) :
    Nat.card (Subgroup.centralizer {w}) = m * Nat.card F := by
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ Nat.card F := Nat.card_pos
  have hWcard : Nat.card (CentralExtension F b m hm heven) =
      p ^ f * (m * (Nat.card F ^ 2 - 1)) := by
    rw [card_centralExtension_eq, hF]
    ring
  have hcop : Nat.Coprime p (m * (Nat.card F ^ 2 - 1)) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hpm h
    · have hpq : p ∣ Nat.card F := by
        rw [hF]
        exact dvd_pow_self p (by
          rintro rfl
          rw [pow_zero] at hF
          have : 1 < Nat.card F := Finite.one_lt_card
          omega)
      have h1 : p ∣ Nat.card F ^ 2 := dvd_pow hpq two_ne_zero
      have h2 := Nat.dvd_sub h1 h
      rw [show Nat.card F ^ 2 - (Nat.card F ^ 2 - 1) = 1 by
        have : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ hq1
        omega] at h2
      exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  have hfac : (Nat.card (CentralExtension F b m hm heven)).factorization p = f := by
    rw [hWcard, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (by
        intro h0
        rw [h0] at hcop
        exact hp.one_lt.ne' ((Nat.coprime_zero_right _).mp hcop)),
      Finsupp.add_apply, hp.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.Prime.coprime_iff_not_dvd hp).mp hcop h),
      add_zero]
  have hU : Nat.card (unipotentSubgroup F b m hm heven) =
      p ^ (Nat.card (CentralExtension F b m hm heven)).factorization p := by
    rw [card_unipotentSubgroup, hF, hfac]
  have hwp : IsPGroup p (Subgroup.zpowers w) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hwk]
    exact ⟨k, rfl⟩
  obtain ⟨g, hg⟩ := exists_conj_mem_of_card_eq _ hU hwp
  obtain ⟨t, ht⟩ := (mem_unipotentSubgroup_iff F b m hm heven _).mp hg
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [unipotentElement_zero] at ht
    apply hw1
    have : w = g * (g⁻¹ * w * g) * g⁻¹ := by group
    rw [this, ← ht]
    group
  have hconj : IsConj w (unipotentElement F b m hm heven t) := by
    rw [ht]
    exact isConj_iff.mpr ⟨g⁻¹, by group⟩
  rw [card_centralizer_of_isConj hconj, ← card_centralizer_of_isConj (isConj_unipotent hb ht0),
    card_centralizer_unipotent hb]

end Model

section Arithmetic

theorem dvd_mul_two_pow_of_not_dvd {c M n : ℕ} (hM : Odd M) (h : c ∣ M * 2 ^ (n + 1))
    (h2 : ¬ 2 ^ (n + 1) ∣ c) : c ∣ M * 2 ^ n := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact h2 (dvd_zero _)
  obtain ⟨a, c', hc', rfl⟩ := Nat.exists_eq_two_pow_mul_odd hc0
  have hcop : Nat.Coprime c' (2 ^ (n + 1)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hc')
  have hc'M : c' ∣ M :=
    hcop.dvd_of_dvd_mul_right ((Dvd.intro_left _ rfl).trans h)
  have ha : 2 ^ a ∣ M * 2 ^ (n + 1) := (Dvd.intro _ rfl).trans h
  have ha' : 2 ^ a ∣ 2 ^ (n + 1) :=
    (Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hM)).dvd_of_dvd_mul_left ha
  have han : a ≤ n := by
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp ha'
    rcases Nat.lt_or_ge a (n + 1) with h' | h'
    · omega
    · exfalso
      apply h2
      have : a = n + 1 := le_antisymm this h'
      rw [this]
      exact Dvd.intro _ rfl
  rw [mul_comm M]
  exact Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 han) hc'M

theorem dvd_of_dvd_mul_of_primes {c M k : ℕ} (h : c ∣ M * k)
    (hk : ∀ p₀ : ℕ, p₀.Prime → p₀ ∣ k → ¬ p₀ ∣ c) : c ∣ M :=
  (Nat.coprime_of_dvd fun p₀ hp₀ hc hk' => hk p₀ hp₀ hk' hc).dvd_of_dvd_mul_right h

end Arithmetic

open CFSG.Wreathed.PrimewiseConfinedCentralCore in
theorem exists_centralizer_model
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrec : SmallerWreathedRecognition G)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq5 : 5 ≤ p ^ f)
    (hq3 : p ^ f % 4 = 3)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    (hst : OriginalAllPrimeStationarity n S e) (hcov : OriginalAllPrimeCoverage n S e) :
    Nat.card (centralizerOddCore n S e) ∣ p ^ f + 1 ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (b : Fˣ), Nat.card F = p ^ f ∧ ¬ IsSquare b ∧
      ∃ Φ : centralizerOddCore n S e × CentralExtension F b (2 ^ n) (wreathModulus_pos n)
          (wreathModulus_even hn) →* G,
        Function.Injective Φ ∧ (∀ z, Φ z ∈ involutionCentralizer n S e) ∧
        (∀ g ∈ involutionCentralizer n S e, ∃ z, Φ z = g) ∧
        ∀ r : centralizerOddCore n S e, Φ (r, 1) = ((r : involutionCentralizer n S e) : G) := by
  have hp2 : p ≠ 2 := fun h => by rw [h] at hpodd; exact (Nat.not_odd_iff_even.mpr even_two) hpodd
  have hconf :=
    ComponentCoverConfinement.stationarity_and_original_coverage_confine_all_odd_core_elements
      hnonab n hn S e hfour p f hp hpodd hf hq5 hmodel hrec hst hcov
  obtain ⟨-, -, -, -, -, -, hRdvd, -, ⟨F, hF, hFfin, Sigma, b, hSigma, ρ, Ψ, hdata⟩, hall,
      -, -, -, JS, -, ⟨μ, hμ⟩, ⟨φ, -⟩⟩ :=
    original_primewise_coverage_and_confinement_give_central_cyclic_odd_core
      hnonab n hn S e hfour p f hp hp2 hf hmodel hcov (fun r hr hr1 => (hconf r hr hr1).1)
  have hSig : Nat.card Sigma = 1 := hall F Sigma b hSigma ρ Ψ hdata
  have : Subsingleton Sigma := (Nat.card_eq_one_iff_unique.mp hSig).1
  let eW := CFSG.Semidihedral.SimpleLayerFrontier.semidirectProductTrivialRightEquiv
    (fieldAction F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma)
  let eH := φ.trans (Ψ.symm.trans eW.symm)
  have hε : (if p ^ f % 4 = 1 then (1 : ℤ) else -1) = -1 := by simp [hq3]
  rw [hε] at hRdvd
  have htwo := NormalComponentLift.two_pow_eq_two_part (n := n) (hn := hn) (S := S) (e := e)
    hnonab hfour hp hp2 hf hmodel
  rw [hε] at htwo
  have h2q : 2 ^ n ∣ p ^ f + 1 := by
    have h := padicValInt_dvd (p := 2) ((p ^ f : ℕ) - (-1 : ℤ))
    have h' : ((2 ^ n : ℕ) : ℤ) ∣ ((p ^ f + 1 : ℕ) : ℤ) := by
      rw [htwo]
      push_cast
      simpa using h
    exact Int.natCast_dvd_natCast.mp h'
  exact ⟨dvd_add_one_of_dvd_div h2q hRdvd, F, hF, hFfin, b, hdata.card, hdata.nonsquare,
    productEmbedding μ eH, productEmbedding_injective μ eH, productEmbedding_mem μ eH,
    fun g hg => exists_productEmbedding_eq μ eH hg, fun r => by
      rw [productEmbedding_apply μ hμ eH, map_one]
      simp⟩

theorem exists_central_involution {X : Type*} [Group X] [Finite X] {P : Subgroup X}
    (hP : IsPGroup 2 P) (hbot : P ≠ ⊥) :
    ∃ t ∈ P, orderOf t = 2 ∧ ∀ y ∈ P, y * t = t * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, pow_zero, Subgroup.card_eq_one] at ha
      exact absurd ha hbot
    · exact h
  obtain ⟨k, hk, hkc⟩ := IsPGroup.card_center_eq_prime_pow ha ha0
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) 2 (by
    rw [hkc]
    exact dvd_pow_self 2 hk.ne')
  refine ⟨((t : P) : X), (t : P).2, ?_, fun y hy => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht]
  · have h := Subgroup.mem_center_iff.mp t.2 ⟨y, hy⟩
    exact congrArg Subtype.val h

theorem card_two_subgroup_dvd
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrec : SmallerWreathedRecognition G)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq5 : 5 ≤ p ^ f)
    (hq3 : p ^ f % 4 = 3)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    (hst : OriginalAllPrimeStationarity n S e) (hcov : OriginalAllPrimeCoverage n S e)
    {u : G} (hu1 : u ≠ 1) {k : ℕ} (hk : orderOf u = p ^ k) {P₂ : Subgroup G}
    (hP₂ : IsPGroup 2 P₂) (hP₂u : P₂ ≤ Subgroup.centralizer {u}) : Nat.card P₂ ∣ 2 ^ n := by
  have hp2 : p ≠ 2 := fun h => by rw [h] at hpodd; exact (Nat.not_odd_iff_even.mpr even_two) hpodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype G := Fintype.ofFinite G
  by_cases hbot : P₂ = ⊥
  · rw [hbot, Subgroup.card_bot]
    exact one_dvd _
  set x : G := wreathModelHom S e (Original.x (2 ^ n)) with hx
  have hxord : orderOf x = 2 := CompatibleFamilies.orderOf_x S e hn
  have hinv : ∀ a c : G, orderOf a = 2 → orderOf c = 2 → IsConj a c :=
    (simple_wreathed_one_involution_class_and_local_S3 hnonab n hn S e).2.2.1
  obtain ⟨t, htP, htord, htc⟩ := exists_central_involution hP₂ hbot
  obtain ⟨c, hc⟩ := isConj_iff.mp (hinv t x htord hxord)
  set P₂' : Subgroup G := P₂.map (MulAut.conj c).toMonoidHom with hP₂'
  have hP₂'card : Nat.card P₂' = Nat.card P₂ :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  set u' : G := c * u * c⁻¹ with hu'
  have hu'ord : orderOf u' = p ^ k := by
    rw [hu', ← MulAut.conj_apply, MulEquiv.orderOf_eq, hk]
  have hu'1 : u' ≠ 1 := by
    intro h
    apply hu1
    have : u = c⁻¹ * u' * c := by rw [hu']; group
    rw [this, h]
    group
  have hu'x : u' ∈ involutionCentralizer n S e := by
    show u' ∈ Subgroup.centralizer {x}
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc, hu']
    have htu : t * u = u * t := Subgroup.mem_centralizer_singleton_iff.mp (hP₂u htP)
    calc c * u * c⁻¹ * (c * t * c⁻¹) = c * (u * t) * c⁻¹ := by group
      _ = c * (t * u) * c⁻¹ := by rw [htu]
      _ = c * t * c⁻¹ * (c * u * c⁻¹) := by group
  have hP₂'x : P₂' ≤ involutionCentralizer n S e := by
    rintro _ ⟨y, hy, rfl⟩
    show _ ∈ Subgroup.centralizer {x}
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hyt := htc y hy
    calc c * y * c⁻¹ * (c * t * c⁻¹) = c * (y * t) * c⁻¹ := by group
      _ = c * (t * y) * c⁻¹ := by rw [hyt]
      _ = c * t * c⁻¹ * (c * y * c⁻¹) := by group
  have hP₂'u : P₂' ≤ Subgroup.centralizer {u'} := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hyu : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp (hP₂u hy)
    rw [hu']
    calc c * y * c⁻¹ * (c * u * c⁻¹) = c * (y * u) * c⁻¹ := by group
      _ = c * (u * y) * c⁻¹ := by rw [hyu]
      _ = c * u * c⁻¹ * (c * y * c⁻¹) := by group
  obtain ⟨hRq, F, hF, hFfin, b, hFcard, hb, Φ, hΦinj, hΦN, hNΦ, -⟩ :=
    exists_centralizer_model hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel hst hcov
  obtain ⟨z, hz⟩ := hNΦ u' hu'x
  have hzord : orderOf z = p ^ k := by rw [← orderOf_injective Φ hΦinj, hz, hu'ord]
  have hz1 : z.1 = 1 := by
    have h1 : orderOf z.1 ∣ p ^ k := by
      rw [← hzord, Prod.orderOf]
      exact Nat.dvd_lcm_left _ _
    have h2 : orderOf z.1 ∣ Nat.card (centralizerOddCore n S e) := orderOf_dvd_natCard _
    have hcop : Nat.Coprime (p ^ k) (Nat.card (centralizerOddCore n S e)) := by
      apply Nat.Coprime.pow_left
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      have h' : p ∣ p ^ f + 1 := h.trans hRq
      have hpq : p ∣ p ^ f := dvd_pow_self p (by omega)
      exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hpq).mp h'))
    have h3 : orderOf z.1 ∣ 1 := by
      rw [← Nat.Coprime.gcd_eq_one hcop]
      exact Nat.dvd_gcd h1 h2
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  set w := z.2 with hw
  have hword : orderOf w = p ^ k := by
    rw [← hzord, Prod.orderOf, hz1, orderOf_one, Nat.lcm_one_left]
  have hw1 : w ≠ 1 := by
    intro h
    apply hu'1
    rw [← hz, show z = 1 from Prod.ext hz1 h, map_one]
  have hpm : ¬ p ∣ 2 ^ n := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hCw : Nat.card (Subgroup.centralizer {w}) = 2 ^ n * Nat.card F :=
    card_centralizer_of_pElement hp hFcard hpm hb hw1 hword
  have hP₂'range : P₂' ≤ Φ.range := fun g hg => by
    obtain ⟨y, hy⟩ := hNΦ g (hP₂'x hg)
    exact ⟨y, hy⟩
  set P'' := P₂'.comap Φ with hP''
  have hP''card : Nat.card P'' = Nat.card P₂' := by
    rw [← Subgroup.card_map_of_injective hΦinj, hP'', Subgroup.map_comap_eq_self hP₂'range]
  have hP''le : P'' ≤ (⊤ : Subgroup (centralizerOddCore n S e)).prod
      (Subgroup.centralizer {w}) := by
    intro y hy
    refine ⟨Subgroup.mem_top _, ?_⟩
    have hyu := hP₂'u hy
    rw [Subgroup.mem_centralizer_singleton_iff, ← hz, ← map_mul, ← map_mul] at hyu
    have hyz := hΦinj hyu
    show y.2 ∈ Subgroup.centralizer {w}
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Prod.snd hyz
  have hdvd : Nat.card P₂ ∣ Nat.card (centralizerOddCore n S e) * Nat.card F * 2 ^ n := by
    rw [← hP₂'card, ← hP''card]
    have h := Subgroup.card_dvd_of_le hP''le
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_top,
      hCw] at h
    calc Nat.card P'' ∣ Nat.card (centralizerOddCore n S e) * (2 ^ n * Nat.card F) := h
      _ = Nat.card (centralizerOddCore n S e) * Nat.card F * 2 ^ n := by ring
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP₂
  rw [ha] at hdvd ⊢
  have hodd : Odd (Nat.card (centralizerOddCore n S e) * Nat.card F) := by
    refine (centralizerOddCore_card_odd n S e).mul ?_
    rw [hFcard]
    exact hpodd.pow
  exact (Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd)).dvd_of_dvd_mul_left hdvd

theorem basis_character_mem_blocksIrr {X : Type} [Group X] [Fintype X]
    (basis : FiniteIrreducibleCharacterBasis X) (l : basis.index) :
    (basis.representation l).character ∈ CFSG.BlocksIrr X :=
  ⟨(basis.representation l).vector, inferInstance, inferInstance, inferInstance,
    (basis.representation l).representation, basis.irreducible l, rfl⟩

open CFSG.Semidihedral.Principal in
theorem character_eq_zero_of_full_part {X : Type} [Group X] [Fintype X]
    (basis : FiniteIrreducibleCharacterBasis X) (l : basis.index) {r d M : ℕ} (hr : r.Prime)
    (hdeg : (basis.representation l).character 1 = (d : ℂ)) (hX : Nat.card X = d * M)
    (hM : ¬ r ∣ M) {g : X} (hg : r ∣ orderOf g) : (basis.representation l).character g = 0 := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨ideal, hmax, hmem⟩ := (CFSG.BlockBasics.residue_prime_existence _ hr).1
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) r :=
    (CFSG.BlockBasics.residue_prime_existence _ hr).2 ideal hmax hmem
  have hdeg' : r ^ (Nat.card X).factorization r ∣
      Module.finrank ℂ (basis.representation l).vector := by
    rw [CFSG.BrauerLinearThree.QOne.finrank_eq_of_character_one basis l hdeg]
    have h := Nat.ordProj_dvd (Nat.card X) r
    rw [hX] at h ⊢
    exact (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hr).mpr hM)).dvd_of_dvd_mul_right
      h
  exact (full_prime_part_character_degree_singleton_block_singular_vanishing
    basis ideal r l hdeg').2 g hg

theorem exists_irr_degree_cube
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (_hrec : SmallerWreathedRecognition G)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (_hq5 : 5 ≤ p ^ f)
    (hq3 : p ^ f % 4 = 3)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    (_hst : OriginalAllPrimeStationarity n S e) (_hcov : OriginalAllPrimeCoverage n S e) :
    ∃ χ : G → ℂ, χ ∈ CFSG.BlocksIrr G ∧ χ 1 = (((p ^ f) ^ 3 : ℕ) : ℂ) := by
  have hp2 : p ≠ 2 := fun h => by rw [h] at hpodd; exact (Nat.not_odd_iff_even.mpr even_two) hpodd
  let _ : Fintype G := Fintype.ofFinite G
  have hloc := ConditionalLocalHyp.of_isSimpleGroup hnonab n hn S e hfour p f hp hp2 hf hmodel
  obtain ⟨ideal, hmax, hmem⟩ := (CFSG.BlockBasics.residue_prime_existence _ Nat.prime_two).1
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 :=
    (CFSG.BlockBasics.residue_prime_existence _ Nat.prime_two).2 ideal hmax hmem
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨A, -, -, -, -, hA, -, -, -⟩ := unitary_principal_characters_of_localHyp n hn S e p f hp
    hp2 hf hloc rfl hq3 ideal basis (LinearLocalTwistMoment.principalCharacterLabel basis)
    (LinearLocalTwistMoment.principalCharacterLabel_character basis)
  exact ⟨_, basis_character_mem_blocksIrr basis A, by rw [hA]; push_cast; ring⟩

theorem card_centralizer_dvd
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrec : SmallerWreathedRecognition G)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq5 : 5 ≤ p ^ f)
    (hq3 : p ^ f % 4 = 3)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    (hst : OriginalAllPrimeStationarity n S e) (hcov : OriginalAllPrimeCoverage n S e) :
    ∀ u : G, u ≠ 1 → (∃ k : ℕ, orderOf u = p ^ k) →
      Nat.card (Subgroup.centralizer {u}) ∣
        Nat.card (centralizerOddCore n S e) * 2 ^ n * (p ^ f) ^ 3 := by
  rintro u hu1 ⟨k, hk⟩
  have hp2 : p ≠ 2 := fun h => by rw [h] at hpodd; exact (Nat.not_odd_iff_even.mpr even_two) hpodd
  let _ : Fintype G := Fintype.ofFinite G
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hu1 hk
  obtain ⟨K, hKcard, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hGq⟩ :=
    exists_centralizer_data hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel hst hcov
  rw [hKcard] at hGq
  obtain ⟨hRq, -⟩ :=
    exists_centralizer_model hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel hst hcov
  set q := p ^ f with hqdef
  set r := Nat.card (centralizerOddCore n S e) with hr
  have hq1 : 1 ≤ q := by omega
  have hqodd : Odd q := hpodd.pow
  have hrodd : Odd r := centralizerOddCore_card_odd n S e
  have hpq : p ∣ q := dvd_pow_self p (by omega)
  have hpq1 : ¬ p ∣ q + 1 := fun h =>
    hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hpq).mp h))
  have hloc := ConditionalLocalHyp.of_isSimpleGroup hnonab n hn S e hfour p f hp hp2 hf hmodel
  obtain ⟨ideal, hmax, hmem⟩ := (CFSG.BlockBasics.residue_prime_existence _ Nat.prime_two).1
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 :=
    (CFSG.BlockBasics.residue_prime_existence _ Nat.prime_two).2 ideal hmax hmem
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨A, B, D, χ, ψ, hA, -, -, hχ, hψ, -, -, hrel⟩ := unitary_principal_characters_of_localHyp
    n hn S e p f hp hp2 hf hloc rfl hq3 ideal basis
    (LinearLocalTwistMoment.principalCharacterLabel basis)
    (LinearLocalTwistMoment.principalCharacterLabel_character basis)
  have hpM : ¬ p ∣ r * 2 ^ n * (q - 1) * (q ^ 3 + 1) := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · exact hpq1 (h.trans hRq)
        · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
      · have h' := Nat.dvd_sub hpq h
        rw [show q - (q - 1) = 1 by omega] at h'
        exact hp.one_lt.ne' (Nat.dvd_one.mp h')
    · have h3 : p ∣ q ^ 3 := dvd_pow hpq (by norm_num)
      exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h3).mp h))
  have hA0 : ∀ g : G, p ∣ orderOf g → (basis.representation A).character g = 0 := fun g hg =>
    character_eq_zero_of_full_part basis A hp (d := q ^ 3) (by rw [hA, hqdef]; push_cast; ring)
      (by rw [hGq]; ring) hpM hg
  have hu_odd : Odd (orderOf u) := by rw [hk]; exact hpodd.pow
  have hpu : p ∣ orderOf u := by rw [hk]; exact dvd_pow_self p hk0
  have hχu : (basis.representation χ).character u = 1 := by
    obtain ⟨h1, h2, -⟩ := hrel u hu_odd
    rw [hA0 u hpu, add_zero] at h1
    rw [← h2, ← h1]
  have h3 := CFSG.Semidihedral.UnitaryBranch.card_centralizer_mul_dvd_of_character_eq_one
    (basis_character_mem_blocksIrr basis χ) (d := q ^ 3 + 1) (by rw [hχ, hqdef]; push_cast; ring)
    hχu
  rw [hGq] at h3
  have h4 : Nat.card (Subgroup.centralizer {u}) ∣ r * 2 ^ n * q ^ 3 * (q - 1) :=
    Nat.dvd_of_mul_dvd_mul_right (by positivity) h3
  have hk₁ : Odd ((q - 1) / 2) := ⟨(q - 3) / 4, by omega⟩
  have h5 : ∀ p₀ : ℕ, p₀.Prime → p₀ ∣ (q - 1) / 2 → ¬ p₀ ∣ Nat.card (Subgroup.centralizer {u}) := by
    intro p₀ hp₀ hp₀k hp₀C
    have : Fact p₀.Prime := ⟨hp₀⟩
    have hp₀odd : Odd p₀ := hk₁.of_dvd_nat hp₀k
    have hp₀q : p₀ ∣ q - 1 := hp₀k.trans (Nat.div_dvd_of_dvd (by
      obtain ⟨c, hc⟩ := hqodd
      exact ⟨c, by omega⟩))
    have hp₀p : p₀ ≠ p := by
      rintro rfl
      have h' := Nat.dvd_sub hpq hp₀q
      rw [show q - (q - 1) = 1 by omega] at h'
      exact hp₀.one_lt.ne' (Nat.dvd_one.mp h')
    have hp₀q1 : ¬ p₀ ∣ q + 1 := by
      intro h
      have h' := Nat.dvd_sub h hp₀q
      rw [show q + 1 - (q - 1) = 2 by omega] at h'
      have := (Nat.prime_dvd_prime_iff_eq hp₀ Nat.prime_two).mp h'
      rw [this] at hp₀odd
      exact absurd hp₀odd (by decide)
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer {u}) p₀ hp₀C
    set u₀ := u ^ p ^ (k - 1) with hu₀
    have hdvdk : p ^ (k - 1) ∣ orderOf u := by
      rw [hk]
      exact Nat.pow_dvd_pow p (Nat.sub_le k 1)
    have hu₀ord : orderOf u₀ = p := by
      rw [hu₀, orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) hdvdk, hk,
        Nat.pow_div (Nat.sub_le k 1) hp.pos, show k - (k - 1) = 1 by omega, pow_one]
    have hvord : orderOf (v : G) = p₀ := by rw [Subgroup.orderOf_coe, hv]
    have hcomm : Commute u₀ (v : G) := by
      have hvu := Subgroup.mem_centralizer_singleton_iff.mp v.2
      exact (Commute.pow_left hvu.symm _)
    have hcop : Nat.Coprime (orderOf u₀) (orderOf (v : G)) := by
      rw [hu₀ord, hvord, Nat.coprime_primes hp hp₀]
      exact hp₀p.symm
    set g := u₀ * (v : G) with hg
    have hgord : orderOf g = p * p₀ := by
      rw [hg, hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hu₀ord, hvord]
    have hgodd : Odd (orderOf g) := by rw [hgord]; exact hpodd.mul hp₀odd
    have hAg : (basis.representation A).character g = 0 :=
      hA0 g (by rw [hgord]; exact dvd_mul_right _ _)
    have hp₀M : ¬ p₀ ∣ r * 2 ^ n * q ^ 3 * (q + 1) := by
      intro h
      rcases (Nat.Prime.dvd_mul hp₀).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp₀).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hp₀).mp h with h | h
          · exact hp₀q1 (h.trans hRq)
          · have := (Nat.prime_dvd_prime_iff_eq hp₀ Nat.prime_two).mp (hp₀.dvd_of_dvd_pow h)
            rw [this] at hp₀odd
            exact absurd hp₀odd (by decide)
        · have h' : p₀ ∣ p ^ f := hp₀.dvd_of_dvd_pow h
          exact hp₀p ((Nat.prime_dvd_prime_iff_eq hp₀ hp).mp (hp₀.dvd_of_dvd_pow h'))
      · exact hp₀q1 h
    have hψg : (basis.representation ψ).character g = 0 :=
      character_eq_zero_of_full_part basis ψ hp₀ (d := (q - 1) * (q ^ 2 - q + 1))
        (M := r * 2 ^ n * q ^ 3 * (q + 1))
        (by
          rw [hψ, hqdef]
          have h1 : 1 ≤ p ^ f := hq1
          have h2 : p ^ f ≤ (p ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
          push_cast [h1, h2]
          ring)
        (by
          rw [hGq]
          have h2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) _
          zify [hq1, h2]
          ring)
        hp₀M (by rw [hgord]; exact dvd_mul_left _ _)
    obtain ⟨e1, -, e3⟩ := hrel g hgodd
    rw [hAg, add_zero] at e1
    rw [hψg] at e3
    exact CFSG.BrauerLinearThree.QOne.false_of_two_mul_eq_neg_one
      ((finite_character_value_isIntegral (basis.representation D) g).neg)
      (by linear_combination e1 - e3)
  have h6 : ¬ 2 ^ (n + 1) ∣ Nat.card (Subgroup.centralizer {u}) := by
    intro h
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 2 h
    have hPp : IsPGroup 2 (P.map (Subgroup.centralizer {u}).subtype) := by
      rw [IsPGroup.iff_card, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hP]
      exact ⟨n + 1, rfl⟩
    have hPu : P.map (Subgroup.centralizer {u}).subtype ≤ Subgroup.centralizer {u} :=
      Subgroup.map_subtype_le P
    have hdvd := card_two_subgroup_dvd hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel
      hst hcov hu1 hk hPp hPu
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hP] at hdvd
    have := Nat.le_of_dvd (by positivity) hdvd
    have h2 : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have h7 : Nat.card (Subgroup.centralizer {u}) ∣ r * q ^ 3 * 2 ^ (n + 1) := by
    have hsplit : r * 2 ^ n * q ^ 3 * (q - 1) = r * q ^ 3 * 2 ^ (n + 1) * ((q - 1) / 2) := by
      have : q - 1 = 2 * ((q - 1) / 2) := by
        obtain ⟨c, hc⟩ := hqodd
        omega
      rw [pow_succ]
      nth_rewrite 1 [this]
      ring
    exact dvd_of_dvd_mul_of_primes (hsplit ▸ h4) h5
  have h8 := dvd_mul_two_pow_of_not_dvd (hrodd.mul hqodd.pow) h7 h6
  calc Nat.card (Subgroup.centralizer {u}) ∣ r * q ^ 3 * 2 ^ n := h8
    _ = r * 2 ^ n * q ^ 3 := by ring

end CFSG.Wreathed.SameFieldUnitary
