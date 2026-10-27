module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuter
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossUniOuter
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSUOrder
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuBadAux.Diag
public import CFSG.LocalAnalysis.ComponentClassification.LieOrderNumeratorMod
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedOdd
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.TwistedA
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Timmesfeld.LocalTwo
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.LieType.Chevalley
open CFSG.ComponentClassification.CatLeaf CFSG.HardMathSupport.Lang.Coordinator
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem card_range_primeSubfieldPSU {ℓ f N p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2) {σ : K ≃+* K}
    (hσ : orderOf σ = p) (hN : 1 ≤ N) :
    Nat.card (primeSubfieldPSU h hp hp2 hσ N).range =
      Nat.card (primeFormP (fixSubfield_unitaryFieldData h hp hp2 hσ)
        ((1 : GL (Fin N) (fixSubfield σ)) : Matrix (Fin N) (Fin N) (fixSubfield σ))) := by
  have hinj := subfieldPSU_injective h (fixSubfield_unitaryFieldData h hp hp2 hσ)
    (fixSubfield_unitaryFieldData_bar h hp hp2 hσ) N hN
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem dvd_card_primeSubfieldPSU_of_dvd_card {ℓ f N p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2) {σ : K ≃+* K}
    (hσ : orderOf σ = p) (hN : 3 ≤ N) (hpℓ : p ≠ ℓ)
    (hpdvd : p ∣ Nat.card (primeFormP h
      ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))) :
    p ∣ Nat.card (primeSubfieldPSU h hp hp2 hσ N).range := by
  obtain ⟨hpf, -⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  by_cases hpq : p ∣ ℓ ^ f + 1
  · exact dvd_card_range_of_dvd_q h hp hp2 hσ hN hpq
  ·
    set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
    have hAq : p ∣ lieOrderNumerator .PSU N (ℓ ^ f) := by
      rw [← card_primeFormP_one_mul_gcd h (n := N) (by omega)]
      exact dvd_mul_of_dvd_left hpdvd _
    have hAq₀ : p ∣ lieOrderNumerator .PSU N (ℓ ^ (f / p)) :=
      (prime_dvd_lieOrderNumerator_pow_iff .PSU N hp
        (Nat.one_le_of_lt h.prime.one_lt) hpf).1 hAq
    have hnotg : ¬ p ∣ Nat.gcd N (ℓ ^ (f / p) + 1) := by
      intro hg
      apply hpq
      have h1 : p ∣ ℓ ^ (f / p) + 1 := hg.trans (Nat.gcd_dvd_right _ _)
      have hodd : Odd p := hp.odd_of_ne_two hp2
      haveI : Fact p.Prime := ⟨hp⟩
      have hneg : ((ℓ ^ (f / p) : ℕ) : ZMod p) = -1 := by
        have h0 : (((ℓ ^ (f / p) + 1 : ℕ)) : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff _ p).2 h1
        rw [Nat.cast_add, Nat.cast_one] at h0
        exact eq_neg_of_add_eq_zero_left h0
      have hq : ℓ ^ f = (ℓ ^ (f / p)) ^ p := by rw [← pow_mul, Nat.div_mul_cancel hpf]
      have h0 : (((ℓ ^ f + 1 : ℕ)) : ZMod p) = 0 := by
        rw [Nat.cast_add, Nat.cast_one, hq, Nat.cast_pow, hneg, hodd.neg_one_pow]
        ring
      exact (ZMod.natCast_eq_zero_iff _ p).1 h0
    have hcard₀ := card_primeFormP_one_mul_gcd h₀ (n := N) (by omega)
    have hP₀ : p ∣ Nat.card (primeFormP h₀
        ((1 : GL (Fin N) (fixSubfield σ)) : Matrix (Fin N) (Fin N) (fixSubfield σ))) := by
      rw [← hcard₀] at hAq₀
      rcases (Nat.Prime.dvd_mul hp).1 hAq₀ with hh | hh
      · exact hh
      · exact absurd hh hnotg
    rwa [card_range_primeSubfieldPSU h hp hp2 hσ (by omega)]

theorem mem_innAutDerived_of_mem_primeFormD {ℓ f N p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2)
    {x : MulAut (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))}
    (hxD : x ∈ primeFormD h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))
    (hxp : x ^ p = 1) :
    x ∈ innAutDerived (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) := by
  classical
  simp only [primeFormD] at hxD
  obtain ⟨M, rfl⟩ := hxD
  refine mem_innAutDerived_of_inner_inv_of_odd
    (α := primeFormConjHom h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) M)
    (τ := primeFormFieldHom h (isPrimeFormGram_one (n := N)) (barAut h))
    (hp.odd_of_ne_two hp2) hxp ?_
  exact isInnerAut_field_conj_mul h M

theorem exists_conj_primeFormFieldHom_of_not_inner {ℓ f N p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hN : 3 ≤ N) (hne : ¬(N = 3 ∧ ℓ ^ f = 2))
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hpdvd : p ∣ Nat.card (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)))
    (hexc : ¬(N = 3 ∧ ℓ ^ f = 8 ∧ p = 3))
    {x : MulAut (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))}
    (hxp : x ^ p = 1)
    (hxout : x ∉ innAutDerived (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))) :
    ∃ (σ : K ≃+* K)
      (M : primeFormUnitary h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)),
      orderOf σ = p ∧ p ∣ f ∧ ¬(N = 3 ∧ ℓ ^ (f / p) = 2) ∧
        x = primeFormConjHom h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) M *
          primeFormFieldHom h (isPrimeFormGram_one (n := N)) σ *
          (primeFormConjHom h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) M)⁻¹ := by
  classical
  haveI : Finite K := h.finite
  haveI : Fact p.Prime := ⟨hp⟩
  have hxD : x ∉ primeFormD h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := fun hx =>
    hxout (mem_innAutDerived_of_mem_primeFormD h hp hp2 hx hxp)
  have hσ1 : primeFormFieldFactor h (isPrimeFormGram_one (n := N)) hN hne x ≠ 1 := by
    intro h1
    apply hxD
    rw [← ker_primeFormFieldFactor h (isPrimeFormGram_one (n := N)) hN hne]
    exact h1
  have hσp : primeFormFieldFactor h (isPrimeFormGram_one (n := N)) hN hne x ^ p = 1 := by
    rw [← map_pow, hxp, map_one]
  have hσord : orderOf (primeFormFieldFactor h (isPrimeFormGram_one (n := N)) hN hne x) = p :=
    orderOf_eq_prime hσp hσ1
  have hx1 : x ≠ 1 := fun h1 => hxD (h1 ▸ one_mem _)
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  obtain ⟨hpf, -, -, -, -, M, hM⟩ :=
    unitary_prime_semilinear_field_descent' h hN hne hp hp2 x hxord
      (primeFormFieldFactor h (isPrimeFormGram_one (n := N)) hN hne x) rfl hσord
  set σ := primeFormFieldFactor h (isPrimeFormGram_one (n := N)) hN hne x with hσdef
  have hJp : p ∣ Nat.card (primeSubfieldPSU h hp hp2 hσord N).range :=
    dvd_card_primeSubfieldPSU_of_dvd_card h hp hp2 hσord hN hpℓ hpdvd
  have hq₀ : ¬(N = 3 ∧ ℓ ^ (f / p) = 2) := by
    rintro ⟨hN3, hq2⟩
    obtain ⟨hℓ2, hk1⟩ := Nat.prime_two.pow_eq_iff.mp hq2
    have hfp : f = p := by rw [← Nat.mul_div_cancel' hpf, hk1, mul_one]
    have hcard72 : Nat.card (primeSubfieldPSU h hp hp2 hσord N).range = 72 := by
      rw [hN3, card_range_primeSubfieldPSU h hp hp2 hσord (N := 3) (by norm_num)]
      exact card_primeFormP_three_two (fixSubfield_unitaryFieldData h hp hp2 hσord) hq2
    have hp3 : p = 3 := by
      have h2 : p ∣ 2 ^ 3 * 3 ^ 2 := by
        rw [show (2 : ℕ) ^ 3 * 3 ^ 2 = 72 by norm_num, ← hcard72]
        exact hJp
      rcases (Nat.Prime.dvd_mul hp).1 h2 with hh | hh
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
          (hp.dvd_of_dvd_pow hh)) hp2
      · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hh)
    exact hexc ⟨hN3, by rw [hℓ2, hfp, hp3]; norm_num, hp3⟩
  refine ⟨σ, M, hσord, hpf, hq₀, ?_⟩
  rw [← hM]
  group

theorem fieldCoreAt_unitary {ℓ f N : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (hN : 3 ≤ N) (hne : ¬(N = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ)
    (hpdvd : p ∣ Nat.card (primeFormP h
      ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)))
    (hexc : ¬(N = 3 ∧ ℓ ^ f = 8 ∧ p = 3)) :
    ∀ x : MulAut (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)),
      x ^ p = 1 → x ∉ innAutDerived
        (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) → FieldCoreAt p x := by
  haveI : Finite K := h.finite
  haveI : Fact p.Prime := ⟨hp⟩
  intro x hxp hxout
  obtain ⟨σ, M, hσord, -, hq₀, hxδ⟩ :=
    exists_conj_primeFormFieldHom_of_not_inner h hN hne hp hp2 hpℓ hpdvd hexc hxp hxout
  have hJp : p ∣ Nat.card (primeSubfieldPSU h hp hp2 hσord N).range :=
    dvd_card_primeSubfieldPSU_of_dvd_card h hp hp2 hσord hN hpℓ hpdvd
  have hfc : FieldCoreAt p (primeFormFieldHom h (isPrimeFormGram_one (n := N)) σ) :=
    fieldCoreAt_fieldHom_of_subfield h hp hp2 hσord hN hne hq₀ hJp
  exact fieldCoreAt_of_conj hfc
    (primeFormConjHom h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) M)⁻¹
    (by rw [hxδ]; group)

theorem lieOuterPLayer_unitary (p : ℕ) : p.Prime → p ≠ 2 →
    LieOuterPLayer p isUnitaryIdx := by
  intro hp hp2 d hd hP hnExc S hS hfin he hnot hpdvd
  obtain ⟨e⟩ := he
  cases d with
  | twistedA n q =>
    have hmodel := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA n q hd e
    obtain ⟨K, _, hU, -, ⟨eP⟩⟩ :=
      exists_primeFormP_mulEquiv_of_statedModel hmodel
    let eS : S ≃* primeFormP hU
        ((1 : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) := eP
    have hN : 3 ≤ n + 1 := hmodel.1.2.2.1
    have hne : ¬(n + 1 = 3 ∧ q.p ^ q.exponent = 2) := by
      rintro ⟨h1, h2⟩
      exact hmodel.1.2.2.2 (by rw [h1, h2])
    have hpℓ : p ≠ q.p := by
      have h := characteristic_ne_of_not_isChevSimple hd ⟨e⟩ hnot
      rw [TauCeti.LieTypeIndex.characteristic_twistedA] at h
      exact h.symm
    have hpdvdM : p ∣ Nat.card (primeFormP hU
        ((1 : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) := by
      rw [← Nat.card_congr eS.toEquiv]
      exact hpdvd
    have hexc : ¬(n + 1 = 3 ∧ q.p ^ q.exponent = 8 ∧ p = 3) := by
      rintro ⟨h1, h2, h3⟩
      apply hnExc
      have hn2 : n = 2 := by omega
      subst hn2
      simp only [outerPLayerExc, TauCeti.PrimePower.card_def]
      exact ⟨h3, h2⟩
    haveI : Finite (primeFormP hU
        ((1 : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) :=
      CFSG.RankThree.PartOne.KCUnitaryModel.finite_primeFormP
    exact outerPLayerAt_of_mulEquiv_of_fieldCoreAt hp eS
      (fieldCoreAt_unitary hU hN hne hp hp2 hpℓ hpdvdM hexc)
  | A n q => exact absurd hP (by simp [isUnitaryIdx])
  | B n q => exact absurd hP (by simp [isUnitaryIdx])
  | C n q => exact absurd hP (by simp [isUnitaryIdx])
  | D n q => exact absurd hP (by simp [isUnitaryIdx])
  | twistedD n q => exact absurd hP (by simp [isUnitaryIdx])
  | E6 q => exact absurd hP (by simp [isUnitaryIdx])
  | E7 q => exact absurd hP (by simp [isUnitaryIdx])
  | E8 q => exact absurd hP (by simp [isUnitaryIdx])
  | F4 q => exact absurd hP (by simp [isUnitaryIdx])
  | G2 q => exact absurd hP (by simp [isUnitaryIdx])
  | twistedE6 q => exact absurd hP (by simp [isUnitaryIdx])
  | trialityD4 q => exact absurd hP (by simp [isUnitaryIdx])
  | suzuki k => exact absurd hP (by simp [isUnitaryIdx])
  | reeG2 k => exact absurd hP (by simp [isUnitaryIdx])
  | reeF4 k => exact absurd hP (by simp [isUnitaryIdx])
  | tits => exact absurd hP (by simp [isUnitaryIdx])

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
