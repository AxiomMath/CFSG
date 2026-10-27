module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentE16Tags
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentE16ArithSO
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentE16ArithExc
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentE16OddPSL
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentE16OddPSU
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.XFiveLemma

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard.HSStd.Zassenhaus
open scoped commutatorElement

theorem e16_isQuasisimple_of_simple_nonab {J : Type*} [Group J] (hs : IsSimpleGroup J)
    (hn : ∃ a b : J, a * b ≠ b * a) : CFSG.IsQuasisimple J := by
  have hc : center J = ⊥ := by
    rcases (inferInstance : (center J).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hn
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
  let e : J ⧸ center J ≃* J :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  refine ⟨?_, e.isSimpleGroup, ?_⟩
  · refine Group.isPerfect_def.mpr ?_
    rcases (inferInstance : (commutator J).Normal).eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hn
      have hmem : ⁅a, b⁆ ∈ commutator J := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hab hmem
    · exact h
  · obtain ⟨a, b, hab⟩ := hn
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this

theorem e16_card_quotient_center {J : Type*} [Group J] (hs : IsSimpleGroup J)
    (hn : ∃ a b : J, a * b ≠ b * a) : Nat.card (J ⧸ center J) = Nat.card J := by
  have hc : center J = ⊥ := by
    rcases (inferInstance : (center J).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hn
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
  exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hc).trans
    QuotientGroup.quotientBot).toEquiv

theorem e16_exists_component {K : Type} [Group K] [Finite K] (D : CatE16Data K) :
    ∃ C : Subgroup ↥(fixedSubgroup D.τ), IsComponent C ∧ Nat.card C = 60 ∧
      Nat.card (C ⧸ center C) = 60 := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := a5_isSimpleGroup
  haveI hsimple : IsSimpleGroup ↥(autCentralizer D.τ) := D.e.isSimpleGroup
  have hnonab : ∃ a b : ↥(autCentralizer D.τ), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := a5_nonabelian
    refine ⟨D.e.symm a, D.e.symm b, fun h => hab ?_⟩
    have := congrArg D.e h
    simpa using this
  have hq : CFSG.IsQuasisimple ↥(autCentralizer D.τ) :=
    e16_isQuasisimple_of_simple_nonab hsimple hnonab
  have hsub : ((autCentralizer D.τ).subgroupOf (autCentralizer D.τ)).IsSubnormal := by
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.Normal.isSubnormal inferInstance
  obtain ⟨C, hC, ⟨eC⟩⟩ := fixedComponent_of_pump (τ := D.τ) (N := autCentralizer D.τ) le_rfl hq hsub
  have hC60 : Nat.card C = 60 := by rw [Nat.card_congr eC.toEquiv]; exact D.card_fixed
  haveI : IsSimpleGroup C := eC.isSimpleGroup
  have hCna : ∃ a b : C, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨eC.symm a, eC.symm b, fun h => hab ?_⟩
    have := congrArg eC h
    simpa using this
  exact ⟨C, hC, hC60, (e16_card_quotient_center ‹_› hCna).trans hC60⟩

theorem e16_odd_prime_eq_five (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    {K : Type} [Group K] [Finite K] (D : CatE16Data K) {t : StatedLieTag} {n p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (hmod : LieModel K t n p f) : p = 5 := by
  obtain ⟨C, hC, hC60, hCq60⟩ := e16_exists_component D
  rcases hGLS K t n p f hp hp2 hadm hmod D.τ D.orderOf_τ C hC with
    ⟨t', n', f', hadm', hmod'⟩ | ⟨-, -, -, hL⟩
  · obtain ⟨-, -, hfac⟩ := hO (C ⧸ center C) t' n' p f' hadm' hmod'
    rw [hCq60] at hfac
    have hexp := e16_sylowExp_pos hadm'
    have hf' : 1 ≤ f' := hadm'.2.1
    have hpos : 1 ≤ lieSylowExponent t' n' * f' := Nat.mul_pos hexp hf'
    have hp60 : p ∣ 60 :=
      Nat.dvd_of_factorization_pos (by omega)
    have h60 : (60 : ℕ) = 2 * (2 * (3 * 5)) := by norm_num
    rw [h60] at hp60
    have hp35 : p = 3 ∨ p = 5 := by
      rcases (Nat.Prime.dvd_mul hp).1 hp60 with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hp2
      rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hp2
      rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h)
    rcases hp35 with rfl | h5
    · exfalso
      have hle : lieSylowExponent t' n' * f' ≤ 1 := by
        by_contra hlt
        have : 3 ^ 2 ∣ 60 := by
          rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by norm_num), hfac]
          omega
        omega
      obtain ⟨rfl, rfl, rfl⟩ := e16_sylowExp_mul_eq_one hadm' (by omega)
      exact hadm'.2.2.2.2 rfl
    · exact h5
  · exfalso
    have hadm8 : StatedLieAdmissible .PSL 2 2 3 :=
      ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩
    obtain ⟨-, hord, -⟩ := hO C .PSL 2 2 3 hadm8 hL
    have h1 : lieOrderDivisor .PSL 2 (2 ^ 3) = 1 := by decide
    have h2 : lieOrderNumerator .PSL 2 (2 ^ 3) = 504 := by decide
    rw [h1, h2, mul_one] at hord
    omega

theorem e16_dvd_card_of_arith {X : Type*} [Group X] {t : StatedLieTag} {n q : ℕ}
    (hord : Nat.card X * lieOrderDivisor t n q = lieOrderNumerator t n q)
    (hpos : 0 < lieOrderDivisor t n q)
    (h : 2 ^ 5 * lieOrderDivisor t n q ∣ lieOrderNumerator t n q) : 2 ^ 5 ∣ Nat.card X := by
  rw [← hord] at h
  exact Nat.dvd_of_mul_dvd_mul_right hpos h

theorem e16_div_pos (t : StatedLieTag) {n q : ℕ} (hq : 2 ≤ q) : 0 < lieOrderDivisor t n q := by
  cases t <;> simp only [lieOrderDivisor] <;>
    first
      | (apply Nat.pos_of_ne_zero; rw [Ne, Nat.gcd_eq_zero_iff]; omega)
      | norm_num

theorem e16_odd_cases (hO : LieOrderFormulasInput) {K : Type} [Group K] {t : StatedLieTag}
    {n f : ℕ} (hadm : StatedLieAdmissible t n 5 f) (hmod : LieModel K t n 5 f)
    (h32 : ¬ 2 ^ 5 ∣ Nat.card K) : (t = .PSL ∧ n = 2) ∨ (t = .PSU ∧ n = 3) := by
  obtain ⟨-, hord, -⟩ := hO K t n 5 f hadm hmod
  have hq4 : (5 ^ f) % 4 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have hq2 : 2 ≤ 5 ^ f := by
    calc 2 ≤ 5 ^ 1 := by norm_num
      _ ≤ 5 ^ f := Nat.pow_le_pow_right (by norm_num) hadm.2.1
  have hpos : ∀ t' : StatedLieTag, ∀ n' : ℕ, 0 < lieOrderDivisor t' n' (5 ^ f) :=
    fun t' n' => e16_div_pos t' hq2
  obtain ⟨hchar5a, hchar5b, hchar5c, hchar5d⟩ := e16_char5_tag hadm
  cases t
  · by_cases h2 : n = 2
    · exact Or.inl ⟨rfl, h2⟩
    · exfalso
      have hn : 3 ≤ n := by have := hadm.2.2.1; omega
      exact h32 (e16_dvd_card_of_arith hord (hpos _ _) (e16_arith_psl hq4 hn))
  · by_cases h3 : n = 3
    · exact Or.inr ⟨rfl, h3⟩
    · exfalso
      have hn : 4 ≤ n := by have := hadm.2.2.1; omega
      exact h32 (e16_dvd_card_of_arith hord (hpos _ _) (e16_arith_psu hq4 hn))
  · exfalso
    exact h32 (e16_dvd_card_of_arith hord (hpos _ _) (e16_arith_psp hq4 hadm.2.2.1))
  · exfalso
    exact h32 (e16_dvd_card_of_arith hord (hpos _ _) (e16_arith_omegaOdd hq4 hadm.2.2.1))
  · exfalso
    exact h32 (e16_dvd_card_of_arith hord (hpos _ _) (e16_arith_omegaPlus hq4 hadm.2.2))
  · exfalso
    exact h32 (e16_dvd_card_of_arith hord (hpos _ _) (e16_arith_omegaMinus hq4 hadm.2.2))
  · exfalso
    exact h32 (e16_dvd_card_of_arith hord (hpos _ _) (e16_arith_G2 hq4))
  · exfalso
    exact h32 (e16_dvd_card_of_arith hord (hpos _ _) (e16_arith_F4 hq4))
  · exfalso
    exact h32 (e16_dvd_card_of_arith hord (hpos _ _) (e16_arith_E6 hq4))
  · exfalso
    exact h32 (e16_dvd_card_of_arith hord (hpos _ _) (e16_arith_E7 hq4))
  · exfalso
    exact h32 (e16_dvd_card_of_arith hord (hpos _ _) (e16_arith_E8 hq4))
  · exfalso
    exact h32 (e16_dvd_card_of_arith hord (hpos _ _) (e16_arith_twistedE6 hq4))
  · exfalso
    exact h32 (e16_dvd_card_of_arith hord (hpos _ _) (e16_arith_trialityD4 hq4))
  · exact absurd rfl hchar5a
  · exact absurd rfl hchar5b
  · exact absurd rfl hchar5c
  · exact absurd rfl hchar5d

theorem e16_false_odd (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    {K : Type} [Group K] [Finite K] (D : CatE16Data K) (hodd : OddLieType K) : False := by
  obtain ⟨t, n, p, f, hp, hp2, hadm, hmod⟩ := hodd
  have hp5 : p = 5 := e16_odd_prime_eq_five hGLS hO D hp hp2 hadm hmod
  subst hp5
  rcases e16_odd_cases hO hadm hmod D.not_two_pow_five_dvd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact e16_false_psl_two hO D hadm hmod
  · exact e16_false_psu_three hO D hadm hmod

end CFSG.ComponentClassification.CatFC
