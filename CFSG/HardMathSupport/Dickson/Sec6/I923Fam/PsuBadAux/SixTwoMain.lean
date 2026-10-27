module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuBadAux.SixTwoDiag
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuBadAux.SixTwoKey
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuBadAux.SixTwoNum
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary32Base
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Split

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.PartOne.Sec66T
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification.CatLeaf
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryFrame
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo CFSG.RankThree.PartTwo.KFacts
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped commutatorElement

variable {ℓ f : ℕ} {K : Type} [Field K]

variable (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2)

include hq in
theorem exists_conj_of_pow_three {ψ : MulAut (primeFormP h (idGram K 6))} (hψ3 : ψ ^ 3 = 1) :
    ∃ M : primeFormUnitary h (idGram K 6), primeFormConjHom h (idGram K 6) M = ψ := by
  have hn : 3 ≤ 6 := by norm_num
  have hne : ¬(6 = 3 ∧ ℓ ^ f = 2) := fun hh => by omega
  have hfin := h.finite
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_two h hq
  have hK4 : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_eq_four h hq
  have hσ : primeFormFieldFactor h (isPrimeFormGram_one (n := 6)) hn hne ψ = 1 := by
    apply ringEquiv_eq_one_of_pow_three hK4
    rw [← map_pow, hψ3, map_one]
  have hD : ψ ∈ primeFormD h (idGram K 6) := by
    rw [← ker_primeFormFieldFactor h (isPrimeFormGram_one (n := 6)) hn hne]
    exact hσ
  exact hD

include hq in
theorem scalar_of_conj_pow_three {M : primeFormUnitary h (idGram K 6)}
    (hM3 : primeFormConjHom h (idGram K 6) M ^ 3 = 1) :
    ∃ c₀ : Kˣ, (M : GL (Fin 6) K) ^ 3 = GeneralLinearGroup.scalar (Fin 6) c₀ := by
  have hn : 3 ≤ 6 := by norm_num
  have hne : ¬(6 = 3 ∧ ℓ ^ f = 2) := fun hh => by omega
  have h1 : primeFormConjHom h (idGram K 6) (M ^ 3) = 1 := by rw [map_pow]; exact hM3
  obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne (M ^ 3)).1 h1
  exact ⟨c, by simpa using hc⟩

include hq in
theorem not_scalar_of_not_inner {M : primeFormUnitary h (idGram K 6)}
    (hψ : ¬ IsInnerAut (primeFormConjHom h (idGram K 6) M)) (c : Kˣ) :
    (M : GL (Fin 6) K) ≠ GeneralLinearGroup.scalar (Fin 6) c := by
  intro hc
  apply hψ
  have hn : 3 ≤ 6 := by norm_num
  have hne : ¬(6 = 3 ∧ ℓ ^ f = 2) := fun hh => by omega
  have h1 : primeFormConjHom h (idGram K 6) M = 1 := by
    refine (primeFormConjHom_eq_one_iff_of_ne hn hne M).2 ⟨c, ?_, hc⟩
    rw [hq]
    exact unit_pow_three_eq_one h hq c
  rw [h1]
  exact one_mem _

include hq in
theorem normOneScalars_pow_three {z : gramSU h (idGram K 6)}
    (hz : z ∈ normOneScalars h (gramSU h (idGram K 6)) 6) : z ^ 3 = 1 := by
  obtain ⟨c, -, -, hz⟩ := hz
  apply Subtype.ext
  rw [Subgroup.coe_pow, hz, ← map_pow, unit_pow_three_eq_one h hq, map_one]
  rfl

include hq in
theorem exists_lift_commute {M : primeFormUnitary h (idGram K 6)} {g : primeFormP h (idGram K 6)}
    (hg : orderOf g = 11) (hgM : primeFormConjHom h (idGram K 6) M g = g) :
    ∃ g' : primeFormUnitary h (idGram K 6), g' * M = M * g' ∧ g' ^ 11 = 1 ∧ g' ≠ 1 := by
  classical
  obtain ⟨ĝ, rfl⟩ := QuotientGroup.mk_surjective g
  have hg11 : ((ĝ : primeFormP h (idGram K 6)) ^ 11 = 1) := by
    rw [← hg]; exact pow_orderOf_eq_one _
  have hmem : ĝ ^ 11 ∈ normOneScalars h (gramSU h (idGram K 6)) 6 := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hg11
  have hg33 : ĝ ^ 33 = 1 := by
    rw [show 33 = 11 * 3 by norm_num, pow_mul]
    exact normOneScalars_pow_three h hq hmem
  set ĝ' : gramSU h (idGram K 6) := ĝ ^ 12 with hĝ'
  have hĝ'11 : ĝ' ^ 11 = 1 := by
    rw [hĝ', ← pow_mul, show 12 * 11 = 33 * 4 by norm_num, pow_mul, hg33, one_pow]
  have hĝ'mk : (ĝ' : primeFormP h (idGram K 6)) = ĝ := by
    rw [hĝ', QuotientGroup.mk_pow, show 12 = 11 + 1 by norm_num, pow_add, hg11, one_mul, pow_one]
  have hĝ'1 : ĝ' ≠ 1 := by
    intro h1
    rw [h1] at hĝ'mk
    have : (ĝ : primeFormP h (idGram K 6)) = 1 := by rw [← hĝ'mk]; rfl
    rw [this, orderOf_one] at hg
    exact absurd hg (by norm_num)
  have hfix : primeFormConjHom h (idGram K 6) M (ĝ' : primeFormP h (idGram K 6)) =
      (ĝ' : primeFormP h (idGram K 6)) := by rw [hĝ'mk]; exact hgM
  rw [primeFormConjHom_mk, QuotientGroup.eq] at hfix
  set a : gramSU h (idGram K 6) :=
    ⟨(M : GL (Fin 6) K) * ĝ' * (M : GL (Fin 6) K)⁻¹, conj_mem_gramSU h _ M.2 ĝ'.2⟩ with ha
  set z : gramSU h (idGram K 6) := a⁻¹ * ĝ' with hz
  have hzmem : z ∈ normOneScalars h (gramSU h (idGram K 6)) 6 := hfix
  have hz3 : z ^ 3 = 1 := normOneScalars_pow_three h hq hzmem
  have hzc : Commute a z := by
    have := (Subgroup.mem_center_iff.1 (normOneScalars_le_center h _ 6 hzmem) a)
    exact this
  have ha11 : a ^ 11 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ha]
    change ((M : GL (Fin 6) K) * (ĝ' : GL (Fin 6) K) * (M : GL (Fin 6) K)⁻¹) ^ 11 = 1
    rw [conj_pow]
    have : (ĝ' : GL (Fin 6) K) ^ 11 = 1 := by
      have := congrArg (fun x : gramSU h (idGram K 6) => (x : GL (Fin 6) K)) hĝ'11
      simpa using this
    rw [this]
    group
  have hz11 : z ^ 11 = 1 := by
    have h1 : ĝ' = a * z := by rw [hz]; group
    have h2 : ĝ' ^ 11 = a ^ 11 * z ^ 11 := by
      conv_lhs => rw [h1]
      exact hzc.mul_pow 11
    rw [hĝ'11, ha11, one_mul] at h2
    exact h2.symm
  have hz1 : z = 1 := by
    calc z = (z ^ 3) ^ 4 * (z ^ 11)⁻¹ := by group
      _ = 1 := by rw [hz3, hz11]; simp
  have hĝ'a : ĝ' = a := by
    have : ĝ' = a * z := by rw [hz]; group
    rw [this, hz1, mul_one]
  have hcomm : (ĝ' : GL (Fin 6) K) * (M : GL (Fin 6) K) =
      (M : GL (Fin 6) K) * (ĝ' : GL (Fin 6) K) := by
    have h1 : (ĝ' : GL (Fin 6) K) = (M : GL (Fin 6) K) * ĝ' * (M : GL (Fin 6) K)⁻¹ := by
      have := congrArg (fun x : gramSU h (idGram K 6) => (x : GL (Fin 6) K)) hĝ'a
      simpa [ha] using this
    exact (mul_inv_eq_iff_eq_mul.mp h1.symm).symm
  refine ⟨⟨(ĝ' : GL (Fin 6) K), ((mem_gramSU_iff_unitary h).1 ĝ'.2).1⟩, Subtype.ext hcomm, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_pow]
    change (ĝ' : GL (Fin 6) K) ^ 11 = 1
    have := congrArg (fun x : gramSU h (idGram K 6) => (x : GL (Fin 6) K)) hĝ'11
    simpa using this
  · intro h1
    apply hĝ'1
    apply Subtype.ext
    exact congrArg (fun x : primeFormUnitary h (idGram K 6) => (x : GL (Fin 6) K)) h1

theorem noL2Layer_psu_sixTwo (hO : LieOrderFormulasInput) (h2 : UnitaryFieldData 2 1 K)
    (hcard : Nat.card (primeFormP h2 (idGram K 6)) ∣ 9196830720)
    {ψ : MulAut (primeFormP h2 (idGram K 6))} (hψ3 : ψ ^ 3 = 1) (hψ : ¬ IsInnerAut ψ) :
    NoL2Layer ψ := by
  classical
  have hq : 2 ^ 1 = 2 := by norm_num
  have hfin := h2.finite
  have hGL : Finite (GL (Fin 6) K) :=
    Finite.of_injective (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) Units.val_injective
  haveI : Finite (primeFormP h2 (idGram K 6)) := inferInstance
  obtain ⟨M, rfl⟩ := exists_conj_of_pow_three h2 hq hψ3
  obtain ⟨c₀, hM3⟩ := scalar_of_conj_pow_three h2 hq hψ3
  have hMs := not_scalar_of_not_inner h2 hq hψ
  intro A hA r hr hT
  have hAle : A ≤ fixSubgroup (primeFormConjHom h2 (idGram K 6) M) := hA.1
  have hdvd : Nat.card (barOf 3 A ⧸ Subgroup.center (barOf 3 A)) ∣ 9196830720 :=
    (Subgroup.card_quotient_dvd_card _).trans ((Subgroup.card_quotient_dvd_card _).trans
      ((Subgroup.card_subgroup_dvd_card A).trans hcard))
  have h11 : 11 ∣ Nat.card (barOf 3 A ⧸ Subgroup.center (barOf 3 A)) :=
    eleven_dvd_of_typeL2 hr hT hdvd
  have h11A : 11 ∣ Nat.card A :=
    h11.trans ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _))
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 11 h11A
  have hg : orderOf (a : primeFormP h2 (idGram K 6)) = 11 := by
    rw [Subgroup.orderOf_coe]
    exact ha
  have hgfix : primeFormConjHom h2 (idGram K 6) M (a : primeFormP h2 (idGram K 6)) = a :=
    hAle a.2
  obtain ⟨g', hg'M, hg'11, hg'1⟩ := exists_lift_commute h2 hq hg hgfix
  obtain ⟨T, D, i₀, ν, μ, hνμ, hMTD, hDmat⟩ := exists_diag_form hq hg'M hg'11 hg'1 hM3 hMs
  have hnoD : NoL2Layer (primeFormConjHom h2 (idGram K 6) D) :=
    noL2Layer_diag_sixTwo h2 hO i₀ hνμ hDmat
  have hconj := noL2Layer_conj (primeFormConjHom h2 (idGram K 6) T) hnoD
  have hMψ : primeFormConjHom h2 (idGram K 6) T * primeFormConjHom h2 (idGram K 6) D *
      (primeFormConjHom h2 (idGram K 6) T)⁻¹ = primeFormConjHom h2 (idGram K 6) M := by
    rw [← map_inv, ← map_mul, ← map_mul, ← hMTD]
  rw [hMψ] at hconj
  exact hconj A hA r hr hT

end CFSG.HardMathSupport.Dickson.Sec6.I923
