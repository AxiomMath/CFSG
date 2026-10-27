module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.OuterFixedBasic
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.PSUFour
public import CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup TauCeti Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

section Unitary

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem exists_E9_fixed_primeFormFieldHom (h : UnitaryFieldData ℓ f K) (hn : 4 ≤ n)
    (hℓ3 : ℓ ≠ 3) (hg : ¬ 3 ∣ Nat.gcd n (ℓ ^ f + 1)) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    ∃ E : Subgroup (primeFormP h (idGram K n)), IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      ∀ e ∈ E, primeFormFieldHom h isPrimeFormGram_one σ e = e := by
  haveI := h.finite
  have hn3 : 3 ≤ n := by omega
  have hne : ¬ (n = 3 ∧ ℓ ^ f = 2) := by omega
  have hZ : ¬ 3 ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) := by
    rw [CFSG.RankThree.Classical.card_normOneScalars_one h (by omega)]
    exact hg
  obtain ⟨-, -, -, -, -, hinj, hrange, -⟩ :=
    CFSG.RankThree.Classical.prime_subfield_fixed_group_package h Nat.prime_three (by norm_num)
      hσ n hn3 hne hZ
  set h₀ := CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h Nat.prime_three
    (by norm_num) hσ with hh₀
  haveI := h₀.finite
  have hmod : StatedClassicalModel (primeFormP h₀ ((1 : GL (Fin n)
      (CFSG.LieType.Chevalley.fixSubfield σ)) : Matrix (Fin n) (Fin n)
        (CFSG.LieType.Chevalley.fixSubfield σ))) .PSU n ℓ (f / 3) := by
    refine ⟨⟨h.prime, h₀.one_le, hn3, fun he => by simp only [Prod.mk.injEq] at he; omega⟩,
      CFSG.LieType.Chevalley.fixSubfield σ, inferInstance, inferInstance, ?_,
      ⟨(CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h₀ n).symm.trans
        (unitaryPSUEquiv h₀ (by omega))⟩⟩
    rw [h₀.card, ← pow_mul, mul_comm]
  have h2 := CFSG.HardMathSupport.Timmesfeld.FieldBonus.two_le_pRank_three_psu_four hn hℓ3 hmod
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, -, hE, hE9⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h2
  obtain ⟨hE', hE9'⟩ := isElemAbelian_card_map_of_E9 _ hinj hE (by rw [hE9]; norm_num)
  refine ⟨_, hE', hE9', ?_⟩
  rintro _ ⟨y, -, rfl⟩
  have hy : CFSG.RankThree.Classical.primeSubfieldPSU h Nat.prime_three (by norm_num) hσ n y ∈
      CFSG.RankThree.Classical.fieldFixedPSU h n σ := by
    rw [← hrange]
    exact ⟨y, rfl⟩
  exact hy

theorem outerFixesE9_primeFormP (h : UnitaryFieldData ℓ f K) (hn : 4 ≤ n) (hℓ3 : ℓ ≠ 3)
    (hg : ¬ 3 ∣ Nat.gcd n (ℓ ^ f + 1)) : OuterFixesE9 (primeFormP h (idGram K n)) := by
  haveI := h.finite
  have hn3 : 3 ≤ n := by omega
  have hne : ¬ (n = 3 ∧ ℓ ^ f = 2) := by omega
  refine outerFixesE9_of_descent fun α hα3 hαo => ?_
  set σ := primeFormFieldFactor h isPrimeFormGram_one hn3 hne α with hσdef
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hD : α ∈ primeFormD h (idGram K n) := by
      rw [← ker_primeFormFieldFactor h isPrimeFormGram_one hn3 hne]
      exact h1
    exact hαo (CFSG.RankThree.PartOne.pElement_mem_inner_of_not_dvd_gcd h hn3 hne
      Nat.prime_three hg hD hα3)
  have hσ3 : σ ^ 3 = 1 := by rw [hσdef, ← map_pow, hα3, map_one]
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hα1 : α ≠ 1 := fun h1 => hαo ⟨1, by rw [h1, map_one]⟩
  have hαord : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn3 hne
      Nat.prime_three (by norm_num) (Ne.symm hℓ3) α hαord σ rfl hσord
  refine ⟨primeFormConjHom h _ M, primeFormFieldHom h isPrimeFormGram_one σ, ?_,
    exists_E9_fixed_primeFormFieldHom h hn hℓ3 hg hσord⟩
  rw [← hM]
  group

end Unitary

theorem outerFixedAt_twistedA (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedA r q).Valid)
    (hr : 3 ≤ r) (hp3 : q.p ≠ 3) (hg : ¬ 3 ∣ Nat.gcd (r + 1) (q.card + 1)) :
    OuterFixedAt ⟨.twistedA r q, hv⟩ := by
  refine outerFixedAt_of_model fun K _ _ e => ?_
  obtain ⟨-, -, -, -, F, _, h, ⟨θ⟩⟩ :=
    CFSG.RankThree.PartOne.exists_primeFormP_of_statedClassicalModel_PSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e)
  refine ⟨_, _, outerFixesE9_primeFormP h (by omega) hp3 ?_, ⟨θ⟩⟩
  rwa [PrimePower.card_def] at hg

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
