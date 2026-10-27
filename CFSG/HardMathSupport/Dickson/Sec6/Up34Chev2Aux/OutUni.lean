module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.ExcOuter
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.LayerMore
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.PartOne.Sec66T
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Dickson.Sec6.I923
open Up34Chev2
open scoped commutatorElement

@[expose] def Up34C2OutDiagUniAt (n : ℕ) : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K), 3 ≤ n → ¬(n = 3 ∧ 2 ^ f = 2) →
    ∀ ψ ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      ψ ∉ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) →
        ¬ Up34Pumpup (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ψ

@[expose] def Up34C2OutDiag_TwA2 : Prop := Up34C2OutDiagUniAt 3

@[expose] def Up34C2OutDiag_TwAHigh : Prop := ∀ n : ℕ, 4 ≤ n → Up34C2OutDiagUniAt n

namespace Up34Chev2

theorem noL34_of_commutator_solvable {P : Type} [Group P] [Finite P] (ψ : MulAut P)
    (S : Subgroup P) (hcomm : ⁅fixSubgroup ψ, fixSubgroup ψ⁆ ≤ S) (hS : Group.IsSolvable ↥S) :
    NoL34Layer ψ := by
  intro A hA hT
  have hAD : A ≤ fixSubgroup ψ := hA.1
  have hperf : ⁅A, A⁆ = A := glaPComponent_perfect hA
  have hAS : A ≤ S := by
    calc A = ⁅A, A⁆ := hperf.symm
      _ ≤ ⁅fixSubgroup ψ, fixSubgroup ψ⁆ := Subgroup.commutator_mono hAD hAD
      _ ≤ S := hcomm
  haveI : Group.IsSolvable ↥A :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hAS)
  haveI : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.mpr hperf
  haveI : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr (glaPComponent_ne_bot hA)
  exact Group.IsPerfect.not_isSolvable ↥A inferInstance

section Field

variable {ℓ f n : ℕ} {K : Type} [Field K]


theorem noL34Layer_fieldAut_psu (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) :
    NoL34Layer (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) := by
  classical
  have hfin := h.finite
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by decide
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  obtain ⟨h3f, hcard⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  have hf0 : 1 ≤ f / 3 := by
    have : 3 ≤ f := Nat.le_of_dvd (by have := h.one_le; omega) h3f
    omega
  have hGL : Finite (GL (Fin n) K) :=
    Finite.of_injective (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) Units.val_injective
  have hfinT : Finite (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    inferInstance
  set j := primeSubfieldPSU h hp hp2 hσ n with hj
  have hinj : Function.Injective j := subfieldPSU_injective h h₀ hbar n (by omega)
  have hJC : j.range ≤ fixSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) :=
    range_subfieldPSU_le h n h₀ hbar
  have hCC := commutator_fixed_le_range (n := n) h hσ
  let eJ : primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ)) ≃* ↥j.range := MonoidHom.ofInjective hinj
  by_cases hq0 : n = 3 ∧ 2 ^ (f / 3) = 2
  ·
    obtain ⟨rfl, hq2⟩ := hq0
    have hcard72 := card_primeFormP_three_two h₀ hq2
    haveI : Group.IsSolvable (primeFormP h₀ ((1 : GL (Fin 3) (fixSubfield σ)) :
        Matrix (Fin 3) (Fin 3) (fixSubfield σ))) :=
      CFSG.SignalizerFunctorTheorem.McBride.UnitaryHeisenberg.isSolvable_of_card_dvd_seventy_two
        (by rw [hcard72])
    haveI : Group.IsSolvable ↥j.range :=
      Group.isSolvable_of_isSolvable_injective (f := eJ.symm.toMonoidHom) eJ.symm.injective
    exact noL34_of_commutator_solvable _ j.range hCC inferInstance
  ·
    have hs₀ := isSimpleGroup_primeFormP_one h₀ hn hq0
    have hnc₀ := not_commute_primeFormP_one h₀ hn hq0
    haveI : IsSimpleGroup (primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
        Matrix (Fin n) (Fin n) (fixSubfield σ))) := hs₀
    haveI : IsSimpleGroup ↥j.range := eJ.symm.isSimpleGroup
    have hnab : ∃ a b : ↥j.range, a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      apply hnc₀
      intro x y
      apply eJ.injective
      rw [map_mul, map_mul]
      exact hcon _ _
    have hperf₀ : Group.IsPerfect (primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
        Matrix (Fin n) (Fin n) (fixSubfield σ))) := by
      have := isPerfect_gramSU_one h₀ hn hq0
      exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    have hJCC : j.range ≤ ⁅fixSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ),
        fixSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ)⁆ := by
      haveI := hperf₀
      calc j.range = ⁅j.range, j.range⁆ := range_eq_commutator_of_perfect j
        _ ≤ _ := Subgroup.commutator_mono hJC hJC
    have hadm₀ : StatedLieAdmissible .PSU n 2 (f / 3) :=
      ⟨Nat.prime_two, hf0, hn, fun hc => hq0 ⟨(Prod.mk.inj hc).1, (Prod.mk.inj hc).2⟩⟩
    have hcard' : Nat.card (fixSubfield σ) = (2 ^ (f / 3)) ^ 2 := by
      rw [hcard, ← pow_mul, mul_comm]
    obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h₀
      (isPrimeFormGram_one (n := n) (K := fixSubfield σ))
    have hmodel : LieModel ↥j.range .PSU n 2 (f / 3) :=
      (lieModel_classical_iff (by decide)).mpr
        ⟨hadm₀, ↥(fixSubfield σ), inferInstance, inferInstance, hcard',
          ⟨(eJ.symm.trans eP).trans (unitaryPSUEquiv h₀ (by omega))⟩⟩
    exact noL34Layer_of_simple_commutator _ j.range (le_antisymm hJCC hCC) inferInstance hnab
      fun hT => not_isLThreeFour_of_lieModel_two hmodel (by decide) hT

theorem up34C2Out_uni_model {n f : ℕ} (hn : 3 ≤ n) (hD : Up34C2OutDiagUniAt n)
    (hadm : StatedLieAdmissible .PSU n 2 f) {S : Type} [Group S] [Finite S]
    (hm : Blueprint.LieModel S .PSU n 2 f) (α : MulAut S)
    (hα : α ∉ (MulAut.conj : S →* MulAut S).range) (hp : Up34Pumpup S α) : False := by
  obtain ⟨K, _, h, ⟨e⟩⟩ := exists_psu_model hadm hm
  haveI := h.finite
  haveI : Finite (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    Finite.of_equiv S e.toEquiv
  have hne : ¬(n = 3 ∧ 2 ^ f = 2) := fun ⟨h1, h2⟩ => hadm.2.2.2 (by rw [h1, h2])
  have hψ3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, ((up34Pumpup_iff α).1 hp).1, map_one]
  have hψinn : MulAut.congr e α ∉ inner (primeFormP h ((1 : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) := fun hin => hα ((congr_mem_inner_iff_of_equiv e α).mp hin)
  by_cases hσ : primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn hne (MulAut.congr e α) = 1
  · have hD' : MulAut.congr e α ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← ker_primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn hne]
      exact hσ
    exact hD f K h hn hne _ hD' hψinn (hp.of_congr e)
  · obtain ⟨σ, u, hσord, hu⟩ := exists_conj_fieldAut_of_factor_ne_one h hn hne hψ3 hσ
    have h1 : NoL34Layer (MulAut.congr e α) := by
      rw [hu]
      exact noL34Layer_conj u (noL34Layer_fieldAut_psu h hn hσord)
    exact ((up34Pumpup_iff α).1 hp).2.2 (noL34Layer_congr e h1)

end Field

end Up34Chev2

section Family


theorem statedLieAdmissible_twistedA {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) :
    StatedLieAdmissible .PSU (r + 1) q.p q.exponent := by
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  refine ⟨q.prime_p, q.exponent_pos, by omega, fun hc => ?_⟩
  have h1 := (Prod.mk.inj hc).1
  have h2 := (Prod.mk.inj hc).2
  have : r = 2 := by omega
  subst this
  have := hr.2 rfl
  rw [TauCeti.PrimePower.card_def, h2] at this
  omega

theorem up34C2Out_twA2_of_diag (hD : Up34C2OutDiag_TwA2) : Up34Chev2Out FamTwA2 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | twistedA r q =>
    exfalso
    have hq2 : q.p = 2 := hc
    have hr2 : r = 2 := hF
    subst hr2
    have hm := blueprintLieModel_twistedA 2 q hv e
    have hadm := statedLieAdmissible_twistedA hv
    rw [hq2] at hm hadm
    exact up34C2Out_uni_model (by norm_num) hD hadm hm α hα hp
  | _ => exact hF.elim

theorem up34C2Out_twAHigh_of_diag (hD : Up34C2OutDiag_TwAHigh) : Up34Chev2Out FamTwAHigh := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | twistedA r q =>
    exfalso
    have hq2 : q.p = 2 := hc
    have hr3 : 3 ≤ r := hF
    have hm := blueprintLieModel_twistedA r q hv e
    have hadm := statedLieAdmissible_twistedA hv
    rw [hq2] at hm hadm
    exact up34C2Out_uni_model (by omega) (hD (r + 1) (by omega)) hadm hm α hα hp
  | _ => exact hF.elim

end Family

end CFSG.HardMathSupport.Dickson.Sec6
