module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutCharTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutUni

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.PartOne.Sec66T
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartTwo.KFacts
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.HardMathSupport.Dickson.Sec6
  (FamTwA2 FamTwAHigh statedLieAdmissible_twistedA blueprintLieModel_twistedA)
open CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2
open CFSG.LocalAnalysis.GLTheoremA.I1431C2 (mem_innAutDerived_of_primeFormD_pow_three)
open scoped commutatorElement

section Field

variable {T Pc : TauCeti.CFSGIndex → Prop} {tm tf tN : ℕ}

variable {ℓ f n : ℕ} {K : Type} [Field K]


theorem typeLayer_fieldAut_psu (hD : LieSOutType T tm tf tN) (h : UnitaryFieldData 2 f K)
    (hn : 3 ≤ n) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    TypeLayer T (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) False := by
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
    exact typeSub_of_commutator_solvable _ j.range hCC inferInstance
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
    have hadm₀ : StatedLieAdmissible .PSU n 2 (f / 3) :=
      ⟨Nat.prime_two, hf0, hn, fun hc => hq0 ⟨(Prod.mk.inj hc).1, (Prod.mk.inj hc).2⟩⟩
    have hcard' : Nat.card (fixSubfield σ) = (2 ^ (f / 3)) ^ 2 := by
      rw [hcard, ← pow_mul, mul_comm]
    obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h₀
      (isPrimeFormGram_one (n := n) (K := fixSubfield σ))
    have hmodel : Blueprint.LieModel ↥j.range .PSU n 2 (f / 3) :=
      (lieModel_classical_iff (by decide)).mpr
        ⟨hadm₀, ↥(fixSubfield σ), inferInstance, inferInstance, hcard',
          ⟨(eJ.symm.trans eP).trans (unitaryPSUEquiv h₀ (by omega))⟩⟩
    refine typeLayer_of_simple_commutator _ j.range (le_antisymm ?_ hCC) inferInstance hnab
      fun hT => ?_
    · haveI hperf₀ : Group.IsPerfect (primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
          Matrix (Fin n) (Fin n) (fixSubfield σ))) := by
        have := isPerfect_gramSU_one h₀ hn hq0
        exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _)
          (QuotientGroup.mk'_surjective _)
      calc j.range = ⁅j.range, j.range⁆ := range_eq_commutator_of_perfect j
        _ ≤ _ := Subgroup.commutator_mono hJC hJC
    · exact absurd (hD.det hT hmodel).1 (by decide)

theorem lieSOut_uni_model (hD : LieSOutType T tm tf tN) {n f : ℕ} (hn : 3 ≤ n)
    (hadm : StatedLieAdmissible .PSU n 2 f) {S : Type} [Group S] [Finite S]
    (hm : Blueprint.LieModel S .PSU n 2 f) (α : MulAut S) (hα : α ∉ innAutDerived S)
    (hp : TypePumpup T S α) : False := by
  obtain ⟨K, _, h, ⟨e⟩⟩ := exists_psu_model hadm hm
  haveI := h.finite
  haveI : Finite (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    Finite.of_equiv S e.toEquiv
  have hne : ¬(n = 3 ∧ 2 ^ f = 2) := fun ⟨h1, h2⟩ => hadm.2.2.2 (by rw [h1, h2])
  have hψ3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hp.1, map_one]
  by_cases hσ :
      primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn hne (MulAut.congr e α) = 1
  · have hD' : MulAut.congr e α ∈
        primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← ker_primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn hne]
      exact hσ
    exact hα ((mem_innAutDerived_congr e).mp
      (mem_innAutDerived_of_primeFormD_pow_three h hψ3 hD'))
  · obtain ⟨σ, u, hσord, hu⟩ := exists_conj_fieldAut_of_factor_ne_one h hn hne hψ3 hσ
    have h1 : TypeLayer T (MulAut.congr e α) False := by
      rw [hu]
      exact typeLayer_conj u (typeLayer_fieldAut_psu hD h hn hσord)
    exact hp.apply (typeLayer_congr e h1)

theorem lieSOut_twA2 (hD : LieSOutType T tm tf tN) : TypeOuterAt T Pc FamTwA2 := by
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
    exact lieSOut_uni_model hD (by norm_num) hadm hm α hα hp
  | _ => exact hF.elim

theorem lieSOut_twAHigh (hD : LieSOutType T tm tf tN) : TypeOuterAt T Pc FamTwAHigh := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | twistedA r q =>
    exfalso
    have hq2 : q.p = 2 := hc
    have hr3 : 3 ≤ r := hF
    have hm := blueprintLieModel_twistedA r q hv e
    have hadm := statedLieAdmissible_twistedA hv
    rw [hq2] at hm hadm
    exact lieSOut_uni_model hD (by omega) hadm hm α hα hp
  | _ => exact hF.elim

end Field

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
