module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutLin

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.Sec66T
  CFSG.ComponentClassification.RankTwoClassical
  CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
  CFSG.ComponentClassification.CatLeaf CFSG.HardMathSupport.Dickson.Sec6.I923
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs CFSG.LocalAnalysis.GLTheoremB
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open Matrix CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.Classical CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.Coordinator
open scoped commutatorElement

section PslThree

theorem noL34OuterAt3_pslGood (hO : LieOrderFormulasInput) :
    NoL34OuterAtThree FamPslGood := by
  intro P _ _ t n f hadm ht hF hm ψ hψ3 hψ
  obtain ⟨rfl, hn3, hcop⟩ := hF
  have hC : StatedClassicalModel P .PSL n 3 f := (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  rw [← hK] at hcop
  let e : P ≃* projectiveSL n K := e0.trans (statedProjEquiv n K)
  haveI : Finite (projectiveSL n K) := Finite.of_equiv P e.toEquiv
  refine noL34Layer_congr e ?_
  have hψ3' : (MulAut.congr e ψ) ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hD : MulAut.congr e ψ ∉ linearAutGroup n K := fun hD =>
    hψ ((congr_mem_inner_iff_of_equiv e ψ).mp
      (inner_of_mem_linearAut_of_pow_eq_one hn3 hcop hD hψ3'))
  obtain ⟨σ, hσ, H, hψH⟩ := linear_order_three_field_descent hn3 _ hψ3' hD
  rw [hψH]
  exact noL34Layer_conj _
    (noL34Layer_fieldAut_psl hO hn3 hσ hcop hadm.1 (by decide) hadm.2.1 hK)

theorem noL34OuterAt3_pslTwo (hO : LieOrderFormulasInput) : NoL34OuterAtThree FamPslTwo := by
  intro P _ _ t n f hadm ht hF hm ψ hψ3 hψ
  have hp2 : (3 : ℕ) ≠ 2 := by decide
  obtain ⟨rfl, rfl⟩ := hF
  have hC : StatedClassicalModel P .PSL 2 3 f := (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  haveI : Finite (StatedProj (StatedSL 2 K)) := Finite.of_equiv P e0.toEquiv
  refine noL34Layer_congr e0 ?_
  have hβ3 : (MulAut.congr e0 ψ) ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβ1 : MulAut.congr e0 ψ ≠ 1 := fun h =>
    hψ ((congr_mem_inner_iff_of_equiv e0 ψ).mp (h ▸ one_mem _))
  rcases Solomon.Coordinator.l2Aut3Classification_holds K _ hβ3 with h | hsol | ⟨σ, φ, γ, hφ, hβ⟩
  · exact absurd h hβ1
  · exact noL34Layer_of_fixed_solvable_lin _ hsol
  · obtain ⟨F₀, hF₀f, hF₀fin, hcard, ⟨ψ0⟩⟩ :=
      Solomon.Coordinator.l2FieldFixed_holds K _ hβ3 hβ1 σ φ γ hφ hβ
    have hdvd : Nat.card F₀ ∣ 3 ^ f := by
      rw [← hK, hcard]
      exact dvd_pow_self _ (by norm_num)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hj1 : 1 ≤ j := by
      by_contra h0
      have h1 : 1 < Nat.card F₀ := Finite.one_lt_card
      rw [hj, show j = 0 by omega] at h1
      simp at h1
    by_cases hj2 : 2 ≤ j
    · have h9 : 9 ≤ 3 ^ j := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
      have hadm₀ : StatedLieAdmissible .PSL 2 3 j :=
        ⟨Nat.prime_three, hj1, le_rfl, fun hc => by have := (Prod.mk.inj hc).2; omega,
          fun hc => by have := (Prod.mk.inj hc).2; omega⟩
      have hmodel : LieModel (StatedProj (StatedSL 2 F₀)) .PSL 2 3 j :=
        (lieModel_classical_iff (by decide)).mpr
          ⟨hadm₀, F₀, inferInstance, inferInstance, hj, ⟨MulEquiv.refl _⟩⟩
      obtain ⟨hq, hz⟩ := Solomon.Coordinator.l2fld_isQuasisimple_psl2 (F := F₀) (by omega)
      haveI : IsSimpleGroup (StatedProj (StatedSL 2 F₀)) :=
        isSimpleGroup_of_quasisimple_of_center_bot_lin hq hz
      exact noL34Layer_of_fixed_equiv _ ψ0 inferInstance (exists_noncomm_of_center_bot hz)
        (not_isLThreeFour_of_lieModel_odd hO hp2 hmodel)
    · obtain rfl : j = 1 := by omega
      have hle : Nat.card F₀ ≤ 3 := by rw [hj]; norm_num
      haveI : Group.IsSolvable (StatedProj (StatedSL 2 F₀)) :=
        Solomon.Coordinator.l2fld_isSolvable_psl2_of_card_le_three hle
      haveI : Group.IsSolvable ↥(fixSubgroup (MulAut.congr e0 ψ)) :=
        Group.isSolvable_of_isSolvable_injective (f := ψ0.toMonoidHom) ψ0.injective
      exact noL34Layer_of_fixed_solvable_lin _ inferInstance

end PslThree

section PsuThree

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem noL34Layer_fieldAut_psu_odd (hO : LieOrderFormulasInput) (h : UnitaryFieldData ℓ f K)
    (hn : 3 ≤ n) (hℓ2 : ℓ ≠ 2) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    NoL34Layer (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) := by
  classical
  have hfin := h.finite
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by decide
  have hℓ3 : 3 ≤ ℓ := by have := h.prime.two_le; omega
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  obtain ⟨h3f, hcard⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  have hf0 : 1 ≤ f / 3 := by
    have : 3 ≤ f := Nat.le_of_dvd (by have := h.one_le; omega) h3f
    omega
  have hq0 : ¬(n = 3 ∧ ℓ ^ (f / 3) = 2) := fun ⟨_, h2⟩ => by
    have : ℓ ≤ ℓ ^ (f / 3) := Nat.le_self_pow (by omega) ℓ
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
  have hadm₀ : StatedLieAdmissible .PSU n ℓ (f / 3) :=
    ⟨h.prime, hf0, hn, fun hc => hq0 ⟨(Prod.mk.inj hc).1, (Prod.mk.inj hc).2⟩⟩
  have hcard' : Nat.card (fixSubfield σ) = (ℓ ^ (f / 3)) ^ 2 := by
    rw [hcard, ← pow_mul, mul_comm]
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h₀
    (isPrimeFormGram_one (n := n) (K := fixSubfield σ))
  have hmodel : LieModel ↥j.range .PSU n ℓ (f / 3) :=
    (lieModel_classical_iff (by decide)).mpr
      ⟨hadm₀, ↥(fixSubfield σ), inferInstance, inferInstance, hcard',
        ⟨(eJ.symm.trans eP).trans (unitaryPSUEquiv h₀ (by omega))⟩⟩
  exact noL34_of_simple_normal_comm _ j.range hJC hCC inferInstance hnab
    (not_isLThreeFour_of_lieModel_odd hO hℓ2 hmodel)

theorem noL34OuterAt3_psuGood (hO : LieOrderFormulasInput) : NoL34OuterAtThree FamPsuGood := by
  intro P _ _ t n f hadm ht hF hm ψ hψ3 hψ
  obtain ⟨rfl, hn3, hdiv⟩ := hF
  obtain ⟨K, _, h, ⟨e0⟩⟩ := exists_psu_model hadm hm
  have hne : ¬(n = 3 ∧ 3 ^ f = 2) := fun ⟨h1, h2⟩ => hadm.2.2.2 (by rw [h1, h2])
  haveI : Finite (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    Finite.of_equiv P e0.toEquiv
  refine noL34Layer_congr e0 ?_
  have hψ3' : (MulAut.congr e0 ψ) ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hσ1 : primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn3 hne
      (MulAut.congr e0 ψ) ≠ 1 := by
    intro hσ1
    have hD : MulAut.congr e0 ψ ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← ker_primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn3 hne]
      exact hσ1
    exact hψ ((congr_mem_inner_iff_of_equiv e0 ψ).mp
      (mem_inner_of_mem_primeFormD h hn3 hne Nat.prime_three hdiv hD hψ3'))
  obtain ⟨σ, u, hσord, hu⟩ := exists_conj_fieldAut_of_factor_ne_one h hn3 hne hψ3' hσ1
  rw [hu]
  exact noL34Layer_conj _ (noL34Layer_fieldAut_psu_odd hO h hn3 (by decide) hσord)

end PsuThree

end CFSG.HardMathSupport.Dickson.Sec6
