module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkDefs
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Split
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkBase
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutLin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartTwo.KFacts
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.Sec66T
  CFSG.ComponentClassification.RankTwoClassical CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
  CFSG.HardMathSupport.Dickson.Sec6 CFSG.HardMathSupport.Dickson.Sec6.I923
open Matrix CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.Classical CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup l2Aut3Classification_holds
  l2FieldFixed_holds l2fld_isQuasisimple_psl2 l2fld_isSolvable_psl2_of_card_le_three)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

private theorem outerSubThree_fieldAut_psl {n f : ℕ} (hn3 : 3 ≤ n) {K : Type} [Field K]
    [Finite K] {σ : K ≃+* K} (hσ : orderOf σ = 3)
    (hcop : Nat.Coprime 3 (Nat.gcd n (Nat.card K - 1))) (hf : 1 ≤ f)
    (hK : Nat.card K = 3 ^ f) : OuterSubThree .PSL n f (fixSubgroup (fieldAut n K σ)) := by
  set k := semilinearFixedSubfield σ
  have hfixset := fixedSubgroup_fieldAut_eq_range_gen hn3 Nat.prime_three hcop hσ
  have hinj := linearSubfieldInclusion_injective (by omega : 0 < n) k
  have hfix : fixSubgroup (fieldAut n K σ) = (linearSubfieldInclusion n k).range := by
    ext x
    exact Iff.of_eq (congrArg (x ∈ ·) hfixset)
  let eD : ↥(fixSubgroup (fieldAut n K σ)) ≃* projectiveSL n ↥k :=
    (MulEquiv.subgroupCongr hfix).trans (MonoidHom.ofInjective hinj).symm
  haveI : IsSimpleGroup (projectiveSL n ↥k) := KCLinearSubfield.isSimpleGroup_projectiveSL hn3
  have hnab : ∃ a b : projectiveSL n ↥k, a * b ≠ b * a := by
    have h1 := KCLinearSubfield.not_commutative_projectiveSL (n := n) (K := ↥k) hn3
    push Not at h1
    exact h1
  obtain ⟨h3f, hkcard⟩ := card_semilinearFixedSubfield Nat.prime_three hf hK hσ
  have hf0 : 1 ≤ f / 3 := by
    have : 3 ≤ f := Nat.le_of_dvd (by omega) h3f
    omega
  have hadm : StatedLieAdmissible .PSL n 3 (f / 3) :=
    ⟨Nat.prime_three, hf0, by omega, fun hc => by have := (Prod.mk.inj hc).1; omega,
      fun hc => by have := (Prod.mk.inj hc).1; omega⟩
  have hmodel : LieModel (projectiveSL n ↥k) .PSL n 3 (f / 3) :=
    (lieModel_classical_iff (by decide)).mpr
      ⟨hadm, ↥k, inferInstance, inferInstance, hkcard, ⟨(statedProjEquiv n ↥k).symm⟩⟩
  exact outerSubThree_of_fixed_equiv _ eD inferInstance hnab
    (outerLayerThree_of_field (by decide) (Nat.mul_div_cancel' h3f) hmodel)

theorem lieOuterThreeAt_pslGood : LieOuterThreeAt FamPslGood := by
  intro P _ _ t n f hadm hF hm ψ hψ3 hψ
  obtain ⟨rfl, hn3, hcop⟩ := hF
  have hC : StatedClassicalModel P .PSL n 3 f := (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  rw [← hK] at hcop
  let e : P ≃* projectiveSL n K := e0.trans (statedProjEquiv n K)
  haveI : Finite (projectiveSL n K) := Finite.of_equiv P e.toEquiv
  refine outerSubThree_congr e ?_
  have hψ3' : (MulAut.congr e ψ) ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hD : MulAut.congr e ψ ∉ linearAutGroup n K := fun hD =>
    hψ ((congr_mem_inner_iff_of_equiv e ψ).mp
      (inner_of_mem_linearAut_of_pow_eq_one hn3 hcop hD hψ3'))
  obtain ⟨σ, hσ, H, hψH⟩ := linear_order_three_field_descent hn3 _ hψ3' hD
  rw [hψH]
  exact outerSubThree_conj _ (outerSubThree_fieldAut_psl hn3 hσ hcop hadm.2.1 hK)

theorem lieOuterThreeAt_pslTwo : LieOuterThreeAt FamPslTwo := by
  intro P _ _ t n f hadm hF hm ψ hψ3 hψ
  obtain ⟨rfl, rfl⟩ := hF
  have hC : StatedClassicalModel P .PSL 2 3 f := (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  haveI : Finite (StatedProj (StatedSL 2 K)) := Finite.of_equiv P e0.toEquiv
  refine outerSubThree_congr e0 ?_
  have hβ3 : (MulAut.congr e0 ψ) ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβ1 : MulAut.congr e0 ψ ≠ 1 := fun h =>
    hψ ((congr_mem_inner_iff_of_equiv e0 ψ).mp (h ▸ one_mem _))
  rcases l2Aut3Classification_holds K _ hβ3 with h | hsol | ⟨σ, φ, γ, hφ, hβ⟩
  · exact absurd h hβ1
  · exact outerSubThree_of_solvable _ hsol
  · obtain ⟨F₀, _, _, hcard, ⟨ψ0⟩⟩ := l2FieldFixed_holds K _ hβ3 hβ1 σ φ γ hφ hβ
    have hdvd : Nat.card F₀ ∣ 3 ^ f := by
      rw [← hK, hcard]
      exact dvd_pow_self _ (by norm_num)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have h33 : 3 ^ f = 3 ^ (3 * j) := by rw [← hK, hcard, hj, ← pow_mul, Nat.mul_comm j 3]
    have h3j : 3 * j = f := (Nat.pow_right_injective (by norm_num) h33).symm
    have hj1 : 1 ≤ j := by have := hadm.2.1; omega
    by_cases hj2 : 2 ≤ j
    · have h9 : 9 ≤ 3 ^ j :=
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
      have hadm₀ : StatedLieAdmissible .PSL 2 3 j :=
        ⟨Nat.prime_three, hj1, le_rfl, fun hc => by have := (Prod.mk.inj hc).2; omega,
          fun hc => by have := (Prod.mk.inj hc).2; omega⟩
      have hmodel : LieModel (StatedProj (StatedSL 2 F₀)) .PSL 2 3 j :=
        (lieModel_classical_iff (by decide)).mpr
          ⟨hadm₀, F₀, inferInstance, inferInstance, hj, ⟨MulEquiv.refl _⟩⟩
      obtain ⟨hq, hz⟩ := l2fld_isQuasisimple_psl2 (F := F₀) (by rw [hj]; omega)
      haveI : IsSimpleGroup (StatedProj (StatedSL 2 F₀)) :=
        isSimpleGroup_of_quasisimple_of_center_bot_lin hq hz
      exact outerSubThree_of_fixed_equiv _ ψ0 inferInstance (exists_noncomm_of_center_bot hz)
        (outerLayerThree_of_field (by decide) h3j hmodel)
    · obtain rfl : j = 1 := by omega
      haveI : Group.IsSolvable (StatedProj (StatedSL 2 F₀)) :=
        l2fld_isSolvable_psl2_of_card_le_three (by rw [hj]; norm_num)
      haveI : Group.IsSolvable ↥(fixSubgroup (MulAut.congr e0 ψ)) :=
        Group.isSolvable_of_isSolvable_injective (f := ψ0.toMonoidHom) ψ0.injective
      exact outerSubThree_of_solvable _ inferInstance

private theorem outerSubThree_fieldAut_psu {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 3 f K) (hn : 3 ≤ n) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    OuterSubThree .PSU n f
      (fixSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ)) := by
  classical
  have hfin := h.finite
  have hp2 : (3 : ℕ) ≠ 2 := by decide
  have hbar := fixSubfield_unitaryFieldData_bar h Nat.prime_three hp2 hσ
  set h₀ := fixSubfield_unitaryFieldData h Nat.prime_three hp2 hσ
  obtain ⟨h3f, hcard⟩ := dvd_and_card_fixSubfield_unitary h Nat.prime_three hp2 hσ
  have hf0 : 1 ≤ f / 3 := by
    have : 3 ≤ f := Nat.le_of_dvd (by have := h.one_le; omega) h3f
    omega
  have hq0 : ¬(n = 3 ∧ 3 ^ (f / 3) = 2) := fun ⟨_, h2⟩ => by
    have : 3 ≤ 3 ^ (f / 3) := Nat.le_self_pow (by omega) 3
    omega
  have hGL : Finite (GL (Fin n) K) :=
    Finite.of_injective (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) Units.val_injective
  have hfinT : Finite (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    inferInstance
  set j := primeSubfieldPSU h Nat.prime_three hp2 hσ n
  have hinj : Function.Injective j := subfieldPSU_injective h h₀ hbar n (by omega)
  have hJC : j.range ≤ fixSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) :=
    range_subfieldPSU_le h n h₀ hbar
  have hCC := commutator_fixed_le_range (n := n) h hσ
  let eJ : primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ)) ≃* ↥j.range := MonoidHom.ofInjective hinj
  haveI := isSimpleGroup_primeFormP_one h₀ hn hq0
  haveI : IsSimpleGroup ↥j.range := eJ.symm.isSimpleGroup
  have hnab : ∃ a b : ↥j.range, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact not_commute_primeFormP_one h₀ hn hq0 fun x y => eJ.injective (by
      rw [map_mul, map_mul]
      exact hcon _ _)
  have hadm₀ : StatedLieAdmissible .PSU n 3 (f / 3) :=
    ⟨Nat.prime_three, hf0, hn, fun hc => hq0 ⟨(Prod.mk.inj hc).1, (Prod.mk.inj hc).2⟩⟩
  have hcard' : Nat.card (fixSubfield σ) = (3 ^ (f / 3)) ^ 2 := by
    rw [hcard, ← pow_mul, mul_comm]
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h₀
    (isPrimeFormGram_one (n := n) (K := fixSubfield σ))
  have hmodel : LieModel ↥j.range .PSU n 3 (f / 3) :=
    (lieModel_classical_iff (by decide)).mpr
      ⟨hadm₀, ↥(fixSubfield σ), inferInstance, inferInstance, hcard',
        ⟨(eJ.symm.trans eP).trans (unitaryPSUEquiv h₀ (by omega))⟩⟩
  exact outerSubThree_of_simple_normal_comm hJC hCC inferInstance hnab
    (outerLayerThree_of_field (by decide) (Nat.mul_div_cancel' h3f) hmodel)

theorem lieOuterThreeAt_psuGood : LieOuterThreeAt FamPsuGood := by
  intro P _ _ t n f hadm hF hm ψ hψ3 hψ
  obtain ⟨rfl, hn3, hdiv⟩ := hF
  obtain ⟨K, _, h, ⟨e0⟩⟩ := exists_psu_model hadm hm
  have hne : ¬(n = 3 ∧ 3 ^ f = 2) := fun ⟨h1, h2⟩ => hadm.2.2.2 (by rw [h1, h2])
  haveI : Finite (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    Finite.of_equiv P e0.toEquiv
  refine outerSubThree_congr e0 ?_
  have hψ3' : (MulAut.congr e0 ψ) ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hσ1 : primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn3 hne
      (MulAut.congr e0 ψ) ≠ 1 := by
    intro hσ1
    have hD : MulAut.congr e0 ψ ∈
        primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← ker_primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn3 hne]
      exact hσ1
    exact hψ ((congr_mem_inner_iff_of_equiv e0 ψ).mp
      (mem_inner_of_mem_primeFormD h hn3 hne Nat.prime_three hdiv hD hψ3'))
  obtain ⟨σ, u, hσord, hu⟩ := exists_conj_fieldAut_of_factor_ne_one h hn3 hne hψ3' hσ1
  rw [hu]
  exact outerSubThree_conj _ (outerSubThree_fieldAut_psu h hn3 hσord)

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
