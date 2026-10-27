module

public import CFSG.LieType.Steinberg.CentralExt.SpinMinusPosLift
public import CFSG.LieType.Steinberg.CentralExt.CoprimeSplit
public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo

public section

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Steinberg

namespace CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed

variable {n : ℕ} {K : Type} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

theorem shortRels_h_eq_one' [Finite K] [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)] (i : Fin (n - 1))
    {t : ShortField b c} (ht : t ≠ 0) (h1 : (shortRels n hirr i).h t = 1) : t = 1 := by
  by_cases h2 : (2 : K) = 0
  · set a := fieldCoord t with ha_def
    have ha : a ≠ 0 := fieldCoord_ne_zero ht
    rw [shortRels_h] at h1
    have hN : planeNorm b c a = 1 := by
      have he := spinAction_shortTorusElt_eVec n hirr i ha
      rw [h1, map_one] at he
      have := congrFun (congrArg (fun v => (v : Vm n K)) he) (.inl i)
      simpa [eVec] using this.symm
    have hrefl : ∀ q, planeRefl b c a q = planeRefl b c planeOne q := by
      intro q
      have hp := spinAction_shortTorusElt_planeVec n hirr i ha (planeRefl b c planeOne q)
      rw [h1, map_one, planeRefl_planeRefl planeNorm_planeOne_ne_zero] at hp
      exact (planeVec_injective n hp).symm
    have hs1 : planeRefl b c planeOne planeOne = planeOne := by
      have hB1 : polarPlane b c (planeOne : Fin 2 → K) planeOne = 0 := by
        simp [polarPlane, planeOne, h2]
      rw [planeRefl, hB1, zero_div, zero_smul, sub_zero]
    have h0 := hrefl planeOne
    rw [hs1, planeRefl, hN, div_one] at h0
    have hBa : polarPlane b c planeOne a = 0 :=
      (smul_eq_zero.1 (sub_eq_self.1 h0)).resolve_right ha
    have hB : polarPlane b c planeOne a = 2 * a 0 + b * a 1 := by
      simp [polarPlane, planeOne]
    have hb0 : b ≠ 0 := by
      rintro rfl
      have : Fintype K := Fintype.ofFinite K
      have hc2 : ringChar K = 2 := by
        obtain ⟨p, hp, hpc⟩ := TorusLift.exists_prime_charP (k := K)
        have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).1 (by exact_mod_cast h2)
        rw [ringChar.eq K p, (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 hdvd]
      obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two hc2 c
      apply hirr r
      rw [hr]
      linear_combination r ^ 2 * h2
    have ha1 : a 1 = 0 := by
      rw [hB, h2, zero_mul, zero_add] at hBa
      exact (mul_eq_zero.1 hBa).resolve_left hb0
    have ha0 : a 0 = 1 := by
      simp only [planeNorm, ha1] at hN
      have hsq : (a 0 - 1) ^ 2 = 0 := by linear_combination hN + (1 - a 0) * h2
      exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq)
    have hre : t.re = a 0 := rfl
    have him : t.im = a 1 := rfl
    exact QuadraticAlgebra.ext (hre.trans (ha0.trans QuadraticAlgebra.re_one.symm))
      (him.trans (ha1.trans QuadraticAlgebra.im_one.symm))
  · exact shortRels_h_eq_one hirr h2 i ht h1

include hirr in
theorem spinMinus_exists_section_of_coprime [Finite K] (hn : 4 ≤ n) {p : ℕ}
    [Fact p.Prime] [CharP K p] {E : Type*} [Group E] [Finite E]
    {π : E →* spinGroup (quadMinus n K b c)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hC : p.Coprime (Nat.card π.ker)) :
    ∃ s : spinGroup (quadMinus n K b c) →* E, ∀ g, π (s g) = g := by
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) p :=
    charP_of_injective_algebraMap (algebraMap K (ShortField b c)).injective p
  have hC' : ¬ p ∣ Nat.card π.ker := (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hC
  refine (existsUnique_section_of_rankOne_lift
    (minusDatum_isCTGroupDatum n hirr hn) (minusDatum_steinbergExtras n hirr)
    (fun _ hγ => isPGroup_minusRootGroup hirr hγ) hπ hcen hC' fun i => ?_).exists
  by_cases hi : i.val + 1 < n - 1
  · obtain ⟨ρ', hρ', -⟩ := CFSG.SectionRank.EvenCover.sl2_existsUnique_lift (p := p) hπ hcen hC'
      ((minusFrame n b c).longSL2 (succ_ne_of_lt n hi) true false)
    exact exists_lift_of_injective (SpinFrame.longSL2_injective _ _ _ _)
      (rankOne_minusRootGroup_of_lt n hirr hi).le fun g => DFunLike.congr_fun hρ' g
  · exact exists_rankOne_lift_of_rankOneRels (minusDatum_steinbergExtras n hirr) i
      (shortRels n hirr i) (mem_minusRootGroup_single_iff hirr hi)
      (mem_minusRootGroup_neg_single_iff hirr hi) (shortRels_x_injective hirr i)
      (fun t ht h1 => shortRels_h_eq_one' hirr i ht h1) hπ hcen hC'

include hirr in
theorem spinMinus_exists_section_of_central [Finite K] (hn : 4 ≤ n)
    (hK : 4 ≤ Nat.card K) {E : Type} [Group E] [Finite E]
    {π : E →* spinGroup (quadMinus n K b c)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ s : spinGroup (quadMinus n K b c) →* E, ∀ g, π (s g) = g := by
  obtain ⟨p, _, _⟩ := TorusLift.exists_prime_charP (k := K)
  exact CoprimeSplit.exists_section_of_parts (p := p) hπ hcen
    (fun _ _ _ _ hπ' hcen' hp' => spinMinus_exists_section_of_pKernel hirr hn hK hπ' hcen' hp')
    (fun _ _ _ _ hπ' hcen' hc' => spinMinus_exists_section_of_coprime hirr hn hπ' hcen' hc')

end CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed
