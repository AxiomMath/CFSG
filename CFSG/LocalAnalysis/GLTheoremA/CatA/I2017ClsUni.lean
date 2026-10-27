module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017ClsInn
import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusLinearTransport
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxUnitary
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2017Cls

open CFSG.Open (StatedSU)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived
  exists_primeFormConjHom_pow_scalar_of_mem_innAutDerived)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

private theorem card_alt_eight_uni : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 8)
  rw [Nat.card_perm, Nat.card_fin] at h
  have h8 : (8 : ℕ).factorial = 40320 := by decide
  omega

private theorem le_six_of_two_pow_dvd_alt {t : ℕ} (h : 2 ^ t ∣ 20160) : t ≤ 6 := by
  rw [show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num] at h
  have h64 : 2 ^ t ∣ 2 ^ 6 :=
    Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.pow_left t (Nat.coprime_two_left.mpr (by norm_num : Odd 315))) h
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h64

private theorem two_pow_dvd_card_centerQuotient_su {E : Type} [Field E] [Finite E] {m f : ℕ}
    (hm : 3 ≤ m) (hf : 1 ≤ f) (hne : (m, 2 ^ f) ≠ (3, 2)) (hE : Nat.card E = (2 ^ f) ^ 2)
    {T : Type*} [Group T] (g : ↥(StatedSU m (2 ^ f) E) →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center ↥(StatedSU m (2 ^ f) E))
    (hperf : commutator ↥(StatedSU m (2 ^ f) E) = ⊤) :
    2 ^ (f * (m * (m - 1) / 2)) ∣ Nat.card (T ⧸ Subgroup.center T) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP E 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := f) hE
  have hUF : UnitaryFieldData 2 f E := CFSG.RankThree.PartOne.KFU.unitaryFieldData_two hE hf
  have hQ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := E) (p := 2)
    (f := f) hE hm hne
  have hZ : Nat.card (Subgroup.center ↥(StatedSU m (2 ^ f) E)) = Nat.gcd m (2 ^ f + 1) := by
    rw [hQ.2]
    exact CFSG.LocalAnalysis.RankFourTheoremC.card_scalars_statedSU (K := E) (r := 2)
      (f := f) hE (by omega)
  have hZodd : Odd (Nat.card (Subgroup.center ↥(StatedSU m (2 ^ f) E))) := by
    rw [hZ]
    refine Odd.of_dvd_nat ?_ (Nat.gcd_dvd_right _ _)
    obtain ⟨k, hk⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
    rw [hk, pow_succ]
    exact ⟨2 ^ k, by ring⟩
  have hsplit := KD264Lie.card_eq_card_centerQuotient_mul_card_center_of_surjective hperf g hg hker
  have hdvd : 2 ^ (f * (m * (m - 1) / 2)) ∣
      Nat.card (T ⧸ Subgroup.center T) * Nat.card (Subgroup.center ↥(StatedSU m (2 ^ f) E)) := by
    rw [← hsplit, KD264Lie.card_statedSU_eq_nat hUF (by omega), ← pow_mul]
    exact dvd_mul_right _ _
  exact Nat.Coprime.dvd_of_dvd_mul_right
    (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hZodd)) hdvd

private theorem false_of_sl_alt_eight {E : Type} [Field E] [Fintype E] {m e : ℕ} (hm : 2 ≤ m)
    (he : 2 ≤ e) (hE : Fintype.card E = 2 ^ e) {X : Type} [Group X]
    (g : Matrix.SpecialLinearGroup (Fin m) E →* X) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E))
    (eX : X ⧸ Subgroup.center X ≃* ↥(alternatingGroup (Fin 8))) : False := by
  classical
  have h4 : 4 ≤ Fintype.card E := by
    rw [hE]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hperf := (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds E m hm
    (fun _ => h4)).perfect
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin m) E) := Group.isPerfect_def.mpr hperf
  have hE' : Nat.card E = 2 ^ e := by rw [Nat.card_eq_fintype_card, hE]
  have hcardQ : Nat.card (X ⧸ Subgroup.center X) = 20160 := by
    rw [Nat.card_congr eX.toEquiv, card_alt_eight_uni]
  have h2 := KD264Lie.pow_dvd_card_centerQuotient_of_surjective_specialLinear (by omega)
    (by omega) hE' g hg hker hperf
  rw [hcardQ] at h2
  have hb := le_six_of_two_pow_dvd_alt h2
  have hm3 : m ≤ 3 := by
    by_contra hc
    have h12 : 4 * 3 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
    have h6 : 6 ≤ m * (m - 1) / 2 := by omega
    have h12' : 2 * 6 ≤ e * (m * (m - 1) / 2) := Nat.mul_le_mul he h6
    omega
  rcases (show m = 2 ∨ m = 3 by omega) with rfl | rfl
  ·
    norm_num at hb
    have hsplit :=
      KD264Lie.card_eq_card_centerQuotient_mul_card_center_of_surjective hperf g hg hker
    rw [hcardQ, LinearFlag.card_SL_eq (K := E) (n := 2) (by norm_num), hE'] at hsplit
    have hz : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E)) ≤ 2 := by
      rw [Nat.card_congr
        (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 2)).toEquiv]
      exact (card_rootsOfUnity (k := Fintype.card (Fin 2)) (R := E)).trans_eq
        (Fintype.card_fin 2)
    generalize Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E)) = z at hsplit hz
    interval_cases e <;> norm_num [Finset.Icc_self] at hsplit <;> omega
  ·
    have he2 : e = 2 := by
      norm_num at hb
      omega
    subst he2
    exact CFSG.HardMathSupport.Solomon.Coordinator.false_of_projectiveSL_alt_eight (F := E)
      (by rw [hE']; norm_num)
      (((QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center 3 E)).trans
        (CFSG.ComponentClassification.PerfectCentralQuotient.equivalence g hg hker)).trans eX)

private theorem false_of_su_alt_eight {E : Type} [Field E] [Fintype E] {m Q f : ℕ}
    (hQ : Q = 2 ^ f) (hm : 3 ≤ m) (hf : 1 ≤ f) (hne : (m, Q) ≠ (3, 2))
    (hE : Fintype.card E = Q ^ 2) {X : Type} [Group X] (g : ↥(StatedSU m Q E) →* X)
    (hg : Function.Surjective g) (hker : g.ker ≤ Subgroup.center ↥(StatedSU m Q E))
    (eX : X ⧸ Subgroup.center X ≃* ↥(alternatingGroup (Fin 8))) : False := by
  classical
  subst hQ
  have hperf := (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds E m (2 ^ f)
    hE hm hne).perfect
  have hE' : Nat.card E = (2 ^ f) ^ 2 := by rw [Nat.card_eq_fintype_card, hE]
  have hcardQ : Nat.card (X ⧸ Subgroup.center X) = 20160 := by
    rw [Nat.card_congr eX.toEquiv, card_alt_eight_uni]
  have h2 := two_pow_dvd_card_centerQuotient_su hm hf hne hE' g hg hker hperf
  rw [hcardQ] at h2
  have hb := le_six_of_two_pow_dvd_alt h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP E 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := f) hE'
  have hUF : UnitaryFieldData 2 f E := CFSG.RankThree.PartOne.KFU.unitaryFieldData_two hE' hf
  have hsplit := KD264Lie.card_eq_card_centerQuotient_mul_card_center_of_surjective hperf g hg hker
  rw [hcardQ] at hsplit
  generalize Nat.card (Subgroup.center ↥(StatedSU m (2 ^ f) E)) = z at hsplit
  have hm4 : m ≤ 4 := by
    by_contra hc
    have h20 : 5 * 4 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
    have h10 : 10 ≤ m * (m - 1) / 2 := by omega
    have h10' : 1 * 10 ≤ f * (m * (m - 1) / 2) := Nat.mul_le_mul hf h10
    omega
  rcases (show m = 3 ∨ m = 4 by omega) with rfl | rfl
  ·
    have hf2 : f = 2 := by
      have hf1 : f ≠ 1 := by
        rintro rfl
        exact hne rfl
      norm_num at hb
      omega
    subst hf2
    have hval : Nat.card ↥(StatedSU 3 (2 ^ 2) E) = 62400 := by
      rw [KD264Lie.card_statedSU_eq_nat hUF (by norm_num)]
      decide
    rw [hval] at hsplit
    omega
  ·
    have hf1 : f = 1 := by
      norm_num at hb
      omega
    subst hf1
    have hval : Nat.card ↥(StatedSU 4 (2 ^ 1) E) = 25920 := by
      rw [KD264Lie.card_statedSU_eq_nat hUF (by norm_num)]
      decide
    rw [hval] at hsplit
    omega

theorem uniTwoNoA8_holds : UniTwoNoA8 := by
  intro n d hd _ _ β hmem hβ3 _ hA8
  classical
  have hU : KD264Lie.isUnitaryIdx d.1 := by rw [hd]; trivial
  obtain ⟨r, q', K, hKf, h, hr, hd', hne, ⟨eP⟩⟩ :=
    KD264Lie.exists_primeFormP_mulEquiv_of_isUnitaryIdx hU
  obtain ⟨-, hq'⟩ := TauCeti.LieTypeIndex.twistedA.inj (hd.symm.trans hd')
  have hp2 : q'.p = 2 := by rw [← hq']; rfl
  have hexp : q'.exponent = 1 := by rw [← hq']; rfl
  let θ : (TauCeti.CFSGIndex.lie d).Group ≃* primeFormP h (idGram K (r + 1)) := eP.symm
  let β' : MulAut (primeFormP h (idGram K (r + 1))) := θ.symm.trans (β.trans θ)
  have hβ'mem : β' ∈ innAutDerived (primeFormP h (idGram K (r + 1))) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr θ).2 hmem
  have hβ'3 : β' ^ 3 = 1 := by
    have h3 := map_pow (MulAut.congr θ) β 3
    rw [hβ3, map_one] at h3
    exact h3.symm
  have hq'' : ¬(r + 1 = 3 ∧ q'.p ^ q'.exponent = 2) := by
    rintro ⟨h1, h2⟩
    exact hne ⟨h1, by rw [TauCeti.PrimePower.card_def]; exact h2⟩
  obtain ⟨A, c, -, hA, hβeq⟩ :=
    exists_primeFormConjHom_pow_scalar_of_mem_innAutDerived h isPrimeFormGram_idGram (by omega)
      hq'' hβ'mem hβ'3
  obtain ⟨J, -, hJc, ⟨eJ⟩⟩ := hA8
  have hfix := CFSG.LocalAnalysis.GLTheoremA.map_fixSubgroup θ β
  have hK : CFSG.Open.IsComponentOf (J.map θ.toMonoidHom)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (primeFormConjHom h (idGram K (r + 1)) A)) := by
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map θ hJc
    rw [← hβeq]
    exact hfix ▸ h1
  have eJK : ↥J ≃* ↥(J.map θ.toMonoidHom) := J.equivMapOfInjective θ.toMonoidHom θ.injective
  have eK : ↥(J.map θ.toMonoidHom) ⧸ Subgroup.center ↥(J.map θ.toMonoidHom) ≃*
      ↥(alternatingGroup (Fin 8)) :=
    (QuotientGroup.congr _ _ eJK (Subgroup.map_center_eq eJK)).symm.trans eJ
  have hpℓ : 3 ≠ q'.p := by rw [hp2]; norm_num
  obtain ⟨dd, hdd, hcase⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_factor_of_component_primeFormConjHom
      (h := h) Nat.prime_three hpℓ A hA _ hK
  rcases hcase with
      ⟨F, hF, hFt, -, hcardF, h4, g, hg, hk⟩ |
      ⟨E, hE, hEt, m, -, hcardE, hm, hne', g, hg, hk⟩ |
      ⟨E, hE, hEt, m, -, hcardE, hm2, -, g, hg, hk⟩
  · letI : Field F := hF
    letI : Fintype F := hFt
    rw [hp2, hexp, one_mul] at hcardF
    have hdd2 : 2 ≤ dd := by
      by_contra hlt
      have h2 : 2 ^ dd ≤ 2 := by
        calc 2 ^ dd ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 2 := by norm_num
      rw [hcardF] at h4
      omega
    exact false_of_sl_alt_eight le_rfl hdd2 hcardF g hg hk eK
  · letI : Field E := hE
    letI : Fintype E := hEt
    exact false_of_su_alt_eight (f := dd) (by rw [hp2, hexp, one_mul]) hm hdd hne' hcardE g hg hk
      eK
  · letI : Field E := hE
    letI : Fintype E := hEt
    rw [hp2, hexp, one_mul] at hcardE
    exact false_of_sl_alt_eight hm2 (e := 2 * dd) (by omega) hcardE g hg hk eK

end CFSG.LocalAnalysis.GLTheoremA.I2017Cls

end
