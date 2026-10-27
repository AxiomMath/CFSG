module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3Order
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3UniBlock
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynTri
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusLinearTransport
public import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.Fitting
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.Mathlib.Arithmetic.TwoPowModThree

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3

open CFSG.Open CFSG.Assembly
open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived
  exists_primeFormConjHom_pow_scalar_of_mem_innAutDerived)

open CFSG.LocalAnalysis.GLTheoremA.I141F.Tri (mem_innAutDerived_of_innDiagKind_of_not_derived)

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (primeFormP primeFormConjHom primeFormUnitary)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram isPrimeFormGram_idGram)

open CFSG.StandardType (MarkedModel markTag markRank markChar markDeg)

open CFSG.SignalizerFunctorTheorem.TransportA (isComponentOf_map)


theorem exists_primeFormP_mulEquiv_of_statedModel_uni {G : Type} [Group G] {N ℓ f : ℕ}
    (h : StatedClassicalModel G .PSU N ℓ f) :
    ∃ (K : Type) (_ : Field K) (hU : UnitaryFieldData ℓ f K),
      Nonempty (G ≃* StatedProj (StatedSU N (ℓ ^ f) K)) ∧
      Nonempty (G ≃* primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) := by
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData ℓ f K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(N = 3 ∧ ℓ ^ f = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  obtain ⟨⟨eT⟩, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_prime_form_full_semilinear_realization
      hU (isPrimeFormGram_idGram (n := N)) hn3 hq
  exact ⟨K, inferInstance, hU, ⟨e⟩,
    ⟨(e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by omega)).symm).trans
      eT.symm⟩⟩

section OrderCerts


theorem U3CoreHyp.card_centerQuot_uni {S : Type} [Group S] {labL : GLALabel} {β : MulAut S}
    {n : ℕ} {J : Subgroup S} (h : U3CoreHyp S labL β n J) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) = ordTwistedA 2 (2 ^ n) := by
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel h.hasLabel
  unfold MarkedModel at hM
  simp only [markTag, markRank, markChar, markDeg] at hM
  rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM]
  norm_num [CFSG.SeitzReduction.F4Pilot.evenLieOrder]

end OrderCerts

section MainCerts


theorem three_dvd_card_center_of_model_uni {S : Type} [Group S] [Finite S]
    {labL : GLALabel} {β : MulAut S} {n : ℕ} {J : Subgroup S}
    (h : U3CoreHyp S labL β n J) (hF : FamUni labL) {d : ℕ} {K : Type} [Field K]
    (hU : UnitaryFieldData 2 labL.n K) (hd3 : 3 ≤ d) (hd6 : d ≤ 6)
    (hne : ¬(d = 3 ∧ 2 ^ labL.n = 2))
    (θ : S ≃* primeFormP hU (idGram K d)) :
    3 ∣ Nat.card ↥(Subgroup.center ↥J) := by
  classical
  have hnd : labL.tag ≠ .B2der ∧ labL.tag ≠ .G2der ∧ labL.tag ≠ .twF4der := by
    rcases hF with htag | ⟨htag, -⟩ <;> rw [htag] <;> decide
  have hβmem : β ∈ innAutDerived S :=
    mem_innAutDerived_of_innDiagKind_of_not_derived h.center_eq_bot hnd h.innDiagKind
  let β' : MulAut (primeFormP hU (idGram K d)) := θ.symm.trans (β.trans θ)
  have hβ'mem : β' ∈ innAutDerived (primeFormP hU (idGram K d)) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr θ).2 hβmem
  have hβ'3 : β' ^ 3 = 1 := by
    have h3 := map_pow (MulAut.congr θ) β 3
    rw [h.pow_three, map_one] at h3
    exact h3.symm
  have hβ'ne : β' ≠ 1 := by
    intro h1
    apply h.ne_one
    have h2 : (MulAut.congr θ) β = 1 := h1
    exact (MulEquiv.map_eq_one_iff (MulAut.congr θ)).1 h2
  obtain ⟨A, c, -, hA, hβeq⟩ :=
    exists_primeFormConjHom_pow_scalar_of_mem_innAutDerived hU
      (isPrimeFormGram_idGram (n := d)) hd3 hne hβ'mem hβ'3
  have hβne : primeFormConjHom hU (idGram K d) A ≠ 1 := by
    rw [← hβeq]
    exact hβ'ne
  let T : Subgroup (primeFormP hU (idGram K d)) := J.map θ.toMonoidHom
  have eJK : ↥J ≃* ↥T := J.equivMapOfInjective θ.toMonoidHom θ.injective
  have hTcomp : CFSG.Open.IsComponentOf T
      (fixSubgroup (primeFormConjHom hU (idGram K d) A)) := by
    have h1 := isComponentOf_map θ h.isComponentOf
    have hfix := CFSG.LocalAnalysis.GLTheoremA.map_fixSubgroup θ β
    rw [← hβeq]
    exact hfix ▸ h1
  have hcardT : Nat.card (↥T ⧸ Subgroup.center ↥T) = ordTwistedA 2 (2 ^ n) := by
    rw [← h.card_centerQuot_uni]
    exact (Nat.card_congr (QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥T)
      eJK (Subgroup.map_center_eq eJK)).toEquiv).symm
  have h3T : 3 ∣ Nat.card ↥(Subgroup.center ↥T) :=
    three_dvd_card_center_of_component_primeForm hU hd6 h.odd A hA hβne hTcomp hcardT
  rw [Nat.card_congr (Subgroup.centerCongr eJK).toEquiv]
  exact h3T

theorem u3CoreOn_uni : U3CoreOn FamUni := by
  intro S _ _ labL β n J hF h
  classical
  have h3dvd : 3 ∣ 2 ^ labL.n + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod,
      CFSG.two_pow_mod_three_of_odd h.odd_labL_n]
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel
    h.hasLabel_of_innDiag
  rcases hF with htag | ⟨htag, hrank⟩
  · have hd6 : labL.rank + 1 ≤ 6 := by
      have hlab2 := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.lambda2_of_hasLabel
        h.hasLabel_of_innDiag
      have hl := CFSG.StandardType.largeEvenLabelAll_torusLift_twA (p := 3)
        hlab2 htag (by norm_num) h3dvd
      have hT := ggTorusLift_of_labelAll h.center_eq_bot h.innDiagKind hl
      have hr := h.rank_le _ hT
      simp only [CFSG.StandardType.ggUnitaryTorusRank] at hr
      split_ifs at hr <;> omega
    have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .PSU
        (labL.rank + 1) 2 labL.n := by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg, htag] using hM
    have hSCM : StatedClassicalModel (S ⧸ Subgroup.center S) .PSU
        (labL.rank + 1) 2 labL.n := hLM.statedClassicalModel (by decide)
    have hSCM' : StatedClassicalModel S .PSU (labL.rank + 1) 2 labL.n :=
      CFSG.StandardType.statedClassicalModel_of_mulEquiv'
        (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot h.center_eq_bot) hSCM
    obtain ⟨K, hKf, hU, -, ⟨eP⟩⟩ := exists_primeFormP_mulEquiv_of_statedModel_uni hSCM'
    exact three_dvd_card_center_of_model_uni (d := labL.rank + 1) h (Or.inl htag) hU
      hSCM'.1.2.2.1 hd6
      (by rintro ⟨h1, h2⟩; exact hSCM'.1.2.2.2 (by rw [h1, h2])) eP
  · have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .PSU 4 2 labL.n := by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg, htag, hrank] using hM
    have hSCM : StatedClassicalModel (S ⧸ Subgroup.center S) .PSU 4 2 labL.n :=
      hLM.statedClassicalModel (by decide)
    have hSCM' : StatedClassicalModel S .PSU 4 2 labL.n :=
      CFSG.StandardType.statedClassicalModel_of_mulEquiv'
        (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot h.center_eq_bot) hSCM
    obtain ⟨K, hKf, hU, -, ⟨eP⟩⟩ := exists_primeFormP_mulEquiv_of_statedModel_uni hSCM'
    exact three_dvd_card_center_of_model_uni (d := 4) h (Or.inr ⟨htag, hrank⟩) hU (by norm_num)
      (by norm_num) (by rintro ⟨h1, -⟩; omega) eP

end MainCerts

end CFSG.LocalAnalysis.GLTheoremA.CanonU3

