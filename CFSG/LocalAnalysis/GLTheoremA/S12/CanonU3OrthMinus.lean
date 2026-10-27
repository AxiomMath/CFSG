module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3Order
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdx
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3OrthMinusBlock
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailFinal
import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.Fitting
import CFSG.Walter.Bender1970.S2.Basic
import CFSG.ClassicalGroups.Orthogonal.Simple
import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.RankThree.PartOne.S11d.LieCentralizerPOmega
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofCases

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3

open CFSG.Open CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)

open CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp (lambda2_of_hasLabel)

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

open CFSG.RankThree.Classical2 CFSG.GroupTheory.WeirSylow

theorem innDiagKind_twD_data_orthMinus {S : Type} [Group S] [Finite S] {labK : GLALabel}
    {α : MulAut S} (hcen : Subgroup.center S = ⊥) (hD : labK.tag = .twD)
    (hr2 : labK.rank ≠ 2) (hr3 : labK.rank ≠ 3) (hin : InnDiagKind S labK α) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K),
      Nat.card K = 2 ^ labK.n ∧ (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (S ≃* LargeEvenProj
          (LargeEvenOmega (LargeEvenQMinus (labK.rank - 1) b c))) ∧
          ∃ a : S, MulAut.conj a = α := by
  have hFam : FamOrth labK := Or.inr ⟨hD, hr2, hr3⟩
  unfold InnDiagKind CFSG.Assembly.LargeEvenMarking at hin
  obtain ⟨-, lab', hlam, hraw⟩ := hin
  obtain ⟨_, _, _, _, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ
  subst lab'
  have hΛ : 1 ≤ labK.n ∧ 2 ≤ labK.rank := by
    have h := hlam
    simp only [LargeEvenInLambda2, hD] at h
    exact h
  have hm4 : 4 ≤ labK.rank := by omega
  have hc : (canonLabel labK).n = labK.n := by simp [canonLabel, hD, hr2, hr3]
  unfold CFSG.Assembly.LargeEvenRawDatum at hraw
  simp only [hD, hr2, hr3, ↓reduceIte] at hraw
  unfold LargeEvenRecipeOmegaMinus at hraw
  obtain ⟨K, hKf, hKfin, hcard, b, c, hbc, hQ'⟩ := hraw
  obtain ⟨-, -, θ, -, u, hu, hind⟩ := hQ'
  simp only [LargeEvenInnSet] at hu
  obtain ⟨r, rfl⟩ := hu
  let e : S ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (labK.rank - 1) b c)) :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm.trans θ
  refine ⟨K, hKf, hKfin, b, c, hcard, hbc, ⟨e⟩, e.symm r, ?_⟩
  refine MulEquiv.ext fun s => ?_
  apply e.injective
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact hind s (α s) rfl

section Certs


theorem U3CoreHyp.exists_orthMinus_model {S : Type} [Group S] [Finite S] {labL : GLALabel}
    {β : MulAut S} {n : ℕ} {J : Subgroup S} (h : U3CoreHyp S labL β n J)
    (hD : labL.tag = .twD) (hr2 : labL.rank ≠ 2) (hr3 : labL.rank ≠ 3) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K)
      (e : S ≃* ProjOrthDerived (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)),
      Nat.card K = 2 ^ labL.n ∧ Odd labL.n ∧
      (∃ s : S, MulAut.conj s = β ∧ orderOf s = 3) ∧
      (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)).Nondegenerate ∧
      (∃ U : Submodule K (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K), Module.finrank K U = 3 ∧
        ∀ u ∈ U, CFSG.LieType.Universal.Spin.quadMinus 4 K b c u = 0) ∧
      ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (CFSG.LieType.Universal.Spin.quadMinus 4 K b c) ∧
      Module.finrank K (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) = 8 ∧
      Nat.card (↥J ⧸ Subgroup.center ↥J) = CFSG.Open.ordTwistedA 2 (2 ^ n) := by
  obtain ⟨t, l, m⟩ := labL
  dsimp only at hD hr2 hr3 ⊢
  subst hD
  have hlam := lambda2_of_hasLabel h.hasLabel_of_innDiag
  have hl2 : 2 ≤ l := by
    have h2 := hlam.2
    dsimp only [LargeEvenInLambda2] at h2
    exact h2
  have hl4 : 4 ≤ l := by omega
  have hm_odd : Odd m := h.odd_labL_n
  have h3m : 3 ∣ 2 ^ m + 1 :=
    CFSG.RankThree.PartTwo.Sec8.Item82OneProof.three_dvd_two_pow_add_one_of_odd hm_odd
  have hlab : GGOrthRestLabel 3 ⟨.twD, l, m⟩ := ⟨hl4, Or.inl ⟨rfl, h3m⟩⟩
  have hl : LargeEvenLabelAll ⟨.twD, l, m⟩ fun R _ _ _ => GGTorusLift 3 (l - 1) R :=
    LargeEvenLabelAll.mono (fun _ _ I _ hP => hP.2)
      (OrthRest.labelAll CFSG.StandardType.ggOrthRestTorusLiftInput_holds (by norm_num) hlab)
  have hT := ggTorusLift_of_labelAll h.center_eq_bot h.innDiagKind hl
  have hrankle := h.rank_le _ hT
  have hl_eq : l = 4 := by omega
  obtain ⟨K, hKf, hKfin, b, c, hKcard, hbc, ⟨e⟩, ⟨s, hs⟩⟩ :=
    innDiagKind_twD_data_orthMinus h.center_eq_bot rfl hr2 hr3 h.innDiagKind
  have hs3 : s ^ 3 = 1 := by
    apply CFSG.HardMathSupport.Lang.Triality.conj_injective_of_center_eq_bot h.center_eq_bot
    rw [map_pow, hs, h.pow_three, map_one]
  have hs1 : s ≠ 1 := by
    intro h1
    apply h.ne_one
    rw [← hs, h1, map_one]
  have hsord : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have e3 : S ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQMinus 3 b c)) := by
    have h3 : (4 - 1 : ℕ) = 3 := by norm_num
    rw [hl_eq, h3] at e
    exact e
  let Q : QuadraticForm K (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) :=
    CFSG.LieType.Universal.Spin.quadMinus 4 K b c
  let e' : S ≃* ProjOrthDerived Q :=
    e3.trans ((CFSG.StandardType.omegaMinusProjEquiv 4 b c).trans
      (CFSG.RankThree.PartOne.statedProjOrthEquiv
        (CFSG.LieType.Universal.Spin.coe_quadMinus (K := K) (n := 4) (b := b) (c := c))))
  have hcardJ : Nat.card (J ⧸ Subgroup.center J) = ordTwistedA 2 (2 ^ n) := by
    have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel h.hasLabel
    unfold CFSG.StandardType.MarkedModel at hM
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg] at hM
    rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM]
    norm_num [CFSG.SeitzReduction.F4Pilot.evenLieOrder]
  have hQgen : (QuadraticMap.polarBilin Q).Nondegenerate := by
    simpa [Q] using (CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (n := 4) (K := K)
      (b := b) (c := c) (by norm_num) hbc).1
  have hTgen : ∃ U : Submodule K (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K), Module.finrank K U = 3 ∧
      ∀ u ∈ U, Q u = 0 := by
    simpa [Q] using (CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (n := 4) (K := K)
      (b := b) (c := c) (by norm_num) hbc).2
  have hVgen : ¬ IsPlusType Q := by
    simpa [Q] using CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (n := 4) (K := K)
      (b := b) (c := c) (by norm_num) hbc
  have hdimgen : Module.finrank K (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [Fintype.card_sum]
  exact ⟨K, hKf, hKfin, b, c, e', hKcard, hm_odd, ⟨s, hs, hsord⟩, hQgen, hTgen, hVgen,
    hdimgen, hcardJ⟩

theorem u3CoreOn_orthMinus :
    U3CoreOn fun lab => lab.tag = .twD ∧ lab.rank ≠ 2 ∧ lab.rank ≠ 3 := by
  intro S _ _ labL β n J hF h
  obtain ⟨hD, hr2, hr3⟩ := hF
  obtain ⟨K, hKf, hKfin, b, c, e, hKcard, hodd, ⟨s, hs, hsord⟩, hQ, hT, hV, hdim, hcardJ⟩ :=
    U3CoreHyp.exists_orthMinus_model h hD hr2 hr3
  let Q : QuadraticForm K (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) :=
    CFSG.LieType.Universal.Spin.quadMinus 4 K b c
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β =
      Subgroup.centralizer ({s} : Set S) := by
    rw [← hs]
    exact CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj s
  have hJcomp : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({s} : Set S)) := by
    have h1 := h.isComponentOf
    rwa [hfix] at h1
  let J' : Subgroup (ProjOrthDerived Q) := J.map (e : S →* ProjOrthDerived Q)
  have hJ' : CFSG.Open.IsComponentOf J'
      (Subgroup.centralizer ({(e s)} : Set (ProjOrthDerived Q))) := by
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hJcomp
    have h2 : (Subgroup.centralizer ({s} : Set S)).map (e : S →* ProjOrthDerived Q) =
        Subgroup.centralizer ({(e s)} : Set (ProjOrthDerived Q)) :=
      CFSG.Walter.map_centralizer_singleton_mulEquiv e s
    exact h2 ▸ h1
  let eJ : ↥J ≃* ↥J' :=
    Subgroup.equivMapOfInjective J (e : S →* ProjOrthDerived Q) e.injective
  have hquot : Nat.card (J' ⧸ Subgroup.center J') = Nat.card (J ⧸ Subgroup.center J) := by
    exact (Nat.card_congr (QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥J') eJ
      (Subgroup.map_center_eq eJ)).toEquiv).symm
  have hcard' : Nat.card (J' ⧸ Subgroup.center J') = ordTwistedA 2 (2 ^ n) := by
    rw [hquot, hcardJ]
  have hx' : orderOf (e s) = 3 := by
    rw [MulEquiv.orderOf_eq, hsord]
  have h3J' : 3 ∣ Nat.card ↥(Subgroup.center ↥J') :=
    CFSG.LocalAnalysis.GLTheoremA.CanonU3.OrthMinus.three_dvd_card_center_of_component
      hQ hT hV hdim hKcard hodd h.odd h.three_le h.dvd hx' hJ' hcard'
  have hcenter : Nat.card ↥(Subgroup.center ↥J') = Nat.card ↥(Subgroup.center ↥J) :=
    (Nat.card_congr (Subgroup.centerCongr eJ).toEquiv).symm
  rwa [hcenter] at h3J'

end Certs

end CFSG.LocalAnalysis.GLTheoremA.CanonU3
