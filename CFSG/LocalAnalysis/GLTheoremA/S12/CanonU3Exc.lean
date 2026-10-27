module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3Order
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2265
public import Certificates.Certificate2266
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate3951

import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynTri
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoThree
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6
import CFSG.LocalAnalysis.GLTheoremA.S11.Lemma117
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeCore
import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
import CFSG.HardMathSupport.Lang.Triality.SylowInnerExt
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutReeF4
import CFSG.LieType.ChevTwo.OppositeFixedExcReeModel
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdx
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
import CFSG.LocalAnalysis.EvenBN.GMSK.TypeDetBender
import CFSG.Mathlib.Arithmetic.TwoPowModThree
import CFSG.RankThree.PartTwo.Sec8.Item86ResProofTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3

open CFSG.Open CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)

open CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp (lambda2_of_hasLabel)

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)


section CertE6


theorem false_of_E6 {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S} {n : ℕ}
    {J : Subgroup S} (h : U3CoreHyp S labL β n J) (hE : labL.tag = .E6) : False := by
  have hm1 := h.labL_n_eq_one_of_untwisted (by rw [hE]; exact trivial)
  have hl := largeEvenLabelAll_torusLift_E6_two (lab := labL) ⟨hE, hm1⟩
  have hT := ggTorusLift_of_labelAll h.center_eq_bot h.innDiagKind hl
  have := h.rank_le 4 hT
  omega

end CertE6

section CertExcPlus


theorem false_of_E7_or_E8 {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {n : ℕ} {J : Subgroup S} (h : U3CoreHyp S labL β n J)
    (hE : labL.tag = .E7 ∨ labL.tag = .E8) : False := by
  have hE0 := hE
  have hm1 := h.labL_n_eq_one_of_untwisted (by
    rcases hE with hE | hE <;> rw [hE] <;> exact trivial)
  have hpn : 3 ∣ 2 ^ labL.n + 1 := by rw [hm1]; norm_num
  have hl := largeEvenLabelAll_torusLift_excPlus (p := 3) (by norm_num) (by norm_num)
    (lab := labL) ⟨by
      rcases hE0 with hE | hE
      · exact Or.inl hE
      · exact Or.inr (Or.inl hE), hpn⟩
  have hT := ggTorusLift_of_labelAll h.center_eq_bot h.innDiagKind hl
  have hrank := h.rank_le _ hT
  rcases hE0 with hE | hE <;> rw [hE] at hrank <;>
    norm_num [CFSG.StandardType.ggNbrExcPlusRank] at hrank

end CertExcPlus

section CertCard


theorem false_of_F4 {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S} {n : ℕ}
    {J : Subgroup S} (h : U3CoreHyp S labL β n J) (hF : labL.tag = .F4) : False := by
  have hm1 := h.labL_n_eq_one_of_untwisted (by rw [hF]; exact trivial)
  have hc : CFSG.StandardType.markChar labL = 2 := by
    simp [CFSG.StandardType.markChar, hF]
  have hcard : Nat.card S = ordF4 2 := by
    rw [h.card_eq hc]
    simp [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markDeg, hF, hm1, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
  have hdvd := h.card_dvd
  rw [hcard] at hdvd
  exact not_ordTwistedA_dvd h.odd h.three_le (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hdvd

theorem false_of_triD4 {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {n : ℕ} {J : Subgroup S} (h : U3CoreHyp S labL β n J) (ht : labL.tag = .triD4) :
    False := by
  have hm1 := h.labL_n_eq_one_of_triD4 ht
  have hc : CFSG.StandardType.markChar labL = 2 := by
    simp [CFSG.StandardType.markChar, ht]
  have hcard : Nat.card S = ordTrialityD4 2 := by
    rw [h.card_eq hc]
    simp [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markDeg, ht, hm1, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
  have hdvd := h.card_dvd
  rw [hcard] at hdvd
  exact not_ordTwistedA_dvd h.odd h.three_le (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hdvd

end CertCard

section NoCerts

theorem false_of_G2 {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S} {n : ℕ}
    {J : Subgroup S} (h : U3CoreHyp S labL β n J) (hG : labL.tag = .G2) : False := by
  have hlam := lambda2_of_hasLabel h.hasLabel_of_innDiag
  simp only [LargeEvenInLambda2, hG] at hlam
  have hn2 := hlam.2.2
  have hm1 := h.labL_n_eq_one_of_untwisted (by rw [hG]; exact trivial)
  omega

end NoCerts

section CertCardSmall


theorem false_of_G2der {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {n : ℕ} {J : Subgroup S} (h : U3CoreHyp S labL β n J) (hG : labL.tag = .G2der) :
    False := by
  obtain ⟨t, r, m⟩ := labL
  dsimp only at hG
  subst hG
  have hlam := lambda2_of_hasLabel h.hasLabel_of_innDiag
  simp only [LargeEvenInLambda2] at hlam
  obtain ⟨-, rfl, rfl⟩ := hlam
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel
    h.hasLabel_of_innDiag
  have h6048 : Nat.card S = 6048 := by
    have hc := CFSG.LocalAnalysis.GLTheoremA.card_of_G2der hM
    rwa [Nat.card_congr
      (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot h.center_eq_bot).toEquiv] at hc
  have hdvd := h.card_dvd
  rw [h6048] at hdvd
  exact not_ordTwistedA_dvd h.odd h.three_le (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hdvd

theorem false_of_twB2 {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {n : ℕ} {J : Subgroup S} (h : U3CoreHyp S labL β n J) (hB : labL.tag = .twB2) :
    False := by
  have hlam := lambda2_of_hasLabel h.hasLabel_of_innDiag
  simp only [LargeEvenInLambda2, hB] at hlam
  have hodd : Odd labL.n := hlam.2.2.1
  have hc : CFSG.StandardType.markChar labL = 2 := by
    simp [CFSG.StandardType.markChar, hB]
  have hcard : Nat.card S = ordSuzuki (2 ^ labL.n) := by
    rw [h.card_eq hc]
    simp [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markDeg, hB, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
  have h3 : 3 ∣ Nat.card S := (three_dvd_ordTwistedA h.odd).trans h.card_dvd
  rw [hcard] at h3
  exact CFSG.LocalAnalysis.EvenBN.GMSK.TypeDet.not_three_dvd_ordSuzuki
    (CFSG.two_pow_mod_three_of_odd hodd) h3

theorem false_of_twF4der {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {n : ℕ} {J : Subgroup S} (h : U3CoreHyp S labL β n J) (hF : labL.tag = .twF4der) :
    False := by
  have hlam := lambda2_of_hasLabel h.hasLabel_of_innDiag
  simp only [LargeEvenInLambda2, hF] at hlam
  have hn1 : labL.n = 1 := hlam.2.2
  have hc : CFSG.StandardType.markChar labL = 2 := by
    simp [CFSG.StandardType.markChar, hF]
  have hcard : Nat.card S = ordTits := by
    rw [h.card_eq hc]
    simp [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markDeg, hF, hn1, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
  have hdvd := h.card_dvd
  rw [hcard] at hdvd
  exact not_ordTwistedA_dvd h.odd h.three_le (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hdvd

end CertCardSmall

section CertTwE6


theorem false_of_twE6 {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {n : ℕ} {J : Subgroup S} (h : U3CoreHyp S labL β n J) (hE : labL.tag = .twE6) :
    False := by
  have h3 : 3 ∣ 2 ^ labL.n + 1 := by
    rcases h.split with ⟨hu, -⟩ | ⟨-, hne, h3⟩ | ⟨h3, -⟩ | ⟨hn1, -⟩
    · rw [hE] at hu
      simp [LargeEvenUntwisted] at hu
    · exact h3
    · rcases h3 with h3 | h3 <;> rw [h3] at hE <;> simp at hE
    · rw [hn1]; norm_num
  have hlam := lambda2_of_hasLabel h.hasLabel_of_innDiag
  have hlab : GGTableBTwE6ThreeLabel 3 labL := ⟨hE, rfl, h3⟩
  have hl : LargeEvenLabelAll labL fun R _ _ _ => GGTorusLift 3 4 R :=
    LargeEvenLabelAll.mono (fun _ _ _ _ hP => hP.1)
      (largeEvenLabelAll_twE6Three_of (p := 3) hlam hlab
        (P := fun _ _ _ => True) (by intro K _ _ m _ _ _; exact trivial))
  have hT := ggTorusLift_of_labelAll h.center_eq_bot h.innDiagKind hl
  have := h.rank_le 4 hT
  omega

end CertTwE6

section CertTwF4


theorem U3CoreHyp.twF4_setup {S : Type} [Group S] [Finite S] {labL : GLALabel}
    {β : MulAut S} {n : ℕ} {J : Subgroup S} (h : U3CoreHyp S labL β n J)
    (ht : labL.tag = .twF4) :
    innAutDerived S ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S ∧
      ∃ (a : ℕ) (s : S), MulAut.conj s = β ∧ s ^ 3 = 1 ∧ s ≠ 1 ∧ 1 ≤ a ∧
        J = Subgroup.centralizer ({s} : Set S) ∧
        Nonempty (↥(Subgroup.centralizer ({s} : Set S)) ≃*
          CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 (2 * a + 1)
            (GaloisField 2 (2 * (2 * a + 1))) 3) := by
  classical
  have hnd : labL.tag ≠ .B2der ∧ labL.tag ≠ .G2der ∧ labL.tag ≠ .twF4der := by
    rw [ht]
    exact ⟨by decide, by decide, by decide⟩
  obtain ⟨t, r, m⟩ := labL
  dsimp only at ht
  subst ht
  have hlam := lambda2_of_hasLabel h.hasLabel_of_innDiag
  simp only [LargeEvenInLambda2] at hlam
  obtain ⟨-, -, hnodd, hn3⟩ := hlam
  obtain ⟨a, rfl⟩ := hnodd
  have ha1 : 1 ≤ a := by omega
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel
    h.hasLabel_of_innDiag
  have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .twistedF4 0 2 (2 * a + 1) := hM
  have hR : CFSG.Blueprint.ReeTitsModel (S ⧸ Subgroup.center S) .twistedF4 2 (2 * a + 1) :=
    (hLM.reeTitsModel (by decide)).2
  obtain ⟨K, _, _, _, hK, ⟨e₁⟩⟩ :=
    CFSG.LieType.ChevTwo.Semi.exists_mulEquiv_reeGamma ha1 hR
  have hβmem : β ∈ innAutDerived S :=
    CFSG.LocalAnalysis.GLTheoremA.I141F.Tri.mem_innAutDerived_of_innDiagKind_of_not_derived
      h.center_eq_bot hnd h.innDiagKind
  have hinnΓ : innAutDerived ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) ≤
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.innAutDerived_le_inner_excTw_of_mulEquiv e₁
      (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6outreef4_innAutDerived_le_inner hR)
  let eS : S ≃* CFSG.LieType.Ree.ReeTag.F4.reeGamma K a :=
    (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot h.center_eq_bot).symm.trans e₁
  have hinnS : innAutDerived S ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.innAutDerived_le_inner_excTw_of_mulEquiv eS.symm hinnΓ
  obtain ⟨s, hs⟩ := hinnS hβmem
  have hs3 : s ^ 3 = 1 := by
    apply CFSG.HardMathSupport.Lang.Triality.conj_injective_of_center_eq_bot h.center_eq_bot
    rw [map_pow, hs, h.pow_three, map_one]
  have hs1 : s ≠ 1 := by
    intro h1
    apply h.ne_one
    rw [← hs, h1, map_one]
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hsord : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  let y : CFSG.LieType.Ree.ReeTag.F4.reeGamma K a := eS s
  have hy3 : orderOf y = 3 := by
    change orderOf (eS s) = 3
    rw [MulEquiv.orderOf_eq]
    exact hsord
  obtain ⟨eC⟩ := CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU
    a K hK y hy3
  have hmap : (Subgroup.centralizer ({s} : Set S)).map eS.toMonoidHom =
      Subgroup.centralizer ({y} : Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a)) := by
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [← map_mul, ← map_mul, hg]
    · intro hz
      refine ⟨eS.symm z, ?_, by simp⟩
      apply eS.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hz
  let eCS : ↥(Subgroup.centralizer ({s} : Set S)) ≃*
      ↥(Subgroup.centralizer ({y} : Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a))) :=
    (eS.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
  let eSU : ↥(Subgroup.centralizer ({s} : Set S)) ≃*
      CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 (2 * a + 1)
        (GaloisField 2 (2 * (2 * a + 1))) 3 :=
    eCS.trans eC
  have hF'card : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]
  have hqU := (CFSG.RankThree.PartTwo.Sec8.Item87Proof.isQuasisimple_statedSU_three
    (F := GaloisField 2 (2 * (2 * a + 1))) (f := 2 * a + 1) hF'card (by omega)).1
  have hqU' : CFSG.Open.IsQuasisimple
      ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 (2 * a + 1)
        (GaloisField 2 (2 * (2 * a + 1))) 3) :=
    ⟨Group.isPerfect_def.mp hqU.1, hqU.2.1⟩
  have hqCS : CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({s} : Set S)) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv eSU hqU'
  have hfix : fixSubgroup β = Subgroup.centralizer ({s} : Set S) := by
    rw [← hs]
    exact CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj s
  have hJeq : J = Subgroup.centralizer ({s} : Set S) := by
    refine CFSG.LocalAnalysis.GLTheoremA.S11.y10xF_eq_of_subnormal hqCS ?_ ?_ h.isComponentOf.2.2
    · have hle := h.isComponentOf.1
      rwa [hfix] at hle
    · have hsub := h.isComponentOf.2.1
      rwa [hfix] at hsub
  exact ⟨hinnS, a, s, hs, hs3, hs1, ha1, hJeq, ⟨eSU⟩⟩

theorem three_dvd_card_center_of_twF4 {S : Type} [Group S] [Finite S] {labL : GLALabel}
    {β : MulAut S}
    {n : ℕ} {J : Subgroup S} (h : U3CoreHyp S labL β n J) (ht : labL.tag = .twF4) :
    3 ∣ Nat.card ↥(Subgroup.center ↥J) := by
  obtain ⟨-, a, s, -, -, -, ha1, hJ, ⟨eSU⟩⟩ := h.twF4_setup ht
  have hF'card : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]
  have hcardZ : Nat.card ↥(Subgroup.center ↥J) = 3 := by
    rw [hJ]
    calc Nat.card ↥(Subgroup.center ↥(Subgroup.centralizer ({s} : Set S)))
        = Nat.card ↥(Subgroup.center ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU
            2 (2 * a + 1) (GaloisField 2 (2 * (2 * a + 1))) 3)) :=
          Nat.card_congr (Subgroup.centerCongr eSU).toEquiv
      _ = 3 := CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.card_center_statedSU_three
          (f := 2 * a + 1) ⟨a, rfl⟩ (by omega) hF'card
  rw [hcardZ]

end CertTwF4

section CertAll


theorem u3CoreOn_exc : U3CoreOn FamExc := by
  intro S _ _ labL β n J hF h
  rcases hF with hE6 | hE7 | hE8 | hF4 | hTwE6 | hTriD4 | hG2 | hG2der | hTwB2 | hTwF4 |
    hTwF4der
  · exact (false_of_E6 h hE6).elim
  · exact (false_of_E7_or_E8 h (Or.inl hE7)).elim
  · exact (false_of_E7_or_E8 h (Or.inr hE8)).elim
  · exact (false_of_F4 h hF4).elim
  · exact (false_of_twE6 h hTwE6).elim
  · exact (false_of_triD4 h hTriD4).elim
  · exact (false_of_G2 h hG2).elim
  · exact (false_of_G2der h hG2der).elim
  · exact (false_of_twB2 h hTwB2).elim
  · exact three_dvd_card_center_of_twF4 h hTwF4
  · exact (false_of_twF4der h hTwF4der).elim

end CertAll


end CFSG.LocalAnalysis.GLTheoremA.CanonU3
