module
public import CFSG.Open.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3Core
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate8064

import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusArith
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriLHolds
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdx
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic
import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeTorus
import CFSG.Quasithin.EmptyFaithful.Insp7NumB
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubUArith
import CFSG.Quasithin.Background.B1
import CFSG.Quasithin.Background.B3Q
import CFSG.Quasithin.Background.B3ThreeModel
import CFSG.Quasithin.Background.B3ThreeStruct
import CFSG.Quasithin.Background.G2Omega4PlusModule
import CFSG.Quasithin.EmptyFaithful.Insp7NumA
import CFSG.Quasithin.EmptyFaithful.S143FF
import CFSG.Quasithin.EmptyFaithful.S143Final
import CFSG.Quasithin.EmptyFaithful.S143HD
import CFSG.Quasithin.EmptyFaithful.S143IG
import CFSG.Quasithin.EmptyFaithful.S143JB
import CFSG.Quasithin.EmptyFaithful.S143KO
import CFSG.Quasithin.EmptyFaithful.S143KP
import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcomp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3

open CFSG.Open CFSG.Assembly
open CFSG.StandardType (GGTorusLift LargeEvenLabelAll)
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField

theorem U3CoreHyp.odd_labL_n {S : Type} [Group S] {labL : GLALabel} {β : MulAut S} {n : ℕ}
    {J : Subgroup S} (h : U3CoreHyp S labL β n J) : Odd labL.n :=
  h.odd.of_dvd_nat h.dvd

theorem U3CoreHyp.labL_n_eq_one_of_untwisted {S : Type} [Group S] {labL : GLALabel}
    {β : MulAut S} {n : ℕ} {J : Subgroup S} (h : U3CoreHyp S labL β n J)
    (hu : LargeEvenUntwisted labL.tag) : labL.n = 1 := by
  have ho := h.odd_labL_n
  rcases h.split with ⟨-, h3⟩ | ⟨hnot, -, -⟩ | ⟨h3, -⟩ | ⟨h1, -⟩
  · exact absurd h3 (CFSG.LocalAnalysis.GLTheoremA.three_not_dvd_two_pow_sub_one_of_odd ho)
  · exact absurd hu hnot
  · rcases h3 with h3 | h3 <;> rw [h3] at hu <;> simp [LargeEvenUntwisted] at hu
  · exact h1

theorem U3CoreHyp.labL_n_eq_one_of_triD4 {S : Type} [Group S] {labL : GLALabel}
    {β : MulAut S} {n : ℕ} {J : Subgroup S} (h : U3CoreHyp S labL β n J)
    (ht : labL.tag = .triD4) : labL.n = 1 := by
  have ho := h.odd_labL_n
  rcases h.split with ⟨hu, -⟩ | ⟨-, hne, -⟩ | ⟨h3, hdvd⟩ | ⟨h1, -⟩
  · rw [ht] at hu
    simp [LargeEvenUntwisted] at hu
  · exact absurd ht hne
  · exact absurd hdvd (CFSG.LocalAnalysis.GLTheoremA.three_not_dvd_two_pow_sub_one_of_odd ho)
  · exact h1

theorem U3CoreHyp.hasLabel_of_innDiag {S : Type} [Group S] {labL : GLALabel}
    {β : MulAut S} {n : ℕ} {J : Subgroup S} (h : U3CoreHyp S labL β n J) :
    HasLabel S (· = labL) :=
  CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.1) h.innDiagKind

section Order

theorem U3CoreHyp.card_dvd {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {n : ℕ} {J : Subgroup S} (h : U3CoreHyp S labL β n J) :
    ordTwistedA 2 (2 ^ n) ∣ Nat.card S := by
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel h.hasLabel
  unfold CFSG.StandardType.MarkedModel at hM
  simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
    CFSG.StandardType.markChar, CFSG.StandardType.markDeg] at hM
  have hcard : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordTwistedA 2 (2 ^ n) := by
    rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM]
    norm_num [CFSG.SeitzReduction.F4Pilot.evenLieOrder]
  rw [← hcard]
  exact (Subgroup.index_dvd_card _).trans (Subgroup.card_subgroup_dvd_card J)

theorem U3CoreHyp.card_eq {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {n : ℕ} {J : Subgroup S} (h : U3CoreHyp S labL β n J)
    (hc : CFSG.StandardType.markChar labL = 2) :
    Nat.card S = CFSG.SeitzReduction.F4Pilot.evenLieOrder
      (CFSG.StandardType.markTag labL) (CFSG.StandardType.markRank labL)
      (CFSG.StandardType.markDeg labL) :=
  CFSG.LocalAnalysis.GLTheoremA.CanonTriL.card_of_label_char_two h.center_eq_bot
    h.hasLabel_of_innDiag hc

end Order

theorem two_pow_dvd_ordTwistedA (n : ℕ) : 2 ^ (3 * n) ∣ ordTwistedA 2 (2 ^ n) :=
  CFSG.Quasithin.Insp7.two_pow_dvd_ordTwistedA_two

theorem three_dvd_ordTwistedA {n : ℕ} (hn : Odd n) : 3 ∣ ordTwistedA 2 (2 ^ n) :=
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub.three_dvd_ordTwistedA
    (f := n) (m := 3) hn.pos (by norm_num)

theorem not_ordTwistedA_dvd {M n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) (h27 : ¬ 2 ^ 27 ∣ M)
    (h19 : ¬ 19 ∣ M) (h11 : ¬ 11 ∣ M) (h43 : ¬ 43 ∣ M) :
    ¬ ordTwistedA 2 (2 ^ n) ∣ M := by
  intro hdvd
  rcases Nat.lt_or_ge n 9 with hlt | hge
  · have hn3 : n = 3 ∨ n = 5 ∨ n = 7 := by
      obtain ⟨k, rfl⟩ := hn
      omega
    rcases hn3 with rfl | rfl | rfl
    · exact h19 ((by decide +kernel : 19 ∣ ordTwistedA 2 (2 ^ 3)).trans hdvd)
    · exact h11 ((by decide +kernel : 11 ∣ ordTwistedA 2 (2 ^ 5)).trans hdvd)
    · exact h43 ((by decide +kernel : 43 ∣ ordTwistedA 2 (2 ^ 7)).trans hdvd)
  · exact h27 ((Nat.pow_dvd_pow 2 (by omega : 27 ≤ 3 * n)).trans
      ((two_pow_dvd_ordTwistedA n).trans hdvd))

theorem ggTorusLift_of_labelAll {S : Type} [Group S] {labL : GLALabel} {β : MulAut S}
    (hcen : Subgroup.center S = ⊥) (hin : InnDiagKind S labL β) {p r : ℕ}
    (hl : LargeEvenLabelAll labL fun R _ _ _ => GGTorusLift p r R) : GGTorusLift p r S := by
  obtain ⟨-, lab, hlam, hraw⟩ := hin
  obtain ⟨R, hR, I, F, hsimple, hna, θ, hlab, u, hu, hinduces⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  subst lab
  have hcanon : LargeEvenRawDatum labL
      (fun R _ _ _ => Nonempty (S ⧸ Subgroup.center S ≃* R)) := by
    refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
    intro R _ I F hP
    obtain ⟨-, -, θ, -⟩ := hP
    exact ⟨θ⟩
  have hlegacy :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.largeEvenRawDatumLegacy_of_canonical_carrier hcanon
  obtain ⟨R', hR', I', F', hT, hLift⟩ :=
    CFSG.StandardType.largeEvenRawDatum_exists (hl _ hlegacy)
  obtain ⟨eR⟩ := hT
  let e : S ≃* R' :=
    (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans eR
  exact CFSG.StandardType.TableBF4.ggTorusLift_of_mulEquiv e hLift

theorem largeEvenLabelAll_typeA_two {lab : LargeEvenLabel} (htag : lab.tag = .A)
    (hn : lab.n = 1) (hl : 5 ≤ lab.rank) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 ((lab.rank + 1) / 2) R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hn hl ⊢
  subst htag
  subst hn
  intro Q hQ
  obtain ⟨K, hKf, hKfin, hKn, hQ'⟩ := hQ
  have hK2 : Nat.card K = 2 := by simpa using hKn
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) (by rw [hK2, pow_one])
  refine ⟨K, hKf, hKfin, hKn, hQ', ?_⟩
  exact CFSG.StandardType.TypeA.ggTorusLift_of_mulEquiv
    (CFSG.StandardType.TypeA.recipeEquiv (l + 1) K)
    (CFSG.StandardType.TwoThree.ggTorusLift_two hK2 (by omega))

theorem largeEvenLabelAll_sp_two {lab : LargeEvenLabel}
    (htag : lab.tag = .B ∨ lab.tag = .C) (hn : lab.n = 1) (hl : 3 ≤ lab.rank) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 (lab.rank - 1) R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hn hl ⊢
  subst hn
  rcases htag with rfl | rfl
  · intro Q hQ
    obtain ⟨K, hKf, hKfin, hKn, hQ'⟩ := hQ
    have hK2 : Nat.card K = 2 := by simpa using hKn
    haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (le_refl 1) (by rw [hK2, pow_one])
    refine ⟨K, hKf, hKfin, hKn, hQ', ?_⟩
    have h := CFSG.StandardType.TwoThree.ggTorusLift_sp_two (K := K) (k := l - 1) hK2
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ l)] at h
  · intro Q hQ
    obtain ⟨K, hKf, hKfin, hKn, hQ'⟩ := hQ
    have hK2 : Nat.card K = 2 := by simpa using hKn
    haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (le_refl 1) (by rw [hK2, pow_one])
    refine ⟨K, hKf, hKfin, hKn, hQ', ?_⟩
    have h := CFSG.StandardType.TwoThree.ggTorusLift_sp_two (K := K) (k := l - 1) hK2
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ l)] at h

end CFSG.LocalAnalysis.GLTheoremA.CanonU3
