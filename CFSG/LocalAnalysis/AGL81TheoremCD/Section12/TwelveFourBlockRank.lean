module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourSteps
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.DResidualSimple
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6
import CFSG.Quasithin.Vol2.Ch11SKFIto
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeData

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L : Subgroup G}

private theorem dvd_card_barM_of_dvd {X : Subgroup G} (hXM : X ≤ M) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (h : r ∣ Nat.card X) : r ∣ Nat.card (barM M X) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) r h
  have hZX : Subgroup.zpowers (x : G) ≤ X := Subgroup.zpowers_le.mpr x.2
  have hcard := card_barM_of_isPGroup hr hr2 (hZX.trans hXM)
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one]))
  rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx] at hcard
  exact hcard ▸ Subgroup.card_dvd_of_le (barM_mono hZX)

private theorem exists_orderOf_not_mem {X : Type} [Group X] [Finite X] {Yb Lb : Subgroup X}
    (hperf : ⁅Yb, Yb⁆ = Yb) (hc : ∀ a ∈ Yb, ∀ x ∈ Lb, a * x = x * a) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrY : r ∣ Nat.card Yb) : ∃ x ∈ Yb, orderOf x = r ∧ x ∉ Lb := by
  have : Fact r.Prime := ⟨hr⟩
  have : Group.IsPerfect ↥Yb := Subgroup.isPerfect_iff.mpr hperf
  obtain ⟨x, hxr, hxZ⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecS.KF.exists_pow_eq_one_not_mem_center hr2 hrY
  refine ⟨x, x.2, (Subgroup.orderOf_coe x).trans
      (orderOf_eq_prime hxr fun h1 => hxZ (h1 ▸ Subgroup.one_mem _)), fun hxL => ?_⟩
  exact hxZ (Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2 x hxL))

private theorem pRank_three_barM_le_two (hm3 : CFSG.Open.pRank 3 M ≤ 3)
    {t : ↥M ⧸ CFSG.pCore 2 ↥M} (ht : orderOf t = 3) (htL : t ∉ barM M L)
    (htc : ∀ x ∈ barM M L, x * t = t * x) : CFSG.Open.pRank 3 (barM M L) ≤ 2 := by
  obtain ⟨E, hEL, hE, hEc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (barM M L)
  obtain ⟨hE', hc⟩ := CFSG.StandardType.isElemAbelian_sup_zpowers_of_card Nat.prime_three hE
    hEc (ht ▸ pow_orderOf_eq_one t) (fun h => htL (hEL h)) (fun e he => htc e (hEL he))
  have hle : E ⊔ Subgroup.zpowers t ≤ barM M M := by
    rw [barM, Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact le_top
  have h1 := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hle hE' hc
  rw [pRank_barM_eq Nat.prime_three (by norm_num) M M le_rfl] at h1
  omega

private theorem not_dvd_card_inf (hLM : L ≤ M) (hd : d.Prime) (hd2 : d ≠ 2)
    (hrank : CFSG.Open.pRank d (H ⊓ M) ≤ 1) {s : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hsHM : s ∈ barM M (H ⊓ M)) (hs : orderOf s = d) (hsL : s ∉ barM M L)
    (hsc : ∀ x ∈ barM M L, x * s = s * x) : ¬ d ∣ Nat.card (L ⊓ H : Subgroup G) := by
  intro hdvd
  have : Fact d.Prime := ⟨hd⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥(barM M (L ⊓ H))) d
    (dvd_card_barM_of_dvd (inf_le_left.trans hLM) hd hd2 hdvd)
  have huL : Subgroup.zpowers (u : ↥M ⧸ CFSG.pCore 2 ↥M) ≤ barM M L :=
    Subgroup.zpowers_le.mpr (barM_mono inf_le_left u.2)
  obtain ⟨hE', hc⟩ := CFSG.StandardType.isElemAbelian_sup_zpowers_of_card hd
    (CFSG.Open.isElemAbelian_zpowers
      (by rw [← Subgroup.orderOf_coe] at hu; exact hu ▸ pow_orderOf_eq_one _))
    (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hu, pow_one])
    (hs ▸ pow_orderOf_eq_one s) (fun h => hsL (huL h)) (fun e he => hsc e (huL he))
  have hle : Subgroup.zpowers (u : ↥M ⧸ CFSG.pCore 2 ↥M) ⊔ Subgroup.zpowers s ≤
      barM M (H ⊓ M) :=
    sup_le (Subgroup.zpowers_le.mpr (barM_mono (le_inf inf_le_right (inf_le_left.trans hLM)) u.2))
      (Subgroup.zpowers_le.mpr hsHM)
  have h2 := CFSG.SectionRank.le_pRank hd.one_lt hle hE' hc
  rw [pRank_barM_eq hd hd2 M (H ⊓ M) inf_le_right] at h2
  omega

theorem twelveFourBlockRank_of_twelveCtx (_h : TwelveCtx G M p Q H) (hd : d ∈ sigmaSet G M)
    (hD : TwelveThreeData M p H d) (hA : TwelveFourStepA M d) (hL : L ∈ weakBlockSet M H)
    (hYL : TwelveFourYCentL M H L d) : TwelveFourBlockRank M H L d := by
  have hdp : d.Prime := sigmaA_prime d hd.1
  have : Fact d.Prime := ⟨hdp⟩
  have hd2 : d ≠ 2 := by have := hA.2.2; omega
  have hLM : L ≤ M := hL.toIsTwoPrimeComponent.le
  have hYM : oPPrimeHull d (H ⊓ M) ≤ M := (oPPrimeHull_le d _).trans inf_le_right
  have := hD.common.y_simple
  have hperf : ⁅oPPrimeHull d (H ⊓ M), oPPrimeHull d (H ⊓ M)⁆ = oPPrimeHull d (H ⊓ M) :=
    commutator_eq_self_of_simple_modPrimeComplement_of_not_solvable hdp
      (S631.oPPrimeHull_oPPrimeHull d _) hD.common.y_nonsolvable
  have hperfbar : ⁅barM M (oPPrimeHull d (H ⊓ M)), barM M (oPPrimeHull d (H ⊓ M))⁆ =
      barM M (oPPrimeHull d (H ⊓ M)) := by
    have h1 : ⁅(oPPrimeHull d (H ⊓ M)).subgroupOf M, (oPPrimeHull d (H ⊓ M)).subgroupOf M⁆ =
        (oPPrimeHull d (H ⊓ M)).subgroupOf M := by
      apply Subgroup.map_subtype_inj.mp
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hYM, hperf]
    rw [barM, ← Subgroup.map_commutator, h1]
  have hc : ∀ a ∈ barM M (oPPrimeHull d (H ⊓ M)), ∀ x ∈ barM M L, a * x = x * a := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨l, hl, rfl⟩
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (y * l * y⁻¹ * l⁻¹) = 1 := by
      obtain ⟨z, hz, hzeq⟩ := hYL.1 y hy l hl
      rw [show y * l * y⁻¹ * l⁻¹ = z from Subtype.ext hzeq.symm]
      exact (QuotientGroup.eq_one_iff z).mpr hz
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
  have h3 : 3 ∣ Nat.card (oPPrimeHull d (H ⊓ M)) :=
    hD.common.three_dvd.trans (Subgroup.card_quotient_dvd_card _)
  have hdY : d ∣ Nat.card (oPPrimeHull d (H ⊓ M)) := by
    by_contra hn
    have hnt : Nontrivial ↥(oPPrimeHull d (H ⊓ M)) := (QuotientGroup.mk'_surjective
      (CFSG.RankThreeEvenClassification.Helpers.primeComplementCore
        (G := ↥(oPPrimeHull d (H ⊓ M))) d)).nontrivial
    have hbot := map_oPPrimeHull_eq_bot_of_not_dvd_card hdp (A := H ⊓ M) (MonoidHom.id G)
      (by rwa [Subgroup.map_id])
    rw [Subgroup.map_id] at hbot
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt hbot
  obtain ⟨t, htY, ht, htL⟩ := exists_orderOf_not_mem hperfbar hc Nat.prime_three (by norm_num)
    (dvd_card_barM_of_dvd hYM Nat.prime_three (by norm_num) h3)
  obtain ⟨s, hsY, hs, hsL⟩ := exists_orderOf_not_mem hperfbar hc hdp hd2
    (dvd_card_barM_of_dvd hYM hdp hd2 hdY)
  exact ⟨pRank_three_barM_le_two hA.2.1 ht htL fun x hx => (hc t htY x hx).symm,
    not_dvd_card_inf hLM hdp hd2 hD.common.rank_le_one (barM_mono (oPPrimeHull_le d _) hsY) hs
      hsL fun x hx => (hc s hsY x hx).symm⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
