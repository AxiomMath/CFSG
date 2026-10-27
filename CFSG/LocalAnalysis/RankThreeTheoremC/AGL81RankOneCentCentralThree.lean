module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentStepSix
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentCentralThreeCover
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceOdd
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinPrimeGlue
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryCover
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bCovers
import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.CentralThree

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique Matrix CFSG.LocalAnalysis.ComponentInitial

section Core

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}

abbrev CentralThreeConcl (X : Type) [Group X] [Finite X] : Prop :=
  Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) ∨
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) ∨ IsLinUnitThreeEven (X ⧸ Subgroup.center X)

theorem linear_case (hGA : GriessAllModelsStatement) (hL : IsComponentOf L ⊤)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) (h3 : 3 ∣ Nat.card (Subgroup.center ↥L))
    (hA : IsLieOf IdxA (↥L ⧸ Subgroup.center ↥L)) : CentralThreeConcl ↥L := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hA
  cases d with
  | A r q =>
    change q.p = 2 at hd
    by_cases hr : r = 2
    · subst hr
      exact Or.inr (Or.inr ⟨⟨.A 2 q, hv⟩, q, hd, Or.inl rfl, ⟨e⟩⟩)
    · obtain ⟨p, k, hp, hk⟩ := q
      change p = 2 at hd
      subst hd
      haveI : Fact (Nat.Prime 2) := ⟨hp⟩
      let e' : ↥L ⧸ Subgroup.center ↥L ≃* LinearFlag.projectiveSL (r + 1) (GaloisField 2 k) :=
        (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r ⟨2, k, hp, hk⟩ hv)).trans
          (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
            _ _)
      haveI : Fintype (GaloisField 2 k) := Fintype.ofFinite _
      have hdvd := oddCenterLinear_of_griess hGA Y L hL hodd (r + 1) (GaloisField 2 k) ⟨e'⟩
      have h3n : 3 ∣ r + 1 := (h3.trans hdvd).trans (Nat.gcd_dvd_left _ _)
      have h3K : 3 ∣ Fintype.card (GaloisField 2 k) - 1 :=
        (h3.trans hdvd).trans (Nat.gcd_dvd_right _ _)
      have hn5 : 5 ≤ r + 1 := by omega
      obtain ⟨ρ, -, hker, -⟩ := ToralCensus.exists_cover_of_oddCenter
        (oddCenterLinear_of_griess hGA) (kFactCoverLinear_of_griess hGA) hL hodd (by omega) e'
      refine Or.inr (Or.inl (four_le_pRank_of_linCover hn5 ?_ ρ hker))
      rw [Nat.card_units, Nat.card_eq_fintype_card]
      exact h3K
  | _ => exact hd.elim

theorem unitary_case (hL : IsComponentOf L ⊤) (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    (h3 : 3 ∣ Nat.card (Subgroup.center ↥L))
    (hU : IsLieOf IdxTwistedA (↥L ⧸ Subgroup.center ↥L)) : CentralThreeConcl ↥L := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hU
  cases d with
  | twistedA r q =>
    change q.p = 2 at hd
    by_cases hr : r = 2
    · subst hr
      exact Or.inr (Or.inr ⟨⟨.twistedA 2 q, hv⟩, q, hd, Or.inr rfl, ⟨e⟩⟩)
    · have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
      rw [hd] at hc
      obtain ⟨⟨-, -, hn3, hnq⟩, K, hK, hKfin, hcard, ⟨e'⟩⟩ := hc
      letI : Field K := hK
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : Fintype K := Fintype.ofFinite K
      haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 2 * q.exponent)
        (by rw [← Nat.card_eq_fintype_card, hcard, ← pow_mul, mul_comm])
      obtain ⟨ρ, hρs, hker, -⟩ :=
        kFactCoverUnitary Y L hL hodd (r + 1) (2 ^ q.exponent) K hcard hn3 hnq e'
      have hperf := CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hcard hn3 hnq
      have hcomap := CFSG.LocalCores.comap_center_eq_of_perfect hperf ρ hρs hker
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥L) 3 h3
      obtain ⟨s, hs⟩ := hρs (z : ↥L)
      have hsC : s ∈ Subgroup.center (StatedSU (r + 1) (2 ^ q.exponent) K) := by
        rw [← hcomap, Subgroup.mem_comap, hs]
        exact z.2
      have hsS := CFSG.StandardType.center_statedSU_le_scalars hcard (by omega) hsC
      rw [Subgroup.mem_subgroupOf] at hsS
      obtain ⟨c, hc⟩ := hsS
      have hcmem := (CFSG.LinearGroups.scalar_mem_statedSU_iff Nat.prime_two hcard (by omega) c).1
        (hc ▸ s.2)
      have hzs : orderOf z ∣ orderOf s := by
        rw [← Subgroup.orderOf_coe z, ← hs]
        exact orderOf_map_dvd ρ s
      have hpow : ∀ m : ℕ, c ^ m = 1 → s ^ m = 1 := fun m hm => by
        apply Subtype.ext
        rw [SubgroupClass.coe_pow, ← hc, ← map_pow, hm, map_one, OneMemClass.coe_one]
      have h3n : 3 ∣ r + 1 := hz ▸ hzs.trans (orderOf_dvd_of_pow_eq_one (hpow _ hcmem.1))
      have h3q : 3 ∣ 2 ^ q.exponent + 1 :=
        hz ▸ hzs.trans (orderOf_dvd_of_pow_eq_one (hpow _ hcmem.2))
      have hn5 : 5 ≤ r + 1 := by omega
      exact Or.inr (Or.inl (four_le_pRank_of_uniCover hcard hn5 h3q ρ hker))
  | _ => exact hd.elim

theorem core (hGA : GriessAllModelsStatement) (hL : IsComponentOf L ⊤)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) (h3 : 3 ∣ Nat.card (Subgroup.center ↥L))
    (hcl : IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L)) : CentralThreeConcl ↥L := by
  rcases isClassicalTwoOrG2_family_cases hcl with hA | hU | hR
  · exact linear_case hGA hL hodd h3 hA
  · exact unitary_case hL hodd h3 hU
  · rcases oddCenterRest_of_griess hGA Y L hL hodd hR with h1 | ⟨-, he⟩
    · rw [h1] at h3
      exact absurd h3 (by norm_num)
    · exact Or.inl he

end Core

theorem kFactCentralThreeClassical_holds : KFactCentralThreeClassical := by
  intro Y _ _ hY hcl h3
  have hGA := CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYq : CFSG.IsQuasisimple Y :=
    ⟨⟨hY.1⟩, hY.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hY⟩
  set A : Subgroup Y := LinearCover.twoPart (Subgroup.center Y) le_rfl with hAdef
  have hAc : A ≤ Subgroup.center Y := LinearCover.twoPart_le_center
  haveI : A.Normal := ⟨fun n hn g => by
    have hc := Subgroup.mem_center_iff.mp (hAc hn) g
    rw [hc, mul_inv_cancel_right]
    exact hn⟩
  obtain ⟨hQ, -, hcen⟩ := CFSG.LocalCores.quasisimple_central_quotient hYq A hAc
  have hodd : Odd (Nat.card (Subgroup.center (Y ⧸ A))) :=
    CFSG.QuasithinUnique.Setup.X7b.odd_card_center_quotient_twoPart rfl hYq
  let e0 : Y ⧸ Subgroup.center Y ≃* (Y ⧸ A) ⧸ Subgroup.center (Y ⧸ A) :=
    CFSG.QuasithinUnique.Setup.X7b.centralQuotientEquiv hYq hAc
  have hnot3A : ¬ 3 ∣ Nat.card A := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (LinearCover.isPGroup_twoPart (N := Subgroup.center Y)
      (hN := le_rfl))
    intro h
    rw [hk] at h
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  have h3' : 3 ∣ Nat.card (Subgroup.center (Y ⧸ A)) := by
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Y) 3 h3
    have hzc : QuotientGroup.mk' A (z : Y) ∈ Subgroup.center (Y ⧸ A) := by
      rw [hcen]
      exact ⟨z, z.2, rfl⟩
    have hz3 : (z : Y) ^ 3 = 1 := by
      rw [← Subgroup.orderOf_coe] at hz
      rw [← hz]
      exact pow_orderOf_eq_one _
    have hord : orderOf (QuotientGroup.mk' A (z : Y)) = 3 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [← map_pow, hz3, map_one]
      · intro h1
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        obtain ⟨-, j, hj⟩ := LinearCover.mem_twoPart.1 h1
        have hdvd : orderOf (z : Y) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
        rw [Subgroup.orderOf_coe, hz] at hdvd
        exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
    have hzo : orderOf (⟨QuotientGroup.mk' A (z : Y), hzc⟩ : Subgroup.center (Y ⧸ A)) = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact hord
    exact hzo ▸ orderOf_dvd_natCard _
  have hQo : CFSG.Open.IsQuasisimple (Y ⧸ A) := ⟨hQ.1.commutator_eq_top, hQ.2.1⟩
  have hL := CFSG.LocalAnalysis.GLTheoremA.isComponentOf_top_of_isQuasisimple hQo
  let eT : ↥(⊤ : Subgroup (Y ⧸ A)) ≃* Y ⧸ A := Subgroup.topEquiv
  have hcT : (Subgroup.center ↥(⊤ : Subgroup (Y ⧸ A))).map eT.toMonoidHom =
      Subgroup.center (Y ⧸ A) := Subgroup.map_center_eq eT
  have hcard : Nat.card (Subgroup.center ↥(⊤ : Subgroup (Y ⧸ A))) =
      Nat.card (Subgroup.center (Y ⧸ A)) := by
    rw [← hcT]
    exact (Subgroup.card_map_of_injective eT.injective).symm
  let eQ : ↥(⊤ : Subgroup (Y ⧸ A)) ⧸ Subgroup.center ↥(⊤ : Subgroup (Y ⧸ A)) ≃*
      (Y ⧸ A) ⧸ Subgroup.center (Y ⧸ A) := QuotientGroup.congr _ _ eT hcT
  let eAll := eQ.trans e0.symm
  have hcl' := isClassicalTwoOrG2_of_iso eAll.symm hcl
  rcases core hGA hL (hcard ▸ hodd) (hcard ▸ h3') hcl' with h6 | h4 | hLU
  · obtain ⟨e6⟩ := h6
    exact Or.inl ⟨eAll.symm.trans e6⟩
  · have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eT
    have h2 := CFSG.SectionRank.pRank_quotient_eq (p := 3) A hnot3A
    exact Or.inr (Or.inl (by omega))
  · obtain ⟨d, q, hq, hdd, ⟨e⟩⟩ := hLU
    exact Or.inr (Or.inr ⟨d, q, hq, hdd, ⟨eAll.symm.trans e⟩⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.CentralThree
