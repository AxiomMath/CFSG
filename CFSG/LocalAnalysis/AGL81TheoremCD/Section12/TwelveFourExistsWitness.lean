module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourSteps
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

private theorem exists_isSylowOf_three_order_three {K : Subgroup G} (h3 : 3 ∣ Nat.card K) :
    ∃ S W : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S K ∧ W ≤ S ∧ Nat.card W = 3 := by
  have := Fact.mk Nat.prime_three
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 h3
  let W : Subgroup G := Subgroup.zpowers (w : G)
  have hWcard : Nat.card W = 3 := by
    change Nat.card (Subgroup.zpowers (w : G)) = 3
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hw]
  have hWK : W ≤ K := by
    change Subgroup.zpowers (w : G) ≤ K
    exact Subgroup.zpowers_le.mpr w.2
  have hWp : IsPGroup 3 W :=
    IsPGroup.of_card (n := 1) (by rw [hWcard, pow_one])
  obtain ⟨Q, hQ⟩ := (hWp.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(Q : Subgroup K).map K.subtype, W, ⟨Q, rfl⟩, ?_, hWcard⟩
  intro x hx
  exact ⟨⟨x, hWK hx⟩, hQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

private theorem twelveFourWitness_of_sylow {M H L S W : Subgroup G} {p d : ℕ} (hd : d.Prime)
    (hYL : TwelveFourYCentL M H L d) (hWS : W ≤ S) (hWcard : Nat.card W = 3)
    (hWX : W ≤ xSub p M H) (hWHM : W ≤ H ⊓ M) (hWLS : W ≤ L ⊔ pCoreOf 2 M)
    (hSrank : 2 ≤ CFSG.Open.pRank d (M ⊓ centralizer (S : Set G))) :
    TwelveFourWitness M p H d W := by
  refine ⟨hWcard, hWX, hYL.2 W hWHM hWLS, ?_⟩
  exact hSrank.trans
    (CFSG.SectionRank.pRank_mono hd.one_lt (inf_le_inf_left M (Subgroup.centralizer_le hWS)))

theorem exists_twelveFourWitness {M H L : Subgroup G} {p d : ℕ} (hd : d.Prime)
    (hL : L ∈ weakBlockSet M H) (hB : TwelveFourBlockFacts M H L)
    (hYL : TwelveFourYCentL M H L d) (hJX : jOne H L ≤ xSub p M H)
    (h7X : TwelveFourASevenLeX M p H L)
    (hJ : ¬ NineThreeFive M L → ∀ S : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 3 S (jOne H L) →
        2 ≤ CFSG.Open.pRank d (M ⊓ centralizer (S : Set G)))
    (h7 : NineThreeFive M L → ∀ S : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 3 S (H ⊓ L) →
        2 ≤ CFSG.Open.pRank d (M ⊓ centralizer (S : Set G))) :
    ∃ W : Subgroup G, TwelveFourWitness M p H d W := by
  by_cases h5 : NineThreeFive M L
  · have h3 : 3 ∣ Nat.card (H ⊓ L : Subgroup G) := by
      rw [inf_comm]
      exact hB.three_dvd
    obtain ⟨S, W, hS, hWS, hWcard⟩ := exists_isSylowOf_three_order_three (K := H ⊓ L) h3
    have hWHL : W ≤ H ⊓ L := hWS.trans hS.le
    have hWHM : W ≤ H ⊓ M := fun x hx => ⟨(hWHL hx).1, hL.le (hWHL hx).2⟩
    have hWLS : W ≤ L ⊔ pCoreOf 2 M := hWHL.trans (inf_le_right.trans le_sup_left)
    have hWU : W ≤ CFSG.ComponentClassification.AS76b.oUpperTwo (H ⊓ L) := by
      intro x hx
      change x ∈ Subgroup.closure {y | y ∈ H ⊓ L ∧ Odd (orderOf y)}
      exact Subgroup.subset_closure ⟨hWHL hx,
        Odd.of_dvd_nat (by rw [hWcard]; norm_num) (Subgroup.orderOf_dvd_natCard W hx)⟩
    exact ⟨W, twelveFourWitness_of_sylow hd hYL hWS hWcard (hWU.trans (h7X h5)) hWHM hWLS
      (h7 h5 S hS)⟩
  · obtain ⟨I, hI⟩ := hB.cZero_nonempty h5
    have h3I : 3 ∣ Nat.card (CFSG.ComponentClassification.AS76b.oUpperTwo I) :=
      hB.three_dvd_oUpperTwo I hI
    have h3J : 3 ∣ Nat.card (jOne H L) :=
      h3I.trans (Subgroup.card_dvd_of_le (IsCZeroMember.oUpperTwo_le_jOne hI))
    obtain ⟨S, W, hS, hWS, hWcard⟩ := exists_isSylowOf_three_order_three (K := jOne H L) h3J
    have hWJ : W ≤ jOne H L := hWS.trans hS.le
    have hWHL : W ≤ H ⊓ L := (hWJ.trans (jOne_le_jZero H L)).trans (jZero_le H L)
    have hWHM : W ≤ H ⊓ M := fun x hx => ⟨(hWHL hx).1, hL.le (hWHL hx).2⟩
    have hWLS : W ≤ L ⊔ pCoreOf 2 M := hWHL.trans (inf_le_right.trans le_sup_left)
    exact ⟨W, twelveFourWitness_of_sylow hd hYL hWS hWcard (hWJ.trans hJX) hWHM hWLS
      (hJ h5 S hS)⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
