module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma22FullBender
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma37Core
import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Lemma34 Lemma22 Lemma37 Lemma22Full


section Bender

variable {G : Type} [Group G] [Finite G]

theorem lemma22_bender {K R L : Subgroup G} (hKs : Group.IsSolvable ↥K) (hK : TightlyEmbedded K)
    (hR : IsSylowOf 2 R K) (hL : CFSG.Open.IsQuasisimple ↥L)
    (hNL : normalizer (K : Set G) ≤ normalizer (L : Set G))
    (hRL : IsSylowOf 2 R (centralizer (L : Set G))) :
    standardComponentIsStandard L ∨
      ∃ g : G, conj L g ≤ centralizer (L : Set G) ∧
        centralizer (L : Set G) ≤ normalizer (conj L g : Set G) ∧ R ≤ conj L g ∧
        Odd (Nat.card (center ↥L)) ∧ fusionIsBenderGroup (↥L ⧸ center ↥L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases lemma22_core hKs hK hR hL hNL hRL with h | ⟨g, hAH, hHA, -, hSE⟩
  · exact Or.inl h
  right
  set A := conj L g with hAdef
  have hAq : CFSG.Open.IsQuasisimple ↥A := isQuasisimple_conj hL g
  have hAK : ¬ A ≤ normalizer (K : Set G) := by
    intro h
    apply hSE.1
    rw [subgroupOf_eq_top]
    exact le_inf le_rfl h
  have hR1 : R ≠ ⊥ := ne_bot_of_isSylowOf_of_tightlyEmbedded hK hR
  set X := A ⊔ R with hX
  have hXH : X ≤ centralizer (L : Set G) := sup_le hAH hRL.le
  have hRX : IsSylowOf 2 R X := hRL.of_le le_sup_right hXH
  have hXA : X ≤ normalizer (A : Set G) := sup_le le_normalizer (hRL.le.trans hHA)
  have hSEX := fusionStronglyEmbedded_of_tightlyEmbedded hK hRX hR.le hR1
    (fun h => hAK (le_sup_left.trans h))
  have hA' : CFSG.Open.IsQuasisimple ↥(A.subgroupOf X) :=
    (isQuasisimple_subgroupOf_iff le_sup_left).mpr hAq
  have hAn' : (A.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hXA
  have hR' : IsPGroup 2 ↥(R.subgroupOf X) :=
    hRX.isPGroup.of_equiv (subgroupOfEquivOfLe le_sup_right).symm
  have hAR' : A.subgroupOf X ⊔ R.subgroupOf X = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hnq : ¬ ∀ S : Sylow 2 X, IsCyclic (S : Subgroup X) ∨
      ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2))) := by
    intro h
    obtain ⟨S, hS'⟩ := hRX.exists_sylow_eq_subgroupOf
    obtain ⟨t, ht, ht2, htC⟩ := exists_involution_mem_centralizer hA' hAn' S (h S)
    rw [hS'] at ht
    obtain ⟨htR, -⟩ := mem_inf.mp ht
    rw [mem_subgroupOf] at htR
    rw [centralizer_subgroupOf le_sup_left, mem_subgroupOf] at htC
    have ht2' : orderOf (t : G) = 2 := by rwa [Subgroup.orderOf_coe]
    apply hAK
    intro a ha
    exact CFSG.StandardSubgroupAPI.centralizer_le_normalizer_of_mem_of_orderOf_eq_two hK
      (hR.le htR) ht2' (mem_centralizer_singleton_iff.2 (mem_centralizer_iff.mp htC a ha))
  obtain ⟨hAtop, hodd, hBender⟩ := bender_of_normal_quasisimple hA' hAn' hR' hAR' hSEX hnq
  have hXA' : X ≤ A := by
    rw [subgroupOf_eq_top] at hAtop
    exact hAtop
  let e : ↥X ≃* ↥L := (MulEquiv.subgroupCongr (le_antisymm hXA' le_sup_left)).trans
    (L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
  refine ⟨g, hAH, hHA, le_sup_right.trans hXA', ?_, ?_⟩
  · rw [← card_center_congr e]
    exact hodd
  · exact CFSG.QuasithinUnique.RankOneRecog.fusionIsBenderGroup_of_mulEquiv
      (quotientCenterCongr e) hBender

theorem lemma22_bender_in {X K R L : Subgroup G} (hKX : K ≤ X) (hLX : L ≤ X)
    (hKs : Group.IsSolvable ↥K) (hK : TightlyEmbedded K) (hR : IsSylowOf 2 R K)
    (hL : CFSG.Open.IsQuasisimple ↥L) (hNL : normalizer (K : Set G) ⊓ X ≤ normalizer (L : Set G))
    (hRL : IsSylowOf 2 R (X ⊓ centralizer (L : Set G))) :
    standardComponentIsStandard (L.subgroupOf X) ∨
      ∃ c ∈ X, conj L c ≤ centralizer (L : Set G) ∧
        X ⊓ centralizer (L : Set G) ≤ normalizer (conj L c : Set G) ∧ R ≤ conj L c ∧
        Odd (Nat.card (center ↥L)) ∧ fusionIsBenderGroup (↥L ⧸ center ↥L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRX : R ≤ X := hR.le.trans hKX
  have hN : normalizer ((K.subgroupOf X : Subgroup X) : Set X) ≤
      normalizer ((L.subgroupOf X : Subgroup X) : Set X) := by
    intro x hx
    rw [← subgroupOf_normalizer_eq hKX, mem_subgroupOf] at hx
    rw [← subgroupOf_normalizer_eq hLX, mem_subgroupOf]
    exact hNL ⟨hx, x.2⟩
  have hS : IsSylowOf 2 (R.subgroupOf X)
      (centralizer ((L.subgroupOf X : Subgroup X) : Set X)) := by
    rw [centralizer_subgroupOf hLX, ← inf_subgroupOf_left (centralizer (L : Set G)) X]
    exact (isSylowOf_subgroupOf_iff hRX inf_le_left).mpr hRL
  rcases lemma22_bender (isSolvable_subgroupOf hKX hKs) (tightlyEmbedded_subgroupOf hKX hK)
      ((isSylowOf_subgroupOf_iff hRX hKX).mpr hR) ((isQuasisimple_subgroupOf_iff hLX).mpr hL)
      hN hS with h | ⟨g, hg1, hg2, hg3, hodd, hB⟩
  · exact Or.inl h
  · right
    have hcX : conj L (g : G) ≤ X := conj_le_of_mem hLX g.2
    rw [conj_subgroupOf, centralizer_subgroupOf hLX] at hg1
    rw [conj_subgroupOf, centralizer_subgroupOf hLX, ← subgroupOf_normalizer_eq hcX] at hg2
    rw [conj_subgroupOf] at hg3
    let e : ↥(L.subgroupOf X) ≃* ↥L := subgroupOfEquivOfLe hLX
    refine ⟨g, g.2, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, ?_, ?_⟩
    · have hy' : (⟨y, hcX hy⟩ : X) ∈ (conj L (g : G)).subgroupOf X := hy
      exact hg1 hy'
    · obtain ⟨hyX, hyC⟩ := mem_inf.mp hy
      have hy' : (⟨y, hyX⟩ : X) ∈ (centralizer (L : Set G)).subgroupOf X := hyC
      exact hg2 hy'
    · have hy' : (⟨y, hRX hy⟩ : X) ∈ R.subgroupOf X := hy
      exact hg3 hy'
    · rw [← card_center_congr e]
      exact hodd
    · exact CFSG.QuasithinUnique.RankOneRecog.fusionIsBenderGroup_of_mulEquiv
        (quotientCenterCongr e) hB

end Bender

end CFSG.ComponentClassification.AS76b
