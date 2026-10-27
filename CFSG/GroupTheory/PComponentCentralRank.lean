module

public import CFSG.Foundations.Basic

public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompR
import CFSG.Quasithin.EmptyFaithful.S14110AuxBlocks
import CFSG.LocalAnalysis.AGLEmbedding.ReducedOrbitsAux
import CFSG.LocalAnalysis.AGLEmbedding.RankTools
import CFSG.GroupTheory.CoprimeCentralizerTransport
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped commutatorElement

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

private theorem center_map_pComponent_eq_bot {K : Subgroup H} (hK : CFSG.IsPComponent p K)
    (hZK : Subgroup.center (K ⧸ CFSG.pPrimeCore p K) = ⊥) :
    Subgroup.center (K.map (QuotientGroup.mk' (CFSG.pPrimeCore p H))) = ⊥ := by
  obtain ⟨-, -, hKsub, -, -⟩ := hK
  let e := CFSG.ComponentClassification.CatalogueBHeldSmallCore.subnormalCoreQuotientEquivImage
    p K hKsub
  have hmap := Subgroup.map_center_eq e
  rw [hZK, Subgroup.map_bot] at hmap
  simpa [e] using hmap.symm

theorem pRank_add_one_le_of_pComponent {z : H} (hz : orderOf z = p)
    (hzZ : z ∈ Subgroup.center H) {K : Subgroup H} (hK : CFSG.IsPComponent p K)
    (hZK : Subgroup.center (K ⧸ CFSG.pPrimeCore p K) = ⊥) :
    CFSG.pRank p K + 1 ≤ CFSG.pRank p H := by
  classical
  have hp : p.Prime := Fact.out
  let O : Subgroup H := CFSG.pPrimeCore p H
  let q : H →* H ⧸ O := QuotientGroup.mk' O
  let A : Subgroup (H ⧸ O) := K.map q
  have hZA : Subgroup.center A = ⊥ := by
    simpa [A, q, O] using center_map_pComponent_eq_bot hK (by simpa [O] using hZK)
  have hOnotdvd : ¬ p ∣ Nat.card O := by
    have hcop : Nat.Coprime p (Nat.card O) := by
      simpa [O] using CFSG.pPrimeCore_coprime_card (p := p) (G := H)
    exact hp.coprime_iff_not_dvd.mp hcop
  haveI : O.Normal := CFSG.pPrimeCore_normal
  have hzq : orderOf (q z) = p := by
    simpa [q] using
      CFSG.GroupTheory.CoprimeTransport.orderOf_mk_eq_prime (p := p) (N := O) hOnotdvd hz
  have hzq_center : q z ∈ Subgroup.center (H ⧸ O) := by
    have hq_surj : Function.Surjective q := by
      simpa [q] using QuotientGroup.mk'_surjective O
    exact Subgroup.map_center_le_center hq_surj (Subgroup.mem_map_of_mem q hzZ)
  have hzq_ne : q z ≠ 1 := by
    intro hq1
    have hord := hzq
    rw [hq1, orderOf_one] at hord
    exact (Fact.out : p.Prime).one_lt.ne hord
  have hzq_pow : (q z) ^ p = 1 := by
    have h := pow_orderOf_eq_one (q z)
    rwa [hzq] at h
  have hzA : q z ∉ A := by
    intro hmem
    have hzcenter : (⟨q z, hmem⟩ : A) ∈ Subgroup.center A := by
      rw [Subgroup.mem_center_iff]
      intro a
      exact Subtype.ext (Subgroup.mem_center_iff.mp hzq_center (a : H ⧸ O))
    rw [hZA, Subgroup.mem_bot] at hzcenter
    exact hzq_ne (congrArg Subtype.val hzcenter)
  obtain ⟨E, hEA, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := p) hp.one_lt A
  have hzE : q z ∉ E := fun h => hzA (hEA h)
  have hzcE : q z ∈ Subgroup.centralizer (E : Set (H ⧸ O)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e _
    exact Subgroup.mem_center_iff.mp hzq_center e
  have hplus : CFSG.Open.pRank p A + 1 ≤
      CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ O)) :=
    CFSG.AGLEmbedding.succ_le_pRank_of_isElemAbelian_of_mem_centralizer
      (H := ⊤) hp hE hEcard hzq_pow hzE hzcE le_top (Subgroup.mem_top _)
  have hKmaprank : CFSG.Open.pRank p A = CFSG.Open.pRank p K := by
    simpa [A, q, O] using
      CFSG.PreuniquenessRankFour.Helpers.pRank_quotient_map_of_coprime_normal
        p hp O hOnotdvd K
  have hrank : CFSG.pRank p K = CFSG.Open.pRank p A := by
    calc
      CFSG.pRank p K = CFSG.Open.pRank p K :=
        (CFSG.SectionRank.pRank_eq_open_pRank_top p K).trans
          (CFSG.SectionRank.pRank_eq_pRank_top_subgroup K).symm
      _ = CFSG.Open.pRank p A := hKmaprank.symm
  have htopMap : CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ O)) =
      CFSG.Open.pRank p (⊤ : Subgroup H) := by
    have h := CFSG.PreuniquenessRankFour.Helpers.pRank_quotient_map_of_coprime_normal
      p hp O hOnotdvd (⊤ : Subgroup H)
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective O)] at h
  have htop : CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ O)) = CFSG.pRank p H :=
    htopMap.trans (CFSG.SectionRank.pRank_eq_open_pRank_top p H).symm
  calc
    CFSG.pRank p K + 1 = CFSG.Open.pRank p A + 1 := by rw [hrank]
    _ ≤ CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ O)) := hplus
    _ = CFSG.pRank p H := htop

theorem pRank_add_one_le_of_distinct_pComponents {z : H} (hz : orderOf z = p)
    (hzZ : z ∈ Subgroup.center H) {K M : Subgroup H}
    (hK : CFSG.IsPComponent p K) (hM : CFSG.IsPComponent p M) (hne : K ≠ M)
    (hZK : Subgroup.center (K ⧸ CFSG.pPrimeCore p K) = ⊥)
    (hZM : Subgroup.center (M ⧸ CFSG.pPrimeCore p M) = ⊥) :
    CFSG.pRank p K + CFSG.pRank p M + 1 ≤ CFSG.pRank p H := by
  classical
  have hp : p.Prime := Fact.out
  let O : Subgroup H := CFSG.pPrimeCore p H
  let q : H →* H ⧸ O := QuotientGroup.mk' O
  let A : Subgroup (H ⧸ O) := K.map q
  let B : Subgroup (H ⧸ O) := M.map q
  have hKall := hK
  have hMall := hM
  obtain ⟨K₀, hK₀, -, hKmap, -⟩ := hK
  obtain ⟨M₀, hM₀, -, hMmap, -⟩ := hM
  have hKcomp : CFSG.IsComponent A := by
    rw [show A = K₀ by simpa [A, q, O] using hKmap]
    exact hK₀
  have hMcomp : CFSG.IsComponent B := by
    rw [show B = M₀ by simpa [B, q, O] using hMmap]
    exact hM₀
  have hABne : A ≠ B := by
    intro hAB
    apply hne
    apply CFSG.ComponentClassification.UnbalancedLayer.pComponent_eq_of_map_eq hKall hMall
    simpa [A, B, q, O] using hAB
  have hcommut : ⁅A, B⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hKcomp hMcomp).resolve_left hABne
  have hcommAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    have hle : A ≤ Subgroup.centralizer (B : Set (H ⧸ O)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommut
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm
  have hZA : Subgroup.center A = ⊥ := by
    simpa [A, q, O] using center_map_pComponent_eq_bot hKall (by simpa [O] using hZK)
  have hZB : Subgroup.center B = ⊥ := by
    simpa [B, q, O] using center_map_pComponent_eq_bot hMall (by simpa [O] using hZM)
  have hAB : A ⊓ B = ⊥ :=
    CFSG.Quasithin.S143.InspW2.inf_eq_bot_of_commute hZA hcommAB
  have hAc : ∀ g ∈ A, (∀ l ∈ A, g * l = l * g) → g = 1 := by
    intro g hg hgc
    have hcenter : (⟨g, hg⟩ : A) ∈ Subgroup.center A := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (hgc l l.2).symm
    rw [hZA, Subgroup.mem_bot] at hcenter
    exact congrArg Subtype.val hcenter
  have hBc : ∀ g ∈ B, (∀ l ∈ B, g * l = l * g) → g = 1 := by
    intro g hg hgc
    have hcenter : (⟨g, hg⟩ : B) ∈ Subgroup.center B := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (hgc l l.2).symm
    rw [hZB, Subgroup.mem_bot] at hcenter
    exact congrArg Subtype.val hcenter
  have hZAB : ∀ z ∈ A ⊔ B, (∀ l ∈ A ⊔ B, z * l = l * z) → z = 1 :=
    CFSG.Quasithin.S14110.center_sup_eq_one (X := A) (Y := B) hAc hBc hcommAB
  have hOnotdvd : ¬ p ∣ Nat.card O := by
    have hcop : Nat.Coprime p (Nat.card O) := by
      simpa [O] using CFSG.pPrimeCore_coprime_card (p := p) (G := H)
    exact hp.coprime_iff_not_dvd.mp hcop
  haveI : O.Normal := CFSG.pPrimeCore_normal
  have hzq : orderOf (q z) = p := by
    simpa [q] using
      CFSG.GroupTheory.CoprimeTransport.orderOf_mk_eq_prime (p := p) (N := O) hOnotdvd hz
  have hzq_center : q z ∈ Subgroup.center (H ⧸ O) := by
    have hq_surj : Function.Surjective q := by
      simpa [q] using QuotientGroup.mk'_surjective O
    exact Subgroup.map_center_le_center hq_surj (Subgroup.mem_map_of_mem q hzZ)
  have hzq_ne : q z ≠ 1 := by
    intro hq1
    have hord := hzq
    rw [hq1, orderOf_one] at hord
    exact (Fact.out : p.Prime).one_lt.ne hord
  have hzq_pow : (q z) ^ p = 1 := by
    have h := pow_orderOf_eq_one (q z)
    rwa [hzq] at h
  have hzOutside : q z ∉ A ⊔ B := by
    intro hmem
    have hzc : ∀ l ∈ A ⊔ B, q z * l = l * q z := by
      intro w _
      exact (Subgroup.mem_center_iff.mp hzq_center w).symm
    exact hzq_ne (hZAB (q z) hmem hzc)
  have hABcop : Nat.Coprime p
      (Nat.card (A ⊓ B : Subgroup (H ⧸ O))) := by
    rw [hAB]
    simp
  have hsum : CFSG.Open.pRank p A + CFSG.Open.pRank p B ≤
      CFSG.Open.pRank p (A ⊔ B) :=
    CFSG.AGLEmbedding.pRank_add_le_pRank_sup_of_coprime hp hcommAB hABcop
  obtain ⟨E, hEAB, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := p) hp.one_lt (A ⊔ B)
  have hzE : q z ∉ E := fun h => hzOutside (hEAB h)
  have hzcE : q z ∈ Subgroup.centralizer (E : Set (H ⧸ O)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e _
    exact Subgroup.mem_center_iff.mp hzq_center e
  have hplus : CFSG.Open.pRank p (A ⊔ B) + 1 ≤
      CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ O)) :=
    CFSG.AGLEmbedding.succ_le_pRank_of_isElemAbelian_of_mem_centralizer
      (H := ⊤) hp hE hEcard hzq_pow hzE hzcE le_top (Subgroup.mem_top _)
  have hKmaprank : CFSG.Open.pRank p A = CFSG.Open.pRank p K := by
    simpa [A, q, O] using
      CFSG.PreuniquenessRankFour.Helpers.pRank_quotient_map_of_coprime_normal
        p hp O hOnotdvd K
  have hMmaprank : CFSG.Open.pRank p B = CFSG.Open.pRank p M := by
    simpa [B, q, O] using
      CFSG.PreuniquenessRankFour.Helpers.pRank_quotient_map_of_coprime_normal
        p hp O hOnotdvd M
  have hKrank : CFSG.pRank p K = CFSG.Open.pRank p A := by
    calc
      CFSG.pRank p K = CFSG.Open.pRank p K :=
        (CFSG.SectionRank.pRank_eq_open_pRank_top p K).trans
          (CFSG.SectionRank.pRank_eq_pRank_top_subgroup K).symm
      _ = CFSG.Open.pRank p A := hKmaprank.symm
  have hMrank : CFSG.pRank p M = CFSG.Open.pRank p B := by
    calc
      CFSG.pRank p M = CFSG.Open.pRank p M :=
        (CFSG.SectionRank.pRank_eq_open_pRank_top p M).trans
          (CFSG.SectionRank.pRank_eq_pRank_top_subgroup M).symm
      _ = CFSG.Open.pRank p B := hMmaprank.symm
  have htopMap : CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ O)) =
      CFSG.Open.pRank p (⊤ : Subgroup H) := by
    have h := CFSG.PreuniquenessRankFour.Helpers.pRank_quotient_map_of_coprime_normal
      p hp O hOnotdvd (⊤ : Subgroup H)
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective O)] at h
  have htop : CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ O)) = CFSG.pRank p H :=
    htopMap.trans (CFSG.SectionRank.pRank_eq_open_pRank_top p H).symm
  calc
    CFSG.pRank p K + CFSG.pRank p M + 1 =
        (CFSG.Open.pRank p A + CFSG.Open.pRank p B) + 1 := by rw [hKrank, hMrank]
    _ ≤ CFSG.Open.pRank p (A ⊔ B) + 1 := by omega
    _ ≤ CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ O)) := hplus
    _ = CFSG.pRank p H := htop

end CFSG.GroupTheory

end
