module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelativePairCore
public import CFSG.RankThree.PartOne.KF.F128Act
public import CFSG.RankThree.PerfectCover.CentralQuotientPrimeSupport
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection

public section

namespace CFSG.AGLEmbedding.OuterSylow

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.RankThree.PartOne (centerQuotientConj centerQuotientConj_mem_innerAut_iff)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def ReducedOuterSylow : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card K →
    ∀ S : Subgroup K, IsPGroup p S → ¬ p ∣ S.index → IsCyclic S →
    ∀ α : MulAut K, α ^ p = 1 → (∀ s ∈ S, α s = s) → α ∈ inner K

theorem centerQuotientConj_pow_eq_one {Y : Type} [Group Y] {L : Subgroup Y} {x : Y}
    (hx : x ∈ Subgroup.normalizer (L : Set Y)) {p : ℕ} (hxp : x ^ p = 1) :
    centerQuotientConj L ⟨x, hx⟩ ^ p = 1 := by
  rw [← map_pow]
  have : (⟨x, hx⟩ : Subgroup.normalizer (L : Set Y)) ^ p = 1 :=
    Subtype.ext (by simpa using hxp)
  rw [this, map_one]

theorem centerQuotientConj_mk_of_commute {Y : Type} [Group Y] {L : Subgroup Y} {x : Y}
    (hx : x ∈ Subgroup.normalizer (L : Set Y)) (s : L) (hs : x * (s : Y) = (s : Y) * x) :
    centerQuotientConj L ⟨x, hx⟩ (QuotientGroup.mk s) = QuotientGroup.mk s := by
  show ((L.normalizerMonoidHom ⟨x, hx⟩ s : L) : ↥L ⧸ Subgroup.center ↥L) = _
  congr 1
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hs]
  group

theorem image_sylow_cyclic {Y : Type} [Group Y] {L : Subgroup Y} {p : ℕ} {S : Subgroup Y}
    (hSL : S ≤ L) (hSp : IsPGroup p S) (hSidx : ¬ p ∣ (S.subgroupOf L).index)
    (hScyc : IsCyclic S) :
    IsPGroup p ((S.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) ∧
      ¬ p ∣ ((S.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))).index ∧
      IsCyclic ((S.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) := by
  have hS₀p : IsPGroup p (S.subgroupOf L) := hSp.comap_subtype
  have hS₀cyc : IsCyclic (S.subgroupOf L) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hSL).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hSL).symm.surjective
  refine ⟨hS₀p.map _, fun h => hSidx (h.trans (Subgroup.index_map_dvd (S.subgroupOf L)
    (QuotientGroup.mk'_surjective _))), ?_⟩
  exact isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)

theorem kFactOuterSylowInner_of_reduced (h : ReducedOuterSylow) : KFactOuterSylowInner := by
  intro Y _ _ L p _ hp2 hL hcat hpL S hSL hSp hSidx hScyc x hx hxp hxS
  have hp : p.Prime := Fact.out
  have hperf : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  have hsimple : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2.2.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian L
    hL.2.2
  have hpT : p ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    by_contra hnd
    exact CFSG.RankThree.PerfectCover.perfect_central_quotient_prime_support hp hnd hpL
  obtain ⟨hSbp, hSbidx, hSbcyc⟩ := image_sylow_cyclic hSL hSp hSidx hScyc
  have hfix : ∀ t ∈ (S.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)),
      centerQuotientConj L ⟨x, hx⟩ t = t := by
    rintro t ⟨s, hs, rfl⟩
    exact centerQuotientConj_mk_of_commute hx s (hxS _ hs)
  have hα := h (↥L ⧸ Subgroup.center ↥L) hsimple hnab hcat p hp hp2 hpT _ hSbp hSbidx hSbcyc
    (centerQuotientConj L ⟨x, hx⟩) (centerQuotientConj_pow_eq_one hx hxp) hfix
  exact (centerQuotientConj_mem_innerAut_iff hperf hx).1 hα

end CFSG.AGLEmbedding.OuterSylow
