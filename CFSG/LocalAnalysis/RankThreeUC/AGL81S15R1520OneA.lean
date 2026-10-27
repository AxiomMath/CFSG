module

public import CFSG.RankThree.S4Free.StellmacherSzAllProved
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
public import CFSG.Foundations.Catalog
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SubnormalPrimeCores
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.RankThree.S4Free CFSG.QuasithinUnique CFSG.Open Subgroup

theorem szSections_of_isKGroup (hSz : CFSG.RankThree.PartTwo.KFacts.KPSz) {X : Type} [Group X]
    [Finite X] (hK : CFSG.IsKGroup X) (h3 : ¬ 3 ∣ Nat.card X) : SzSections X := by
  intro H K _ hsimple hnab
  haveI := hsimple
  have hcat : CFSG.Assembly.InCatalog (↥H ⧸ K) :=
    hK.inCatalog_of_surjective H (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
  have h3E : ¬ 3 ∣ Nat.card (↥H ⧸ K) := fun h =>
    h3 (h.trans ((Subgroup.card_quotient_dvd_card K).trans (Subgroup.card_subgroup_dvd_card H)))
  obtain ⟨f, -, a, ha, F, _, _, rfl, hF, he⟩ := hSz (↥H ⧸ K) hnab hcat h3E
  exact ⟨a, ha, F, inferInstance, inferInstance, hF, he⟩

theorem isAdmissibleHost_subtype {X : Type} [Group X] [Finite X] (h3 : ¬ 3 ∣ Nat.card X)
    (hc : CharTwo (⊤ : Subgroup X)) {T : Subgroup X} (hT : IsSylowTwoOf T ⊤) :
    IsAdmissibleHost T.subtype where
  finite := inferInstance
  sym4Free := isSym4Free_of_not_three_dvd h3
  injective := T.subtype_injective
  sylow := by
    have hidx : ¬ 2 ∣ T.index := by
      have := hT.2.2
      rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right] at this
    refine ⟨hT.2.1.toSylow hidx, ?_⟩
    rw [IsPGroup.toSylow_coe, Subgroup.range_subtype]
  centralizer_le := by
    have h : Subgroup.centralizer (pCoreOf 2 (⊤ : Subgroup X) : Set X) ≤ pCoreOf 2 ⊤ := fun x hx =>
      hc ⟨Subgroup.mem_top x, hx⟩
    have hset : {q : Nat.Primes | q.val = 2} = ({⟨2, Nat.prime_two⟩} : Set Nat.Primes) := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩
    have he : oTwo X = pCoreOf 2 (⊤ : Subgroup X) := by
      rw [CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_top_eq_pCore 2, CFSG.pCore_eq_piCore X 2,
        hset]
    rw [he]
    exact h

theorem k520_2_of_isKGroup
    (hSz : CFSG.RankThree.PartTwo.KFacts.KPSz) {X : Type} [Group X] [Finite X]
    (hK : CFSG.IsKGroup X) (h3 : ¬ 3 ∣ Nat.card X) (hc : CharTwo (⊤ : Subgroup X))
    {T : Subgroup X} (hT : IsSylowTwoOf T ⊤) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : 1 < CFSG.Open.pRank p (⊤ : Subgroup X)) :
    ∃ T₀ : Subgroup X, T₀ ≠ ⊥ ∧ T₀ ≤ T ∧ (T₀.subgroupOf T).Characteristic ∧
      1 < CFSG.Open.pRank p (normalizer (T₀ : Set X)) := by
  have hT1 : Nontrivial ↥T := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    rintro rfl
    have hQ : pCoreOf 2 (⊤ : Subgroup X) = ⊥ :=
      le_bot_iff.mp (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT)
    have h : (⊤ : Subgroup X) ⊓ Subgroup.centralizer (pCoreOf 2 (⊤ : Subgroup X) : Set X) ≤
        pCoreOf 2 ⊤ := hc
    rw [hQ] at h
    have hsub : Subsingleton X := by
      refine ⟨fun a b => ?_⟩
      have key : ∀ x : X, x = 1 := fun x => by
        have hx : x ∈ (⊤ : Subgroup X) ⊓ Subgroup.centralizer ((⊥ : Subgroup X) : Set X) := by
          refine ⟨Subgroup.mem_top x, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
          rw [SetLike.mem_coe, Subgroup.mem_bot] at hg
          rw [hg, one_mul, mul_one]
        exact Subgroup.mem_bot.mp (h hx)
      rw [key a, key b]
    have hle : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 0 :=
      CFSG.SectionRank.pRank_le hp.one_lt fun E _ _ => by
        have h1 : Nat.card E ≤ Nat.card X := Subgroup.card_le_card_group E
        have h2 : Nat.card X = 1 := Nat.card_unique
        rw [pow_zero]
        omega
    omega
  obtain ⟨W, hWc, hWne, hWn⟩ := Stell34.stellmacherSzAll_proved.{0, 0} ↥T hT.2.1 hT1
  have hnorm : (W.map T.subtype).Normal :=
    hWn X T.subtype (isAdmissibleHost_subtype h3 hc hT) (szSections_of_isKGroup hSz hK h3)
  refine ⟨W.map T.subtype, ?_, Subgroup.map_subtype_le W, ?_, ?_⟩
  · intro h
    exact hWne ((Subgroup.map_eq_bot_iff_of_injective W T.subtype_injective).mp h)
  · have h : (W.map T.subtype).subgroupOf T = W :=
      Subgroup.comap_map_eq_self_of_injective T.subtype_injective W
    rw [h]
    exact hWc
  · rw [Subgroup.normalizer_eq_top]
    exact hrk

end CFSG.LocalAnalysis.RankThreeUC.S15
