module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesGen
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Core
import CFSG.LocalAnalysis.GLTheoremA.Basic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open Subgroup
open scoped commutatorElement Pointwise

structure P812Hyp (G : Type) [Group G] [Finite G] (M : Subgroup G) (p : ℕ)
    (L₁ L₂ : Subgroup G) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  strong : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M
  rank : 2 < CFSG.Open.pRank p M
  le₁ : L₁ ≤ M
  le₂ : L₂ ≤ M
  ne : L₁ ≠ L₂
  comp₁ : CFSG.IsPComponent p (L₁.subgroupOf M)
  comp₂ : CFSG.IsPComponent p (L₂.subgroupOf M)
  normal₁ : (L₁.subgroupOf M).Normal
  rank_three : CFSG.Open.pRank 3 M ≤ 3
  rank_p₁ : CFSG.Open.pRank p L₁ = 1
  rank_three₁ : CFSG.Open.pRank 3 L₁ = 1
  rank_p₂ : CFSG.Open.pRank p L₂ = 1
  rank_three₂ : CFSG.Open.pRank 3 L₂ = 1
  six : ∀ B : Subgroup G, B ≤ M → Nat.card B = 3 →
    2 ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (B : Set G)) →
    ¬ CFSG.HallHigman.IsPSolvable p ↥(M ⊓ Subgroup.centralizer (B : Set G)) →
    Subgroup.normalizer (B : Set G) ≤ M

private theorem card_pPrimeCore_subgroupOf_eq {G : Type*} [Group G] [Finite G]
    {H L : Subgroup G} (hLH : L ≤ H) (p : ℕ) :
    Nat.card (CFSG.pPrimeCore p ↥(L.subgroupOf H)) =
      Nat.card (CFSG.pPrimeCore p ↥L) := by
  let e : ↥(L.subgroupOf H) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLH
  rw [← CFSG.pPrimeCore_map_iso p e]
  exact (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm

private theorem eq_one_of_mem_pgroup_of_mem_not_dvd {X : Type*} [Group X] [Finite X]
    {q : ℕ} (hq : q.Prime) {S D : Subgroup X} (hS : IsPGroup q S)
    (hD : ¬ q ∣ Nat.card D) {z : X} (hzS : z ∈ S) (hzD : z ∈ D) : z = 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have hordS : orderOf z ∣ Nat.card S := Subgroup.orderOf_dvd_natCard S hzS
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  have hqpow : orderOf z ∣ q ^ n := hn ▸ hordS
  have hznotq : ¬ q ∣ orderOf z := fun hd =>
    hD (hd.trans (Subgroup.orderOf_dvd_natCard D hzD))
  have hcop : Nat.Coprime (orderOf z) (q ^ n) :=
    Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd hq).mpr hznotq).symm
  exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hqpow)

theorem p812At_of_hyp {G : Type} [Group G] [Finite G] {M : Subgroup G}
    (h : ∀ p L₁ L₂, P812Hyp G M p L₁ L₂ →
      ∀ A : Subgroup G, Nat.card A = 3 → (A ≤ L₁ ∨ A ≤ L₂) →
        A ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M) :
    CFSG.LocalAnalysis.AGL81TheoremCD.Section15.P812At G M := by
  intro p hp hp2 hstrong hrank L₁ L₂ hle₁ hle₂ hne hcomp₁ hcomp₂ hnormal hrankM
    hrankp₁ hrank31 hrankp₂ hrank32 hsix A hA hAin
  exact h p L₁ L₂ ⟨hp, hp2, hstrong, hrank, hle₁, hle₂, hne, hcomp₁, hcomp₂, hnormal,
    hrankM, hrankp₁, hrank31, hrankp₂, hrank32, hsix⟩ A hA hAin

theorem mem_uniqueSet_of_isStronglyPEmbedded_three {G : Type} [Group G] [Finite G]
    {M A : Subgroup G} (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 M)
    (hAM : A ≤ M) (hA : Nat.card A = 3) :
    A ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨hAM, fun g hAg => ?_⟩
  by_cases hg : g ∈ M
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
  · exfalso
    exact hM.2.2 g hg (hA ▸ Subgroup.card_dvd_of_le (le_inf hAM hAg))

private theorem dvd_card_center_quotient_of_prime_order
    {X : Type*} [Group X] [Finite X] {p q : ℕ} (hq : q.Prime)
    {K A : Subgroup X} (hA : A ≤ K) (hAq : Nat.card A = q)
    (hcore : ¬ q ∣ Nat.card (CFSG.pPrimeCore p ↥K))
    (hcentral : ∀ a ∈ A, ∀ b ∈ K,
      ⁅a, b⁆ ∈ (CFSG.pPrimeCore p ↥K).map K.subtype) :
    q ∣ Nat.card (Subgroup.center (↥K ⧸ CFSG.pPrimeCore p ↥K)) := by
  classical
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  let core : Subgroup ↥K := CFSG.pPrimeCore p ↥K
  let Q := ↥K ⧸ core
  let qmap : ↥K →* Q := QuotientGroup.mk' core
  haveI : core.Normal := CFSG.pPrimeCore_normal
  obtain ⟨aA, haAord⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) q (by rw [hAq])
  let aK : ↥K := ⟨(aA : X), hA aA.2⟩
  have haKord : orderOf aK = q := by
    rw [← Subgroup.orderOf_coe aK]
    simpa [aK] using (Subgroup.orderOf_coe aA).trans haAord
  have haKcore : aK ∉ core := by
    intro ha
    have hdisj : Disjoint (A.subgroupOf K) core := by
      refine Subgroup.disjoint_of_coprime_natCard ?_
      rw [show Nat.card (A.subgroupOf K) = q from
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv).trans hAq]
      exact (Nat.Prime.coprime_iff_not_dvd hq).mpr hcore
    have haA' : aK ∈ A.subgroupOf K :=
      Subgroup.mem_subgroupOf.mpr (by simpa [aK] using aA.2)
    have hbot : A.subgroupOf K ⊓ core = ⊥ := hdisj.eq_bot
    have hmem : aK ∈ A.subgroupOf K ⊓ core := ⟨haA', ha⟩
    rw [hbot] at hmem
    have h1 : aK = 1 := Subgroup.mem_bot.mp hmem
    rw [h1, orderOf_one] at haKord
    exact hq.one_lt.ne haKord
  have hqmap_ne : qmap aK ≠ 1 := fun hq1 =>
    haKcore (QuotientGroup.eq_one_iff aK |>.mp hq1)
  have hqmap_ord : orderOf (qmap aK) = q := by
    have hdvd : orderOf (qmap aK) ∣ q := by
      rw [← haKord]
      exact orderOf_map_dvd qmap aK
    rcases (Nat.dvd_prime hq).mp hdvd with h1 | hq'
    · exact absurd (orderOf_eq_one_iff.mp h1) hqmap_ne
    · exact hq'
  have hqcenter : qmap aK ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨bK, rfl⟩ := QuotientGroup.mk'_surjective core y
    have hmem : ⁅aK, bK⁆ ∈ core := by
      obtain ⟨z, hz, hzval⟩ := Subgroup.mem_map.mp (hcentral (aA : X) aA.2 bK bK.2)
      have hzK : z = ⁅aK, bK⁆ := by
        apply K.subtype_injective
        rw [hzval]
        simpa [aK] using (map_commutatorElement K.subtype aK bK).symm
      exact hzK ▸ hz
    have hq1 : qmap ⁅aK, bK⁆ = 1 := (QuotientGroup.eq_one_iff (⁅aK, bK⁆)).mpr hmem
    have hqcomm : ⁅qmap aK, qmap bK⁆ = 1 := by
      rw [← map_commutatorElement qmap aK bK]
      exact hq1
    exact (commutatorElement_eq_one_iff_mul_comm.mp hqcomm).symm
  have hcard : Nat.card (Subgroup.zpowers (qmap aK)) = q := by
    rw [Nat.card_zpowers, hqmap_ord]
  rw [← hcard]
  exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hqcenter)

theorem not_forall_commutator_mem_pPrimeCore {X : Type} [Group X] [Finite X] {p q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {K : Subgroup X}
    (hK : CFSG.IsPComponent p K)
    (hcore : ¬ q ∣ Nat.card (CFSG.pPrimeCore p ↥K))
    (hr : CFSG.Open.pRank q K = 1) {a : X} (ha : a ∈ K) (haq : orderOf a = q) :
    ¬ ∀ b ∈ K, ⁅a, b⁆ ∈ (CFSG.pPrimeCore p ↥K).map K.subtype := by
  classical
  intro hcentral
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have hA : Subgroup.zpowers a ≤ K := Subgroup.zpowers_le.mpr ha
  have hAq : Nat.card (Subgroup.zpowers a) = q := by
    rw [Nat.card_zpowers, haq]
  have haCent : a ∈ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p K := by
    refine CFSG.LocalAnalysis.GLTheoremA.mem_centModSubgroup.mpr
      ⟨Subgroup.le_normalizer ha, ?_⟩
    intro k hk
    change ⁅k, a⁆ ∈ (CFSG.pPrimeCore p ↥K).map K.subtype
    simpa only [commutatorElement_inv] using
      Subgroup.inv_mem _ (hcentral k hk)
  have hcentralA : ∀ x ∈ Subgroup.zpowers a, ∀ k ∈ K,
      ⁅x, k⁆ ∈ (CFSG.pPrimeCore p ↥K).map K.subtype := by
    intro x hx k hk
    have hxCent : x ∈ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p K :=
      Subgroup.zpowers_le.mpr haCent hx
    have hmem := (CFSG.LocalAnalysis.GLTheoremA.mem_centModSubgroup.mp hxCent).2 k hk
    have hmem' : ⁅k, x⁆ ∈ (CFSG.pPrimeCore p ↥K).map K.subtype := hmem
    change ⁅x, k⁆ ∈ (CFSG.pPrimeCore p ↥K).map K.subtype
    simpa only [commutatorElement_inv] using Subgroup.inv_mem _ hmem'
  have hqcenter :=
    dvd_card_center_quotient_of_prime_order hq hA hAq hcore hcentralA
  let core : Subgroup ↥K := CFSG.pPrimeCore p ↥K
  let Q := ↥K ⧸ core
  haveI : core.Normal := CFSG.pPrimeCore_normal
  letI : Group.IsPerfect ↥K :=
    CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hK
  have hQrank : CFSG.Open.pRank q (⊤ : Subgroup Q) = 1 := by
    rw [CFSG.SectionRank.pRank_quotient_eq core hcore,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K]
    exact hr
  exact (CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.not_dvd_card_center_of_pRank_eq_one
    (q := q) hq2 hQrank) hqcenter

theorem commute_of_isPComponent {X : Type} [Group X] [Finite X] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    {K₁ K₂ : Subgroup X} (hK₁ : CFSG.IsPComponent p K₁) (hK₂ : CFSG.IsPComponent p K₂)
    (hne : K₁ ≠ K₂) (hcore₁ : ¬ q ∣ Nat.card (CFSG.pPrimeCore p ↥K₁))
    {S : Subgroup X} (hS : IsPGroup q S) {x y : X}
    (hx : x ∈ S ⊓ K₁) (hy : y ∈ S ⊓ K₂) : x * y = y * x := by
  classical
  have hcore :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation
      p hp K₁ K₂ hK₁ hK₂).2 hne
  have hxK₁ : x ∈ K₁ := (Subgroup.mem_inf.mp hx).2
  have hyK₂ : y ∈ K₂ := (Subgroup.mem_inf.mp hy).2
  have hxS : x ∈ S := (Subgroup.mem_inf.mp hx).1
  have hyS : y ∈ S := (Subgroup.mem_inf.mp hy).1
  have hmemCore : ⁅x, y⁆ ∈ (CFSG.pPrimeCore p ↥K₁).map K₁.subtype :=
    (hcore.2.2.1 (Subgroup.commutator_mem_commutator hxK₁ hyK₂)).1
  have hmemS : ⁅x, y⁆ ∈ S :=
    Subgroup.commutator_le_self S (Subgroup.commutator_mem_commutator hxS hyS)
  have hDq : ¬ q ∣ Nat.card ((CFSG.pPrimeCore p ↥K₁).map K₁.subtype) := by
    rw [Subgroup.card_map_of_injective K₁.subtype_injective]
    exact hcore₁
  have h1 : ⁅x, y⁆ = 1 :=
    eq_one_of_mem_pgroup_of_mem_not_dvd hq hS hDq hmemS hmemCore
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem not_le_of_isPComponent {X : Type} [Group X] [Finite X] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2)
    {K₁ K₂ : Subgroup X} (hK₁ : CFSG.IsPComponent p K₁) (hK₂ : CFSG.IsPComponent p K₂)
    (hne : K₁ ≠ K₂) (hcore₂ : ¬ q ∣ Nat.card (CFSG.pPrimeCore p ↥K₂))
    (hr₂ : CFSG.Open.pRank q K₂ = 1) {A : Subgroup X}
    (hA : A ≤ K₁) (hAq : Nat.card A = q) : ¬ A ≤ K₂ := by
  classical
  intro hA2
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) q (by rw [hAq])
  have haA : (a : X) ∈ A := a.2
  have haK₁ : (a : X) ∈ K₁ := hA haA
  have haK₂ : (a : X) ∈ K₂ := hA2 haA
  have haq : orderOf (a : X) = q := (Subgroup.orderOf_coe a).trans ha
  have hcore :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation
      p hp K₁ K₂ hK₁ hK₂).2 hne
  have hcentral : ∀ b ∈ K₂, ⁅(a : X), b⁆ ∈ (CFSG.pPrimeCore p ↥K₂).map K₂.subtype := by
    intro b hb
    exact (hcore.2.2.1 (Subgroup.commutator_mem_commutator haK₁ hb)).2
  exact not_forall_commutator_mem_pPrimeCore hq hq2 hK₂ hcore₂ hr₂ haK₂ haq hcentral

namespace P812Hyp

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {L₁ L₂ : Subgroup G}

theorem subgroupOf_ne (h : P812Hyp G M p L₁ L₂) :
    L₁.subgroupOf M ≠ L₂.subgroupOf M := by
  intro hEq
  apply h.ne
  have hmap := congrArg (Subgroup.map (Subgroup.subtype M)) hEq
  simpa [Subgroup.map_subgroupOf_eq_of_le h.le₁,
    Subgroup.map_subgroupOf_eq_of_le h.le₂] using hmap

theorem pRank_three_subgroupOf₁ (h : P812Hyp G M p L₁ L₂) :
    CFSG.Open.pRank 3 (L₁.subgroupOf M) = 1 :=
  (CFSG.RankThreeEvenClassification.Helpers.pRank_subgroupOf 3 Nat.prime_three L₁ M h.le₁).trans
    h.rank_three₁

theorem pRank_three_subgroupOf₂ (h : P812Hyp G M p L₁ L₂) :
    CFSG.Open.pRank 3 (L₂.subgroupOf M) = 1 :=
  (CFSG.RankThreeEvenClassification.Helpers.pRank_subgroupOf 3 Nat.prime_three L₂ M h.le₂).trans
    h.rank_three₂

theorem not_three_dvd_card_pPrimeCore₁ (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) :
    ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥L₁) := by
  have h3 := not_three_dvd_card_pPrimeCore_of_isPComponent
    (X := ↥M) (p := p) (L := L₁.subgroupOf M) h.prime hSch h.comp₁
    h.pRank_three_subgroupOf₁
  intro hd
  exact h3 ((card_pPrimeCore_subgroupOf_eq h.le₁ p) ▸ hd)

theorem not_three_dvd_card_pPrimeCore₂ (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) :
    ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥L₂) := by
  have h3 := not_three_dvd_card_pPrimeCore_of_isPComponent
    (X := ↥M) (p := p) (L := L₂.subgroupOf M) h.prime hSch h.comp₂
    h.pRank_three_subgroupOf₂
  intro hd
  exact h3 ((card_pPrimeCore_subgroupOf_eq h.le₂ p) ▸ hd)

theorem commute_of_isPGroup (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    {S : Subgroup G} (hS : IsPGroup 3 S)
    {x y : G} (hx : x ∈ S ⊓ L₁) (hy : y ∈ S ⊓ L₂) : x * y = y * x := by
  have hxM : x ∈ M := h.le₁ (Subgroup.mem_inf.mp hx).2
  have hyM : y ∈ M := h.le₂ (Subgroup.mem_inf.mp hy).2
  have hcore₁ : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥(L₁.subgroupOf M)) := by
    rw [show Nat.card (CFSG.pPrimeCore p ↥(L₁.subgroupOf M)) =
        Nat.card (CFSG.pPrimeCore p ↥L₁) from card_pPrimeCore_subgroupOf_eq h.le₁ p]
    exact h.not_three_dvd_card_pPrimeCore₁ hSch
  let xM : ↥M := ⟨x, hxM⟩
  let yM : ↥M := ⟨y, hyM⟩
  let Ssub : Subgroup ↥M := S.subgroupOf M
  have hSsub : IsPGroup 3 Ssub := hS.comap_subtype
  have hxS : xM ∈ Ssub ⊓ L₁.subgroupOf M :=
    ⟨(Subgroup.mem_inf.mp hx).1, (Subgroup.mem_inf.mp hx).2⟩
  have hyS : yM ∈ Ssub ⊓ L₂.subgroupOf M :=
    ⟨(Subgroup.mem_inf.mp hy).1, (Subgroup.mem_inf.mp hy).2⟩
  have hcomm := commute_of_isPComponent h.prime Nat.prime_three h.comp₁ h.comp₂
    h.subgroupOf_ne hcore₁ hSsub hxS hyS
  simpa [xM, yM] using congrArg Subtype.val hcomm

theorem not_le_two (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {A : Subgroup G}
    (hA : A ≤ L₁) (hA3 : Nat.card A = 3) : ¬ A ≤ L₂ := by
  have hcore₂ : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥(L₂.subgroupOf M)) := by
    rw [show Nat.card (CFSG.pPrimeCore p ↥(L₂.subgroupOf M)) =
        Nat.card (CFSG.pPrimeCore p ↥L₂) from card_pPrimeCore_subgroupOf_eq h.le₂ p]
    exact h.not_three_dvd_card_pPrimeCore₂ hSch
  let AM : Subgroup ↥M := A.subgroupOf M
  have hAM₁ : AM ≤ L₁.subgroupOf M := fun a ha => hA (Subgroup.mem_subgroupOf.mp ha)
  have hAMcard : Nat.card AM = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hA.trans h.le₁)).toEquiv).trans hA3
  have hnot := not_le_of_isPComponent h.prime Nat.prime_three (by norm_num) h.comp₁ h.comp₂
    h.subgroupOf_ne hcore₂ h.pRank_three_subgroupOf₂ hAM₁ hAMcard
  intro hA2
  exact hnot fun a ha => hA2 (Subgroup.mem_subgroupOf.mp ha)

end P812Hyp

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
