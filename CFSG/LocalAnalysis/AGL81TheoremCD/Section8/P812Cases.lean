module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812CaseOne
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.CyclicSylowNormal
import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarSylow
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Five
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Fusion
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.LocalAnalysis.GLTheoremA.Lemma48

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open Subgroup
open CFSG.ABGLocalTools
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {L₁ L₂ : Subgroup G}

private theorem exists_card_three_le_normal_of_isPGroup_three {S : Type*} [Group S] [Finite S]
    {N : Subgroup S} [N.Normal] (hS : IsPGroup 3 S) (hN : Nontrivial N) :
    ∃ A₀ : Subgroup S, A₀ ≤ N ∧ Nat.card A₀ = 3 ∧
      ∀ x ∈ A₀, ∀ s : S, x * s = s * x := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (IsPGroup 3 S) := ⟨hS⟩
  obtain ⟨x, hxne, hxcenter⟩ := CFSG.exists_nontrivial_center_mem_normal (N := N) (p := 3)
  let I : Subgroup S := N ⊓ Subgroup.center S
  have hxI : (x : S) ∈ I := ⟨x.2, hxcenter⟩
  haveI : Nontrivial ↥I := ⟨⟨(x : S), hxI⟩, 1, by
    intro h
    exact hxne (Subtype.ext (congrArg (fun w : ↥I => (w : S)) h))⟩
  have hI3 : IsPGroup 3 ↥I := hS.to_subgroup I
  obtain ⟨n, hnpos, hIcard⟩ := hI3.nontrivial_iff_card.mp inferInstance
  have h3dvd : 3 ∣ Nat.card ↥I := by
    rw [hIcard]
    exact dvd_pow_self 3 hnpos.ne'
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥I) 3 h3dvd
  let z : S := (y : ↥I)
  have hzord : orderOf z = 3 := (Subgroup.orderOf_coe y).trans hyord
  have hzcenter : z ∈ Subgroup.center S := y.2.2
  refine ⟨Subgroup.zpowers z, Subgroup.zpowers_le.mpr y.2.1, ?_, ?_⟩
  · rw [Nat.card_zpowers, hzord]
  · intro a ha s
    rw [Subgroup.mem_zpowers_iff] at ha
    obtain ⟨k, rfl⟩ := ha
    have hcomm : Commute z s := (Subgroup.mem_center_iff.mp hzcenter s).symm
    exact (hcomm.zpow_left k).eq

private theorem mem_centModSubgroup_of_commutator_zpowers_le {L : Subgroup G} {x : G}
    (h : ⁅Subgroup.zpowers x, L⁆ ≤ (CFSG.pPrimeCore p ↥L).map L.subtype) :
    x ∈ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p L := by
  have hmap : L.map (MulAut.conj x).toMonoidHom = L := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro l hl
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hl
      have hc : ⁅x, y⁆ ∈ (CFSG.pPrimeCore p ↥L).map L.subtype :=
        Subgroup.commutator_le.mp h x (Subgroup.mem_zpowers x) y hy
      have hcL : ⁅x, y⁆ ∈ L := Subgroup.map_subtype_le _ hc
      change x * y * x⁻¹ ∈ L
      have heq : x * y * x⁻¹ = ⁅x, y⁆ * y := by
        rw [commutatorElement_def]
        group
      rw [heq]
      exact L.mul_mem hcL hy
    · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
  refine CFSG.LocalAnalysis.GLTheoremA.mem_centModSubgroup.mpr
    ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap, fun l hl => ?_⟩
  have hc : ⁅x, l⁆ ∈ (CFSG.pPrimeCore p ↥L).map L.subtype :=
    Subgroup.commutator_le.mp h x (Subgroup.mem_zpowers x) l hl
  change ⁅l, x⁆ ∈ (CFSG.pPrimeCore p ↥L).map L.subtype
  simpa only [commutatorElement_inv] using Subgroup.inv_mem _ hc



namespace P812Hyp

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {L₁ L₂ : Subgroup G}

theorem exists_card_three_le₁ (h : P812Hyp G M p L₁ L₂) {S : Subgroup G}
    (hS : IsSylowOf 3 S M) :
    ∃ A₁ : Subgroup G, A₁ ≤ L₁ ∧ A₁ ≤ S ∧ Nat.card A₁ = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNM : M ≤ Subgroup.normalizer (L₁ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le₁).mp h.normal₁
  have hSinf : IsSylowOf 3 (S ⊓ L₁) L₁ := hS.inf_of_le_normalizer h.le₁ hNM
  have h3L : 3 ∣ Nat.card L₁ := by
    refine CFSG.GroupTheory.dvd_card_of_one_le_pRank Nat.prime_three ?_
    rw [h.rank_three₁]
  have hDne : S ⊓ L₁ ≠ ⊥ := by
    intro hbot
    have hcard := hSinf.card_eq
    rw [hbot, Subgroup.card_bot] at hcard
    have hpos : 0 < (Nat.card L₁).factorization 3 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' h3L
    have hgt : 1 < 3 ^ (Nat.card L₁).factorization 3 :=
      Nat.one_lt_pow hpos.ne' (by norm_num)
    omega
  obtain ⟨A₁, hA₁D, hA₁3⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_card_three_le_of_isPGroup
      (IsPGroup.to_le hS.isPGroup inf_le_left) hDne
  exact ⟨A₁, hA₁D.trans inf_le_right, hA₁D.trans inf_le_left, hA₁3⟩

theorem exists_card_three_le₂ (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {S : Subgroup G}
    (hS : IsSylowOf 3 S M) :
    ∃ A₂ : Subgroup G, A₂ ≤ L₂ ∧ A₂ ≤ S ∧ Nat.card A₂ = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNM : S ⊔ L₂ ≤ Subgroup.normalizer (L₂ : Set G) := by
    refine sup_le ?_ Subgroup.le_normalizer
    intro s hs
    exact h.mem_normalizer_two_of_odd hSch (hS.le hs)
      (CFSG.Quasithin.B1Red.odd_orderOf_of_isPGroup_three hS.isPGroup hs)
  have hSyl : IsSylowOf 3 S (S ⊔ L₂) :=
    hS.of_le le_sup_left (sup_le hS.le h.le₂)
  have hSinf : IsSylowOf 3 (S ⊓ L₂) L₂ := hSyl.inf_of_le_normalizer le_sup_right hNM
  have h3L : 3 ∣ Nat.card L₂ := by
    refine CFSG.GroupTheory.dvd_card_of_one_le_pRank Nat.prime_three ?_
    rw [h.rank_three₂]
  have hDne : S ⊓ L₂ ≠ ⊥ := by
    intro hbot
    have hcard := hSinf.card_eq
    rw [hbot, Subgroup.card_bot] at hcard
    have hpos : 0 < (Nat.card L₂).factorization 3 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' h3L
    have hgt : 1 < 3 ^ (Nat.card L₂).factorization 3 :=
      Nat.one_lt_pow hpos.ne' (by norm_num)
    omega
  obtain ⟨A₂, hA₂D, hA₂3⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_card_three_le_of_isPGroup
      (IsPGroup.to_le hS.isPGroup inf_le_left) hDne
  exact ⟨A₂, hA₂D.trans inf_le_right, hA₂D.trans inf_le_left, hA₂3⟩

theorem mem_uniqueSet_of_omega_le_sup (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {S A₁ A₂ : Subgroup G}
    (hS : IsSylowOf 3 S M) (hA₁ : A₁ ≤ L₁) (hA₁S : A₁ ≤ S)
    (hA₁3 : Nat.card A₁ = 3) (hA₂ : A₂ ≤ L₂) (hA₂S : A₂ ≤ S)
    (hA₂3 : Nat.card A₂ = 3)
    (hΩ : ∀ x ∈ S, x ^ 3 = 1 → x ∈ A₁ ⊔ A₂) :
    A₁ ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M ∧
      A₂ ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x := fun x hx y hy =>
    h.central₁ hS.le hS.isPGroup hA₁ hA₁S hA₁3 x hx y (hA₂S hy)
  have hAel : CFSG.Open.IsElemAbelian 3 (A₁ ⊔ A₂) :=
    CFSG.Open.IsElemAbelian.sup_of_commute
      (CFSG.GroupTheory.isElemAbelian_of_card_prime hA₁3)
      (CFSG.GroupTheory.isElemAbelian_of_card_prime hA₂3) hcomm
  have hNA : Subgroup.normalizer ((A₁ ⊔ A₂ : Subgroup G) : Set G) ≤ M :=
    h.normalizer_sup_le hSch hA₁ hA₂ hA₁3 hA₂3 hcomm
  have hAS : A₁ ⊔ A₂ ≤ S := sup_le hA₁S hA₂S
  refine ⟨?_, ?_⟩
  · exact mem_uniqueSet_of_normalizer_le_of_omega hS hAS hAel hΩ hNA le_sup_left
      (h.normalizer_le_of_le₁ hSch hA₁ hA₁3)
  · exact mem_uniqueSet_of_normalizer_le_of_omega hS hAS hAel hΩ hNA le_sup_right
      (h.normalizer_le_of_le₂ hSch hA₂ hA₂3)


private theorem caseOne_exists_A0_of_center_ne_bot (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {S A₁ A₂ : Subgroup G}
    (hS : IsSylowOf 3 S M)
    (hCne : (S ⊓ (CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p L₁ ⊓
      CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p L₂)) ≠ ⊥) :
    ∃ A₀ : Subgroup G, A₀ ≤ S ∧ Nat.card A₀ = 3 ∧
      (∀ x ∈ A₀, ∀ s ∈ S, x * s = s * x) ∧
      ⁅A₀, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype ∧
      ⁅A₀, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype := by
  classical
  let C : Subgroup G := S ⊓ (CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p L₁ ⊓
    CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p L₂)
  have hCne' : C ≠ ⊥ := by simpa [C] using hCne
  have hCS : C ≤ S := inf_le_left
  have hS_L1 : S ≤ Subgroup.normalizer (L₁ : Set G) :=
    hS.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer h.le₁).mp h.normal₁)
  have hS_L2 : S ≤ Subgroup.normalizer (L₂ : Set G) := by
    intro s hs
    exact h.mem_normalizer_two_of_odd hSch (hS.le hs)
      (CFSG.Quasithin.B1Red.odd_orderOf_of_isPGroup_three hS.isPGroup hs)
  have hS_C : S ≤ Subgroup.normalizer (C : Set G) := by
    have hD : S ≤ Subgroup.normalizer
        ((CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p L₁ ⊓
          CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p L₂ : Subgroup G) : Set G) := by
      refine (le_inf
        (hS_L1.trans
          (CFSG.LocalAnalysis.GLTheoremA.normalizer_le_normalizer_centModSubgroup p L₁))
        (hS_L2.trans
          (CFSG.LocalAnalysis.GLTheoremA.normalizer_le_normalizer_centModSubgroup p L₂))).trans ?_
      intro g hg
      exact Subgroup.inf_normalizer_le_normalizer_inf hg
    refine (le_inf Subgroup.le_normalizer hD).trans ?_
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf hg
  letI : (C.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCS).mpr hS_C
  have hCSne : C.subgroupOf S ≠ ⊥ := by
    intro hbot
    exact hCne' (by
      have hle : C ⊓ S ≤ ⊥ := disjoint_iff_inf_le.mp (Subgroup.subgroupOf_eq_bot.mp hbot)
      rw [inf_eq_left.mpr hCS] at hle
      exact le_bot_iff.mp hle)
  haveI : Nontrivial ↥(C.subgroupOf S) := (Subgroup.nontrivial_iff_ne_bot _).mpr hCSne
  obtain ⟨A₀', hA₀'C, hA₀'3, hA₀'Z⟩ :=
    exists_card_three_le_normal_of_isPGroup_three (S := ↥S) (N := C.subgroupOf S)
      hS.isPGroup inferInstance
  refine ⟨A₀'.map S.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective S.subtype_injective, hA₀'3]
  · intro x hx s hs
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact congrArg Subtype.val (hA₀'Z a ha ⟨s, hs⟩)
  · refine Subgroup.commutator_le.mpr fun x hx l hl => ?_
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    have haC : (a : G) ∈ C := Subgroup.mem_subgroupOf.mp (hA₀'C ha)
    have hca : (a : G) ∈ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p L₁ := haC.2.1
    have hmem := (CFSG.LocalAnalysis.GLTheoremA.mem_centModSubgroup.mp hca).2 l hl
    change ⁅(a : G), l⁆ ∈ CFSG.Open.GLAPPrimeCoreOf p L₁
    simpa only [commutatorElement_inv] using Subgroup.inv_mem _ hmem
  · refine Subgroup.commutator_le.mpr fun x hx l hl => ?_
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    have haC : (a : G) ∈ C := Subgroup.mem_subgroupOf.mp (hA₀'C ha)
    have hca : (a : G) ∈ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p L₂ := haC.2.2
    have hmem := (CFSG.LocalAnalysis.GLTheoremA.mem_centModSubgroup.mp hca).2 l hl
    change ⁅(a : G), l⁆ ∈ CFSG.Open.GLAPPrimeCoreOf p L₂
    simpa only [commutatorElement_inv] using Subgroup.inv_mem _ hmem

private theorem omega_or_caseTwo_of_center_eq_bot {S A₁ A₂ : Subgroup G}
    (hCbot : (S ⊓ (CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p L₁ ⊓
      CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p L₂)) = ⊥) :
    (∀ x ∈ S, x ^ 3 = 1 → x ∈ A₁ ⊔ A₂) ∨
      ((∀ x ∈ S, ⁅Subgroup.zpowers x, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype →
          ⁅Subgroup.zpowers x, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype → x = 1) ∧
        ∃ x ∈ S, x ^ 3 = 1 ∧ x ∉ A₁ ⊔ A₂) := by
  classical
  let C : Subgroup G := S ⊓ (CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p L₁ ⊓
    CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p L₂)
  have hCbot' : C = ⊥ := by simpa [C] using hCbot
  by_cases hb : ∀ x ∈ S, x ^ 3 = 1 → x ∈ A₁ ⊔ A₂
  · exact Or.inl hb
  · refine Or.inr ⟨fun x hxS hx1 hx2 => ?_, ?_⟩
    · have hmem : x ∈ C :=
        ⟨hxS, ⟨mem_centModSubgroup_of_commutator_zpowers_le hx1,
          mem_centModSubgroup_of_commutator_zpowers_le hx2⟩⟩
      rw [hCbot'] at hmem
      exact Subgroup.mem_bot.mp hmem
    · by_contra hnex
      apply hb
      intro x hxS hx3
      by_contra hx
      exact hnex ⟨x, hxS, hx3, hx⟩

theorem caseOne_or_omega_le_sup_or_caseTwo (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {S A₁ A₂ : Subgroup G}
    (hS : IsSylowOf 3 S M) (hA₁ : A₁ ≤ L₁) (hA₁S : A₁ ≤ S) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) (hA₂S : A₂ ≤ S) (hA₂3 : Nat.card A₂ = 3) :
    (∃ A₀ : Subgroup G, A₀ ≤ S ∧ Nat.card A₀ = 3 ∧
        (∀ x ∈ A₀, ∀ s ∈ S, x * s = s * x) ∧
        ⁅A₀, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype ∧
        ⁅A₀, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype) ∨
      (∀ x ∈ S, x ^ 3 = 1 → x ∈ A₁ ⊔ A₂) ∨
      ((∀ x ∈ S, ⁅Subgroup.zpowers x, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype →
          ⁅Subgroup.zpowers x, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype → x = 1) ∧
        ∃ x ∈ S, x ^ 3 = 1 ∧ x ∉ A₁ ⊔ A₂) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup G := S ⊓ (CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p L₁ ⊓
    CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p L₂)
  by_cases hCbot : C = ⊥
  · right
    exact omega_or_caseTwo_of_center_eq_bot (p := p) (L₁ := L₁) (L₂ := L₂)
      (by simpa [C] using hCbot)
  · left
    exact caseOne_exists_A0_of_center_ne_bot (A₁ := A₁) (A₂ := A₂) h hSch hS
      (by simpa [C] using hCbot)

theorem mem_uniqueSet_or_caseTwo
    (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {A : Subgroup G}
    (hA3 : Nat.card A = 3) (hA : A ≤ L₁ ∨ A ≤ L₂) :
    A ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M ∨
      ∃ S A₁ A₂ : Subgroup G, IsSylowOf 3 S M ∧ A₁ ≤ L₁ ∧ A₁ ≤ S ∧
        Nat.card A₁ = 3 ∧ A₂ ≤ L₂ ∧ A₂ ≤ S ∧ Nat.card A₂ = 3 ∧ (A = A₁ ∨ A = A₂) ∧
        (∀ x ∈ S, ⁅Subgroup.zpowers x, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype →
          ⁅Subgroup.zpowers x, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype → x = 1) ∧
        ∃ x ∈ S, x ^ 3 = 1 ∧ x ∉ A₁ ⊔ A₂ := by
  have hAM : A ≤ M := hA.elim (fun h1 => h1.trans h.le₁) (fun h2 => h2.trans h.le₂)
  have hA3g : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by rw [hA3]; norm_num)
  obtain ⟨S, hS, hAS⟩ :=
    CFSG.RankThree.PartTwo.Sec11.Item1120V0Bar.exists_isSylowOf_ge hAM hA3g
  rcases hA with hA₁ | hA₂
  · obtain ⟨A₂, hA₂L₂, hA₂S, hA₂3⟩ := h.exists_card_three_le₂ hSch hS
    rcases h.caseOne_or_omega_le_sup_or_caseTwo hSch hS hA₁ hAS hA3 hA₂L₂ hA₂S hA₂3 with
      ⟨A₀, hA₀S, hA₀3, hA₀Z, h₁, h₂⟩ | hb | hc
    · left
      exact (h.mem_uniqueSet_of_caseOne hSch hS hA₁ hAS hA3 hA₂L₂ hA₂S hA₂3
        hA₀S hA₀3 hA₀Z h₁ h₂).1
    · left
      exact (h.mem_uniqueSet_of_omega_le_sup hSch hS hA₁ hAS hA3 hA₂L₂ hA₂S hA₂3 hb).1
    · exact Or.inr ⟨S, A, A₂, hS, hA₁, hAS, hA3, hA₂L₂, hA₂S, hA₂3, Or.inl rfl, hc⟩
  · obtain ⟨A₁, hA₁L₁, hA₁S, hA₁3⟩ := h.exists_card_three_le₁ hS
    rcases h.caseOne_or_omega_le_sup_or_caseTwo hSch hS hA₁L₁ hA₁S hA₁3 hA₂ hAS hA3 with
      ⟨A₀, hA₀S, hA₀3, hA₀Z, h₁, h₂⟩ | hb | hc
    · left
      exact (h.mem_uniqueSet_of_caseOne hSch hS hA₁L₁ hA₁S hA₁3 hA₂ hAS hA3
        hA₀S hA₀3 hA₀Z h₁ h₂).2
    · left
      exact (h.mem_uniqueSet_of_omega_le_sup hSch hS hA₁L₁ hA₁S hA₁3 hA₂ hAS hA3 hb).2
    · exact Or.inr ⟨S, A₁, A, hS, hA₁L₁, hA₁S, hA₁3, hA₂, hAS, hA3, Or.inr rfl, hc⟩

end P812Hyp

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
