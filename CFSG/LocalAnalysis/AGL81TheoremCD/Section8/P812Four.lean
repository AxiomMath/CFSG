module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Two
public import CFSG.GroupTheory.PComponentCover
import CFSG.GroupTheory.PGroup.RankTwoCommute
import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer
import CFSG.GroupTheory.RankOneNormalCentralizer
import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
import CFSG.GH74.Generic.BProg.BpGeneral
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
import CFSG.Quasithin.Vol2.Ch11SecA12Cop

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {L₁ L₂ : Subgroup G}

theorem commutator_subgroupOf_le_pPrimeCore {X : Type*} [Group X] [Finite X] {p : ℕ}
    {M B L : Subgroup X} (hBM : B ≤ M) (hLM : L ≤ M)
    (h : ⁅B, L⁆ ≤ (CFSG.pPrimeCore p ↥L).map L.subtype) :
    ⁅B.subgroupOf M, L.subgroupOf M⁆ ≤
      (CFSG.pPrimeCore p ↥(L.subgroupOf M)).map (L.subgroupOf M).subtype := by
  have hmap : (⁅B.subgroupOf M, L.subgroupOf M⁆ : Subgroup ↥M).map M.subtype = ⁅B, L⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hBM,
      Subgroup.map_subgroupOf_eq_of_le hLM]
  have hcore :
      ((CFSG.pPrimeCore p ↥(L.subgroupOf M)).map (L.subgroupOf M).subtype).map M.subtype =
        (CFSG.pPrimeCore p ↥L).map L.subtype :=
    CFSG.GH74.Generic.BProg.map_pPrimeCoreOf_subgroupOf p hLM
  rw [← hmap, ← hcore] at h
  exact (Subgroup.map_le_map_iff_of_injective M.subtype_injective).mp h

theorem not_isPSolvable_inf_centralizer_of_subgroupOf {X : Type} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] {M K B : Subgroup X} (hKM : K ≤ M) (hBM : B ≤ M)
    (h : ¬ CFSG.HallHigman.IsPSolvable p
      ↥(K.subgroupOf M ⊓ Subgroup.centralizer ((B.subgroupOf M : Subgroup M) : Set M))) :
    ¬ CFSG.HallHigman.IsPSolvable p ↥(M ⊓ Subgroup.centralizer (B : Set X)) := by
  intro hsolv
  let H : Subgroup ↥M :=
    K.subgroupOf M ⊓ Subgroup.centralizer ((B.subgroupOf M : Subgroup M) : Set M)
  have hHmap : H.map M.subtype ≤ M ⊓ Subgroup.centralizer (B : Set X) := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    refine ⟨w.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro b hb
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hw.2 ⟨b, hBM hb⟩ (Subgroup.mem_subgroupOf.mpr hb))
  have hHsolv : CFSG.HallHigman.IsPSolvable p ↥(H.map M.subtype) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
      hsolv hHmap
  have hHsolv' : CFSG.HallHigman.IsPSolvable p ↥H :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (Subgroup.equivMapOfInjective H M.subtype M.subtype_injective).symm hHsolv
  exact h hHsolv'

namespace P812Hyp

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {L₁ L₂ : Subgroup G}

theorem le_normalizer_two_of_card_three (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {A : Subgroup G}
    (hAM : A ≤ M) (hA3 : Nat.card A = 3) :
    A ≤ Subgroup.normalizer (L₂ : Set G) := by
  intro a ha
  have hdvd : orderOf a ∣ 3 := hA3 ▸ Subgroup.orderOf_dvd_natCard A ha
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · rw [orderOf_eq_one_iff.mp h1]
    exact Subgroup.one_mem _
  · exact h.mem_normalizer_two_of_odd hSch (hAM ha) (by rw [h3]; exact ⟨1, by norm_num⟩)

theorem two_le_pRank_inf_centralizer_of_le₁ (h : P812Hyp G M p L₁ L₂) {A : Subgroup G}
    (hA : A ≤ L₁) (hA3 : Nat.card A = 3) :
    2 ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (A : Set G)) := by
  have hL : M ≤ Subgroup.normalizer (L₁ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le₁).mp h.normal₁
  exact CFSG.GroupTheory.two_le_pRank_inf_centralizer h.prime h.ne_two h.le₁ hL hA hA3
    (le_of_eq h.rank_three₁) (le_of_eq h.rank_p₁) h.rank

private theorem two_le_pRank_inf_centralizer_of_le₂ (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {A : Subgroup G}
    (hA : A ≤ L₂) (hA3 : Nat.card A = 3) :
    2 ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (A : Set G)) := by
  let M₂ : Subgroup G := M ⊓ Subgroup.normalizer (L₂ : Set G)
  have hM₂M : M₂ ≤ M := inf_le_left
  have hrank : CFSG.Open.pRank p M ≤ CFSG.Open.pRank p M₂ := by
    obtain ⟨E, hEM, hEea, hEcard⟩ := CFSG.SectionRank.exists_pRank h.prime.one_lt M
    have hE₂ : E ≤ M₂ := by
      intro x hx
      exact ⟨hEM hx, h.mem_normalizer_two_of_odd hSch (hEM hx)
        (Odd.of_dvd_nat (h.prime.odd_of_ne_two h.ne_two)
          (orderOf_dvd_of_pow_eq_one (hEea.2 x hx)))⟩
    exact CFSG.SectionRank.le_pRank h.prime.one_lt hE₂ hEea hEcard
  have hL₂M₂ : L₂ ≤ M₂ := by
    intro x hx
    exact ⟨h.le₂ hx, Subgroup.le_normalizer hx⟩
  have hM₂N : M₂ ≤ Subgroup.normalizer (L₂ : Set G) := inf_le_right
  have hrank₂ := CFSG.GroupTheory.two_le_pRank_inf_centralizer h.prime h.ne_two hL₂M₂ hM₂N
    hA hA3 (le_of_eq h.rank_three₂) (le_of_eq h.rank_p₂) (h.rank.trans_le hrank)
  have hle : M₂ ⊓ Subgroup.centralizer (A : Set G) ≤
      M ⊓ Subgroup.centralizer (A : Set G) := by
    intro x hx
    exact ⟨hM₂M hx.1, hx.2⟩
  exact hrank₂.trans (CFSG.SectionRank.pRank_mono h.prime.one_lt hle)

private theorem dvd_card_inf_centralizer_of_isPComponent (h : P812Hyp G M p L₁ L₂)
    {q : ℕ} {K B : Subgroup ↥M} (hK : CFSG.IsPComponent p K) (hq : q.Prime)
    (hB : IsPGroup q B) (hBK : B ≤ Subgroup.normalizer (K : Set ↥M))
    (hcomm : ⁅B, K⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hcop : ¬ q ∣ Nat.card (CFSG.pPrimeCore p ↥K)) :
    p ∣ Nat.card ↥(K ⊓ Subgroup.centralizer (B : Set ↥M)) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  refine CFSG.GroupTheory.dvd_card_of_covers h.prime hK inf_le_left ?_
  intro b hb
  have hcop' : Nat.Coprime q (Nat.card (((CFSG.pPrimeCore p ↥K).map K.subtype :
      Subgroup ↥M))) := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd hq).mpr hcop
  have hcomm' : ∀ a ∈ B, ∀ d ∈ K, a * d * a⁻¹ * d⁻¹ ∈
      (CFSG.pPrimeCore p ↥K).map K.subtype := by
    intro a ha d hd
    simpa [commutatorElement_def, mul_assoc] using Subgroup.commutator_le.mp hcomm a ha d hd
  exact CFSG.Quasithin.Vol2.Ch11.SecA.exists_mem_centralizer_of_coprime hq hB hBK
    (Subgroup.map_subtype_le (CFSG.pPrimeCore p ↥K))
    (CFSG.GroupTheory.le_normalizer_map_pPrimeCore K) hcop' hcomm' hb

private theorem exists_order_p_mem_inf_centralizer_of_commutator_le (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {A₀ : Subgroup G}
    (hA₀ : A₀ ≤ M) (hA3 : Nat.card A₀ = 3)
    (h₁ : ⁅A₀, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype) :
    ∃ x ∈ L₁.subgroupOf M ⊓
      Subgroup.centralizer ((A₀.subgroupOf M : Subgroup M) : Set M), orderOf x = p := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hcardM : Nat.card (A₀.subgroupOf M) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀).toEquiv).trans hA3
  have hB : IsPGroup 3 (A₀.subgroupOf M) :=
    IsPGroup.of_card (n := 1) (by rw [hcardM]; norm_num)
  have hN₁ : A₀.subgroupOf M ≤ Subgroup.normalizer (L₁.subgroupOf M : Set ↥M) := by
    rw [← Subgroup.subgroupOf_normalizer_eq h.le₁]
    intro x _
    exact Subgroup.mem_subgroupOf.mpr
      ((Subgroup.normal_subgroupOf_iff_le_normalizer h.le₁).mp h.normal₁ x.2)
  have hdvd := dvd_card_inf_centralizer_of_isPComponent h h.comp₁ Nat.prime_three hB hN₁
    (commutator_subgroupOf_le_pPrimeCore hA₀ h.le₁ h₁)
    (not_three_dvd_card_pPrimeCore_of_isPComponent h.prime hSch h.comp₁
      h.pRank_three_subgroupOf₁)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(L₁.subgroupOf M ⊓
      Subgroup.centralizer ((A₀.subgroupOf M : Subgroup M) : Set M))) p hdvd
  exact ⟨(x : ↥M), x.2, (Subgroup.orderOf_coe x).trans hx⟩

private theorem exists_order_p_mem_inf_centralizer_sup (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {A₀ : Subgroup G}
    (hA₀ : A₀ ≤ M) (hA3 : Nat.card A₀ = 3)
    (h₂ : ⁅A₀, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype) {x₁ : ↥M}
    (hx₁ : x₁ ∈ L₁.subgroupOf M)
    (hx₁C : x₁ ∈ Subgroup.centralizer ((A₀.subgroupOf M : Subgroup M) : Set M))
    (hx₁ord : orderOf x₁ = p) :
    ∃ x₂ ∈ L₂.subgroupOf M ⊓ Subgroup.centralizer
      (((Subgroup.zpowers x₁ ⊔ A₀.subgroupOf M : Subgroup ↥M)) : Set ↥M), orderOf x₂ = p := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup ↥M := L₂.subgroupOf M
  let B₁ : Subgroup ↥M := Subgroup.zpowers x₁
  let B₂ : Subgroup ↥M := A₀.subgroupOf M
  have hK :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation
      p h.prime (L₁.subgroupOf M) K h.comp₁ h.comp₂).2 h.subgroupOf_ne
  have hcard₂ : Nat.card B₂ = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀).toEquiv).trans hA3
  have hB₂ : IsPGroup 3 B₂ := IsPGroup.of_card (n := 1) (by rw [hcard₂]; norm_num)
  have hB₁ : IsPGroup p B₁ :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx₁ord]; norm_num)
  have hB₁K₁ : B₁ ≤ L₁.subgroupOf M := Subgroup.zpowers_le.mpr hx₁
  have hB₁K : B₁ ≤ Subgroup.normalizer (K : Set ↥M) := hB₁K₁.trans hK.2.1
  have hB₂K : B₂ ≤ Subgroup.normalizer (K : Set ↥M) := by
    rw [← Subgroup.subgroupOf_normalizer_eq h.le₂]
    intro x hx
    have hxA : (x : G) ∈ A₀ := Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_subgroupOf.mpr
      (h.le_normalizer_two_of_card_three hSch hA₀ hA3 hxA)
  have hcomm₁ : ⁅B₁, K⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype :=
    (Subgroup.commutator_mono hB₁K₁ le_rfl).trans (hK.2.2.1.trans inf_le_right)
  have hcomm₂ : ⁅B₂, K⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype :=
    commutator_subgroupOf_le_pPrimeCore hA₀ h.le₂ h₂
  have hc : ∀ x ∈ B₁, ∀ y ∈ B₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hcomm : Commute x₁ y := (Subgroup.mem_centralizer_iff.mp hx₁C y hy).symm
    exact (hcomm.zpow_left k).eq
  have hcop₁ : ¬ p ∣ Nat.card (((CFSG.pPrimeCore p ↥K).map K.subtype : Subgroup ↥M)) := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd h.prime).mp CFSG.pPrimeCore_coprime_card
  have hcop₂ : ¬ 3 ∣ Nat.card (((CFSG.pPrimeCore p ↥K).map K.subtype : Subgroup ↥M)) := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact not_three_dvd_card_pPrimeCore_of_isPComponent h.prime hSch h.comp₂
      h.pRank_three_subgroupOf₂
  have hcov : ∀ b ∈ K, ∃ c ∈ K ⊓
      Subgroup.centralizer ((B₁ ⊔ B₂ : Subgroup ↥M) : Set ↥M),
      c⁻¹ * b ∈ (CFSG.pPrimeCore p ↥K).map K.subtype := fun b hb =>
    CFSG.GroupTheory.exists_mem_inf_centralizer_sup h.prime Nat.prime_three
      (Subgroup.map_subtype_le (CFSG.pPrimeCore p ↥K))
      (CFSG.GroupTheory.le_normalizer_map_pPrimeCore K)
      hB₁ hB₂ hc hB₁K hB₂K hcomm₁ hcomm₂ hcop₁ hcop₂ hb
  have hdvd := CFSG.GroupTheory.dvd_card_of_covers h.prime h.comp₂ inf_le_left hcov
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(K ⊓ Subgroup.centralizer ((B₁ ⊔ B₂ : Subgroup ↥M) : Set ↥M))) p hdvd
  exact ⟨(x : ↥M), x.2, (Subgroup.orderOf_coe x).trans hx⟩

private theorem two_le_pRank_inf_centralizer_of_commutator_le (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {A₀ : Subgroup G}
    (hA₀ : A₀ ≤ M) (hA3 : Nat.card A₀ = 3)
    (h₁ : ⁅A₀, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype)
    (h₂ : ⁅A₀, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype) :
    2 ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (A₀ : Set G)) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨x₁, hx₁, hx₁ord⟩ :=
    exists_order_p_mem_inf_centralizer_of_commutator_le h hSch hA₀ hA3 h₁
  obtain ⟨x₂, hx₂, hx₂ord⟩ :=
    exists_order_p_mem_inf_centralizer_sup h hSch hA₀ hA3 h₂ hx₁.1 hx₁.2 hx₁ord
  have hx₂not : x₂ ∉ Subgroup.zpowers x₁ := by
    intro hmem
    have hx₂L₁ : x₂ ∈ L₁.subgroupOf M := Subgroup.zpowers_le.mpr hx₁.1 hmem
    have hcard : Nat.card (Subgroup.zpowers x₂) = p := by
      rw [Nat.card_zpowers, hx₂ord]
    have hcop₂ : ¬ p ∣ Nat.card (CFSG.pPrimeCore p ↥(L₂.subgroupOf M)) :=
      (Nat.Prime.coprime_iff_not_dvd h.prime).mp CFSG.pPrimeCore_coprime_card
    have hr₂ : CFSG.Open.pRank p (L₂.subgroupOf M) = 1 := by
      rw [CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_subgroupOf p h.le₂]
      exact h.rank_p₂
    exact not_le_of_isPComponent h.prime h.prime h.ne_two h.comp₁ h.comp₂ h.subgroupOf_ne
      hcop₂ hr₂ (Subgroup.zpowers_le.mpr hx₂L₁) hcard (Subgroup.zpowers_le.mpr hx₂.1)
  have hx₁C : (x₁ : G) ∈ Subgroup.centralizer (A₀ : Set G) := by
    have h := hx₁.2
    rwa [CFSG.QuasiDihedralFusion.centralizer_subgroupOf hA₀] at h
  have hx₂C : (x₂ : G) ∈ Subgroup.centralizer (A₀ : Set G) := by
    have hC₀ : x₂ ∈ Subgroup.centralizer ((A₀.subgroupOf M : Subgroup M) : Set M) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_iff.mp hx₂.2 y (Subgroup.mem_sup_right hy)
    have h := hC₀
    rwa [CFSG.QuasiDihedralFusion.centralizer_subgroupOf hA₀] at h
  have hcomm₁₂ : Commute (x₁ : G) (x₂ : G) := by
    have h := Subgroup.mem_centralizer_iff.mp hx₂.2 x₁
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁))
    show (x₁ : G) * (x₂ : G) = (x₂ : G) * (x₁ : G)
    simpa using congrArg Subtype.val h
  have hx₂not' : (x₂ : G) ∉ Subgroup.zpowers (x₁ : G) := by
    intro hmem
    apply hx₂not
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩
  exact CFSG.GroupTheory.two_le_pRank_of_commute ⟨x₁.2, hx₁C⟩ ⟨x₂.2, hx₂C⟩
    ((Subgroup.orderOf_coe x₁).trans hx₁ord) ((Subgroup.orderOf_coe x₂).trans hx₂ord)
    hcomm₁₂ hx₂not'

theorem normalizer_le_of_le₁ (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {A : Subgroup G}
    (hA : A ≤ L₁) (hA3 : Nat.card A = 3) :
    Subgroup.normalizer (A : Set G) ≤ M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hAM : A ≤ M := hA.trans h.le₁
  have hK :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation
      p h.prime (L₁.subgroupOf M) (L₂.subgroupOf M) h.comp₁ h.comp₂).2 h.subgroupOf_ne
  have hAM₁ : A.subgroupOf M ≤ L₁.subgroupOf M := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hA (Subgroup.mem_subgroupOf.mp hx))
  have hcardM : Nat.card (A.subgroupOf M) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv).trans hA3
  have hB : IsPGroup 3 (A.subgroupOf M) :=
    IsPGroup.of_card (n := 1) (by rw [hcardM]; norm_num)
  have hBK : A.subgroupOf M ≤ Subgroup.normalizer (L₂.subgroupOf M : Set ↥M) :=
    hAM₁.trans hK.2.1
  have hcomm : ⁅A.subgroupOf M, L₂.subgroupOf M⁆ ≤
      (CFSG.pPrimeCore p ↥(L₂.subgroupOf M)).map (L₂.subgroupOf M).subtype :=
    (Subgroup.commutator_mono hAM₁ le_rfl).trans (hK.2.2.1.trans inf_le_right)
  have hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥(L₂.subgroupOf M)) :=
    not_three_dvd_card_pPrimeCore_of_isPComponent h.prime hSch h.comp₂ h.pRank_three_subgroupOf₂
  have hnotM := CFSG.GroupTheory.not_isPSolvable_inf_centralizer_of_isPComponent h.prime h.comp₂
    Nat.prime_three hB hBK hcomm hcop
  exact h.six A hAM hA3 (h.two_le_pRank_inf_centralizer_of_le₁ hA hA3)
    (not_isPSolvable_inf_centralizer_of_subgroupOf h.le₂ hAM hnotM)

theorem normalizer_le_of_le₂ (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {A : Subgroup G}
    (hA : A ≤ L₂) (hA3 : Nat.card A = 3) :
    Subgroup.normalizer (A : Set G) ≤ M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hAM : A ≤ M := hA.trans h.le₂
  have hK :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation
      p h.prime (L₁.subgroupOf M) (L₂.subgroupOf M) h.comp₁ h.comp₂).2 h.subgroupOf_ne
  have hAM₂ : A.subgroupOf M ≤ L₂.subgroupOf M := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hA (Subgroup.mem_subgroupOf.mp hx))
  have hcardM : Nat.card (A.subgroupOf M) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv).trans hA3
  have hB : IsPGroup 3 (A.subgroupOf M) :=
    IsPGroup.of_card (n := 1) (by rw [hcardM]; norm_num)
  have hBK : A.subgroupOf M ≤ Subgroup.normalizer (L₁.subgroupOf M : Set ↥M) :=
    hAM₂.trans hK.1
  have hcomm : ⁅A.subgroupOf M, L₁.subgroupOf M⁆ ≤
      (CFSG.pPrimeCore p ↥(L₁.subgroupOf M)).map (L₁.subgroupOf M).subtype := by
    refine (Subgroup.commutator_mono hAM₂ le_rfl).trans ?_
    rw [Subgroup.commutator_comm (L₂.subgroupOf M) (L₁.subgroupOf M)]
    exact hK.2.2.1.trans inf_le_left
  have hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥(L₁.subgroupOf M)) :=
    not_three_dvd_card_pPrimeCore_of_isPComponent h.prime hSch h.comp₁ h.pRank_three_subgroupOf₁
  have hnotM := CFSG.GroupTheory.not_isPSolvable_inf_centralizer_of_isPComponent h.prime h.comp₁
    Nat.prime_three hB hBK hcomm hcop
  exact h.six A hAM hA3 (h.two_le_pRank_inf_centralizer_of_le₂ hSch hA hA3)
    (not_isPSolvable_inf_centralizer_of_subgroupOf h.le₁ hAM hnotM)

theorem normalizer_le_of_commutator_le (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {A₀ : Subgroup G}
    (hA₀ : A₀ ≤ M) (hA3 : Nat.card A₀ = 3)
    (h₁ : ⁅A₀, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype)
    (h₂ : ⁅A₀, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype) :
    Subgroup.normalizer (A₀ : Set G) ≤ M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hcardM : Nat.card (A₀.subgroupOf M) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀).toEquiv).trans hA3
  have hB : IsPGroup 3 (A₀.subgroupOf M) :=
    IsPGroup.of_card (n := 1) (by rw [hcardM]; norm_num)
  have hN₁ : A₀.subgroupOf M ≤ Subgroup.normalizer (L₁.subgroupOf M : Set ↥M) := by
    rw [← Subgroup.subgroupOf_normalizer_eq h.le₁]
    intro x _
    exact Subgroup.mem_subgroupOf.mpr
      ((Subgroup.normal_subgroupOf_iff_le_normalizer h.le₁).mp h.normal₁ x.2)
  have hnotM := CFSG.GroupTheory.not_isPSolvable_inf_centralizer_of_isPComponent h.prime h.comp₁
    Nat.prime_three hB hN₁ (commutator_subgroupOf_le_pPrimeCore hA₀ h.le₁ h₁)
    (not_three_dvd_card_pPrimeCore_of_isPComponent h.prime hSch h.comp₁
      h.pRank_three_subgroupOf₁)
  exact h.six A₀ hA₀ hA3 (two_le_pRank_inf_centralizer_of_commutator_le h hSch hA₀ hA3 h₁ h₂)
    (not_isPSolvable_inf_centralizer_of_subgroupOf h.le₁ hA₀ hnotM)

end P812Hyp

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
