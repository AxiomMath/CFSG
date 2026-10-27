module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Four
import CFSG.GroupTheory.CentralizerSup
import CFSG.GroupTheory.RankOneNormalCentralizer
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
import CFSG.LocalAnalysis.UniquenessCase.UC6K35cRed

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {L₁ L₂ : Subgroup G}

namespace P812Hyp

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {L₁ L₂ : Subgroup G}

theorem dvd_card_inf_centralizer_sup (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {A₁ A₂ : Subgroup G}
    (h₁ : A₁ ≤ L₁) (h₂ : A₂ ≤ L₂) (hA₁ : Nat.card A₁ = 3) (hA₂ : Nat.card A₂ = 3)
    (hc : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x) :
    p ∣ Nat.card ↥(M ⊓ Subgroup.centralizer ((A₁ ⊔ A₂ : Subgroup G) : Set G)) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  let C₁ : Subgroup G :=
    M ⊓ Subgroup.centralizer (A₁ : Set G) ⊓ Subgroup.normalizer (L₂ : Set G)
  let D : Subgroup G := L₂ ⊓ Subgroup.centralizer (A₁ : Set G)
  have hDC : D ≤ C₁ := by
    intro x hx
    exact ⟨⟨h.le₂ hx.1, hx.2⟩, Subgroup.le_normalizer hx.1⟩
  have hC₁N : C₁ ≤ Subgroup.normalizer (D : Set G) :=
    CFSG.GroupTheory.FT63ChII.le_normalizer_inf_of_le (fun x hx => hx.2)
      (fun x hx => Subgroup.le_normalizer hx.1.2)
  have hA₂D : A₂ ≤ D := by
    intro x hx
    exact ⟨h₂ hx, Subgroup.mem_centralizer_iff.mpr fun y hy => hc y hy x hx⟩
  have hDcard : CFSG.Open.pRank 3 D ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) (inf_le_left : D ≤ L₂)).trans
      (le_of_eq h.rank_three₂)
  have hDrank : CFSG.Open.pRank p D ≤ 1 :=
    (CFSG.SectionRank.pRank_mono h.prime.one_lt (inf_le_left : D ≤ L₂)).trans
      (le_of_eq h.rank_p₂)
  have hC₁rank : 2 ≤ CFSG.Open.pRank p C₁ := by
    have hle : CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (A₁ : Set G)) ≤
        CFSG.Open.pRank p C₁ := by
      obtain ⟨E, hE, hEea, hEcard⟩ :=
        CFSG.SectionRank.exists_pRank h.prime.one_lt (M ⊓ Subgroup.centralizer (A₁ : Set G))
      have hE₁ : E ≤ C₁ := by
        intro x hx
        exact ⟨hE hx, h.mem_normalizer_two_of_odd hSch (hE hx).1
          (Odd.of_dvd_nat (h.prime.odd_of_ne_two h.ne_two)
            (orderOf_dvd_of_pow_eq_one (hEea.2 x hx)))⟩
      exact CFSG.SectionRank.le_pRank h.prime.one_lt hE₁ hEea hEcard
    exact (h.two_le_pRank_inf_centralizer_of_le₁ h₁ hA₁).trans hle
  have hlt : CFSG.Open.pRank p D < CFSG.Open.pRank p C₁ := by omega
  have hdvd : p ∣ D.relIndex C₁ :=
    CFSG.GroupTheory.dvd_relIndex_of_pRank_lt h.prime hDC hlt
  obtain ⟨y, hy, hyord⟩ := CFSG.GroupTheory.exists_orderOf_eq_mem_inf_centralizer h.prime
    h.ne_two hDC hC₁N hA₂D hA₂ hDcard hdvd
  have hyC : y ∈ M ⊓ Subgroup.centralizer ((A₁ ⊔ A₂ : Subgroup G) : Set G) := by
    refine ⟨hy.1.1.1, ?_⟩
    rw [CFSG.centralizer_sup_eq]
    exact ⟨hy.1.1.2, hy.2⟩
  exact hyord ▸ Subgroup.orderOf_dvd_natCard _ hyC

theorem normalizer_sup_le (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {A₁ A₂ : Subgroup G}
    (h₁ : A₁ ≤ L₁) (h₂ : A₂ ≤ L₂) (hA₁ : Nat.card A₁ = 3) (hA₂ : Nat.card A₂ = 3)
    (hc : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x) :
    Subgroup.normalizer ((A₁ ⊔ A₂ : Subgroup G) : Set G) ≤ M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hC : Subgroup.centralizer ((A₁ ⊔ A₂ : Subgroup G) : Set G) ≤ M := by
    rw [CFSG.centralizer_sup_eq]
    exact (inf_le_left.trans (Subgroup.centralizer_le_normalizer (A₁ : Set G))).trans
      (h.normalizer_le_of_le₁ hSch h₁ hA₁)
  have hdvd : p ∣ Nat.card (Subgroup.centralizer ((A₁ ⊔ A₂ : Subgroup G) : Set G)) := by
    have hd := h.dvd_card_inf_centralizer_sup hSch h₁ h₂ hA₁ hA₂ hc
    rwa [inf_eq_right.mpr hC] at hd
  exact CFSG.RankThree.PartOne.IsStronglyPEmbedded.normalizer_le_of_centralizer_le
    h.strong hC hdvd

private theorem not_isPSolvable_inf_centralizer_sup_of_le₁ (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {A₀ A : Subgroup G}
    (hA₀ : A₀ ≤ M) (hA3 : Nat.card A₀ = 3)
    (h₂ : ⁅A₀, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype)
    (hA₁ : A ≤ L₁) (hA3' : Nat.card A = 3)
    (hc : ∀ x ∈ A₀, ∀ y ∈ A, x * y = y * x) :
    ¬ CFSG.HallHigman.IsPSolvable p
      ↥(L₂.subgroupOf M ⊓ Subgroup.centralizer
        ((A₀.subgroupOf M ⊔ A.subgroupOf M : Subgroup ↥M) : Set ↥M)) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAM : A ≤ M := hA₁.trans h.le₁
  have hK :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation
      p h.prime (L₁.subgroupOf M) (L₂.subgroupOf M) h.comp₁ h.comp₂).2 h.subgroupOf_ne
  have hcM : ∀ x ∈ A₀.subgroupOf M, ∀ y ∈ A.subgroupOf M, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext
      (hc (x : G) (Subgroup.mem_subgroupOf.mp hx) (y : G) (Subgroup.mem_subgroupOf.mp hy))
  have hcard₀ : Nat.card (A₀.subgroupOf M) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀).toEquiv).trans hA3
  have hcardA : Nat.card (A.subgroupOf M) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv).trans hA3'
  have hB₀ : IsPGroup 3 (A₀.subgroupOf M) :=
    IsPGroup.of_card (n := 1) (by rw [hcard₀]; norm_num)
  have hB : IsPGroup 3 (A.subgroupOf M) :=
    IsPGroup.of_card (n := 1) (by rw [hcardA]; norm_num)
  have hA₀N₂ : A₀.subgroupOf M ≤ Subgroup.normalizer (L₂.subgroupOf M : Set ↥M) := by
    rw [← Subgroup.subgroupOf_normalizer_eq h.le₂]
    intro x hx
    have hxA : (x : G) ∈ A₀ := Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_subgroupOf.mpr
      (h.le_normalizer_two_of_card_three hSch hA₀ hA3 hxA)
  have hAM₁ : A.subgroupOf M ≤ L₁.subgroupOf M := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hA₁ (Subgroup.mem_subgroupOf.mp hx))
  have hcomm : ⁅A.subgroupOf M, L₂.subgroupOf M⁆ ≤
      (CFSG.pPrimeCore p ↥(L₂.subgroupOf M)).map (L₂.subgroupOf M).subtype :=
    (Subgroup.commutator_mono hAM₁ le_rfl).trans (hK.2.2.1.trans inf_le_right)
  exact CFSG.GroupTheory.not_isPSolvable_inf_centralizer_sup h.prime h.comp₂ Nat.prime_three
    Nat.prime_three hB₀ hB hcM hA₀N₂ (hAM₁.trans hK.2.1)
    (commutator_subgroupOf_le_pPrimeCore hA₀ h.le₂ h₂) hcomm
    (not_three_dvd_card_pPrimeCore_of_isPComponent h.prime hSch h.comp₂
      h.pRank_three_subgroupOf₂)
    (not_three_dvd_card_pPrimeCore_of_isPComponent h.prime hSch h.comp₂
      h.pRank_three_subgroupOf₂)

private theorem not_isPSolvable_inf_centralizer_sup_of_le₂ (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {A₀ A : Subgroup G}
    (hA₀ : A₀ ≤ M) (hA3 : Nat.card A₀ = 3)
    (h₁ : ⁅A₀, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype)
    (hA₂ : A ≤ L₂) (hA3' : Nat.card A = 3)
    (hc : ∀ x ∈ A₀, ∀ y ∈ A, x * y = y * x) :
    ¬ CFSG.HallHigman.IsPSolvable p
      ↥(L₁.subgroupOf M ⊓ Subgroup.centralizer
        ((A₀.subgroupOf M ⊔ A.subgroupOf M : Subgroup ↥M) : Set ↥M)) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAM : A ≤ M := hA₂.trans h.le₂
  have hK :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation
      p h.prime (L₁.subgroupOf M) (L₂.subgroupOf M) h.comp₁ h.comp₂).2 h.subgroupOf_ne
  have hcM : ∀ x ∈ A₀.subgroupOf M, ∀ y ∈ A.subgroupOf M, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext
      (hc (x : G) (Subgroup.mem_subgroupOf.mp hx) (y : G) (Subgroup.mem_subgroupOf.mp hy))
  have hcard₀ : Nat.card (A₀.subgroupOf M) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀).toEquiv).trans hA3
  have hcardA : Nat.card (A.subgroupOf M) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv).trans hA3'
  have hB₀ : IsPGroup 3 (A₀.subgroupOf M) :=
    IsPGroup.of_card (n := 1) (by rw [hcard₀]; norm_num)
  have hB : IsPGroup 3 (A.subgroupOf M) :=
    IsPGroup.of_card (n := 1) (by rw [hcardA]; norm_num)
  have hA₀N₁ : A₀.subgroupOf M ≤ Subgroup.normalizer (L₁.subgroupOf M : Set ↥M) := by
    rw [← Subgroup.subgroupOf_normalizer_eq h.le₁]
    intro x _
    exact Subgroup.mem_subgroupOf.mpr
      ((Subgroup.normal_subgroupOf_iff_le_normalizer h.le₁).mp h.normal₁ x.2)
  have hAM₂ : A.subgroupOf M ≤ L₂.subgroupOf M := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hA₂ (Subgroup.mem_subgroupOf.mp hx))
  have hcomm : ⁅A.subgroupOf M, L₁.subgroupOf M⁆ ≤
      (CFSG.pPrimeCore p ↥(L₁.subgroupOf M)).map (L₁.subgroupOf M).subtype := by
    refine (Subgroup.commutator_mono hAM₂ le_rfl).trans ?_
    rw [Subgroup.commutator_comm (L₂.subgroupOf M) (L₁.subgroupOf M)]
    exact hK.2.2.1.trans inf_le_left
  exact CFSG.GroupTheory.not_isPSolvable_inf_centralizer_sup h.prime h.comp₁ Nat.prime_three
    Nat.prime_three hB₀ hB hcM hA₀N₁ (hAM₂.trans hK.1)
    (commutator_subgroupOf_le_pPrimeCore hA₀ h.le₁ h₁) hcomm
    (not_three_dvd_card_pPrimeCore_of_isPComponent h.prime hSch h.comp₁
      h.pRank_three_subgroupOf₁)
    (not_three_dvd_card_pPrimeCore_of_isPComponent h.prime hSch h.comp₁
      h.pRank_three_subgroupOf₁)

private theorem not_isPSolvable_inf_centralizer_sup_of_commutator_le (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {A₀ A : Subgroup G}
    (hA₀ : A₀ ≤ M) (hA3 : Nat.card A₀ = 3)
    (h₁ : ⁅A₀, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype)
    (h₂ : ⁅A₀, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype)
    (hA : A ≤ L₁ ∨ A ≤ L₂) (hA3' : Nat.card A = 3)
    (hc : ∀ x ∈ A₀, ∀ y ∈ A, x * y = y * x) :
    ¬ CFSG.HallHigman.IsPSolvable p
      ↥(M ⊓ Subgroup.centralizer ((A₀ ⊔ A : Subgroup G) : Set G)) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hAM : A ≤ M := hA.elim (fun hA₁ => hA₁.trans h.le₁) (fun hA₂ => hA₂.trans h.le₂)
  have hsub : ((A₀ ⊔ A).subgroupOf M : Subgroup M) = A₀.subgroupOf M ⊔ A.subgroupOf M :=
    Subgroup.subgroupOf_sup hA₀ hAM
  rcases hA with hA₁ | hA₂
  · exact not_isPSolvable_inf_centralizer_of_subgroupOf h.le₂ (sup_le hA₀ hAM)
      (by rw [hsub]
          exact not_isPSolvable_inf_centralizer_sup_of_le₁ h hSch hA₀ hA3 h₂ hA₁ hA3' hc)
  · exact not_isPSolvable_inf_centralizer_of_subgroupOf h.le₁ (sup_le hA₀ hAM)
      (by rw [hsub]
          exact not_isPSolvable_inf_centralizer_sup_of_le₂ h hSch hA₀ hA3 h₁ hA₂ hA3' hc)

theorem dvd_card_inf_centralizer_sup_of_commutator_le (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M) {A₀ A : Subgroup G}
    (hA₀ : A₀ ≤ M) (hA3 : Nat.card A₀ = 3)
    (h₁ : ⁅A₀, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype)
    (h₂ : ⁅A₀, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype)
    (hA : A ≤ L₁ ∨ A ≤ L₂) (hA3' : Nat.card A = 3)
    (hc : ∀ x ∈ A₀, ∀ y ∈ A, x * y = y * x) :
    p ∣ Nat.card ↥(M ⊓ Subgroup.centralizer ((A₀ ⊔ A : Subgroup G) : Set G)) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  by_contra hnd
  exact not_isPSolvable_inf_centralizer_sup_of_commutator_le h hSch hA₀ hA3 h₁ h₂ hA hA3' hc
    (CFSG.LocalAnalysis.UniquenessCase.UCK.isPSolvable_of_not_dvd_card hnd)

end P812Hyp

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
