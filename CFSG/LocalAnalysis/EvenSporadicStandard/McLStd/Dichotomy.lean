module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.I32Final
public import CFSG.LocalAnalysis.ComponentClassification.TBLitComponents
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.GH74.GLS.Classes
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer

public section

namespace CFSG.EvenSporadicStandard.McLStd

open Subgroup CFSG CFSG.GH74.GLS CFSG.QuasithinUnique.Id2519 CFSG.QuasithinUnique.I32

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem isTwoComponentIn_centralizer_inf (h : StdHyp G L) {t u : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) {n : ℕ}
    (hB : IsDoubleCoverOfAlt ↥(centralizer ({u} : Set G) ⊓ L) n) :
    IsTwoComponentIn (centralizer ({u} : Set G) ⊓ L)
      (centralizer ({u} : Set G) ⊓ centralizer ({t} : Set G)) := by
  set B : Subgroup G := centralizer ({u} : Set G) ⊓ L with hBdef
  set X : Subgroup G := centralizer ({u} : Set G) ⊓ centralizer ({t} : Set G) with hXdef
  have hLle : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht l hl)
  have hBX : B ≤ X := fun b hb => ⟨hb.1, hLle hb.2⟩
  have hnorm : (B.subgroupOf X).Normal := by
    refine ⟨fun b hb g => ?_⟩
    have hb' : (b : G) ∈ B := hb
    have hgt : (g : G) ∈ centralizer ({t} : Set G) := g.2.2
    have hgL : (g : G) ∈ normalizer (L : Set G) := h.centralizer_le_normalizer ht ht2 hgt
    have hgu : (g : G) ∈ centralizer ({u} : Set G) := g.2.1
    show (g : G) * (b : G) * (g : G)⁻¹ ∈ B
    refine ⟨?_, (mem_normalizer_iff.1 hgL (b : G)).1 hb'.2⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgu hb'.1) (Subgroup.inv_mem _ hgu)
  have hq : IsQuasisimple ↥(B.subgroupOf X) :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBX).symm hB.1
  have hcomp : IsComponent (B.subgroupOf X) := ⟨hq, hnorm.isSubnormal⟩
  have hP : IsPComponent 2 (B.subgroupOf X) :=
    LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hcomp
  exact (isTwoComponentIn_iff hBX).2
    ((ComponentClassification.CatalogueBAlternating.pComponent_two_iff _).1 hP)

theorem layer_dichotomy (h : StdHyp G L) {t u : G} (ht : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) (hu : u ∈ L) (hu2 : orderOf u = 2) {n : ℕ}
    (hB : IsDoubleCoverOfAlt ↥(centralizer ({u} : Set G) ⊓ L) n) :
    (IsTwoComponentIn (⨆ g ∈ oddLayer (centralizer ({u} : Set G)),
        CFSG.conjugate (centralizer ({u} : Set G) ⊓ L) g) (centralizer ({u} : Set G)) ∧
      t ∈ normalizer ((⨆ g ∈ oddLayer (centralizer ({u} : Set G)),
        CFSG.conjugate (centralizer ({u} : Set G) ⊓ L) g : Subgroup G) : Set G)) ∨
    ∃ J : Subgroup G, IsTwoComponentIn J (centralizer ({u} : Set G)) ∧
      J ≠ CFSG.conjugate J t ∧
      (⨆ g ∈ oddLayer (centralizer ({u} : Set G)),
        CFSG.conjugate (centralizer ({u} : Set G) ⊓ L) g) = J ⊔ CFSG.conjugate J t ∧
      OddTwoIso J (centralizer ({u} : Set G) ⊓ L) := by
  have := h.simple
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    exact absurd hu2 (by decide)
  have hucen : u ∉ center G := by
    intro hz
    have hcen : center G = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h' | h'
      · exact h'
      · obtain ⟨a, b, hab⟩ := h.nonabelian
        exact absurd (mem_center_iff.1 (h' ▸ mem_top b) a) hab
    rw [hcen, mem_bot] at hz
    exact hu1 hz
  have hK : SectionRank.IsKGroupCat ↥(centralizer ({u} : Set G)) :=
    ComponentClassification.TBLit.isKGroupCat_centralizer h.kProper hucen
  have htH : t ∈ centralizer ({u} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht u hu).symm
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    exact absurd ht2 (by decide)
  have ht2' : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  exact lemmaI32 G _ hK t htH ht1 ht2' _ (isTwoComponentIn_centralizer_inf h ht ht2 hB)

end CFSG.EvenSporadicStandard.McLStd
