module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G] {a z : G}

theorem gamma_seg27_data (H : GammaHyps a z) {b y c₀ : G} (hb : IsConj a b)
    (hc₀ : c₀ ∈ orb6A a b) (h3 : (b * c₀) ^ 3 = y) :
    IsShapeZ2TimesSym 5 ↥(Gxy b c₀) ∧
      derivedOf (Gxy b c₀) = Gxy b c₀ ⊓ derivedOf (Gxy b y) ∧
      IsShapeA5 ↥(derivedOf (Gxy b c₀)) ∧
      (∀ φ : alternatingGroup (Fin 8) ≃* ↥(derivedOf (Gxy b y)),
        HasSixOrbit φ (derivedOf (Gxy b c₀))) ∧
      Gxy b c₀ ⊓ Subgroup.closure {b, y} = Subgroup.zpowers y := by
  have hc₀' : c₀ ∈ orb6A b b := (gamma_orb6A_eq hb b).symm ▸ hc₀
  subst h3
  have hSix := (H.hLines b z hb (IsConj.refl z)).six_A c₀ hc₀'
  have hShape := (H.hT5 b z hb (IsConj.refl z)).shape_6A c₀ hc₀'
  exact ⟨hShape, hSix.1, hSix.2.1, hSix.2.2.1, hSix.2.2.2⟩

theorem gamma_seg27_fill (H : GammaHyps a z) {b y : G} (hb : IsConj a b) (hy : y ∈ orb2A a b) :
    (∃ c₀ ∈ orb6A a b, (b * c₀) ^ 3 = y) ∧ (∃ c₁ ∈ orb6A a y, (y * c₁) ^ 3 = b) ∧
      ∃ L : Subgroup G, L ≤ Gxy b y ∧ IsShapeZ2TimesSym 6 ↥L := by
  have hy' : y ∈ orb2A b b := (gamma_orb2A_eq hb b).symm ▸ hy
  have hT : TableIVFacts b z := H.hT4 b z hb (IsConj.refl z)
  have hF5b : IsF5Type b z := isF5Type_of_isConj H.h hb (IsConj.refl z)
  have hyb' : IsConj b y := (gamma_isConj_iff hb y).2 hy.1
  obtain ⟨c₀, hc₀set⟩ := ((hT.partition y hy').orbit 5).nonempty
  have hc₀base : c₀ ∈ sBase b y := hc₀set.1
  obtain ⟨hord₀, hcube₀⟩ := perp_orderOf_row_five hF5b hyb' hc₀set
  have hc₀mem : c₀ ∈ orb6A a b :=
    ⟨hb.trans hc₀base.1, hord₀, by rw [hcube₀]; exact hy.1⟩
  have hb' : b ∈ orb2A a y := H.orb2A_symm hb hy
  have hb'' : b ∈ orb2A y y := (gamma_orb2A_eq hy.1 y).symm ▸ hb'
  have hT' : TableIVFacts y z := H.hT4 y z hy.1 (IsConj.refl z)
  have hF5y : IsF5Type y z := isF5Type_of_isConj H.h hy.1 (IsConj.refl z)
  have hyb'' : IsConj y b := hy.1.symm.trans hb
  obtain ⟨c₁, hc₁set⟩ := ((hT'.partition b hb'').orbit 5).nonempty
  have hc₁base : c₁ ∈ sBase y b := hc₁set.1
  obtain ⟨hord₁, hcube₁⟩ := perp_orderOf_row_five hF5y hyb'' hc₁set
  have hc₁mem : c₁ ∈ orb6A a y :=
    ⟨hy.1.trans hc₁base.1, hord₁, by rw [hcube₁]; exact hb⟩
  obtain ⟨c₂, hc₂set⟩ := ((hT.partition y hy').orbit 2).nonempty
  refine ⟨⟨c₀, hc₀mem, hcube₀⟩, ⟨c₁, hc₁mem, hcube₁⟩, ?_⟩
  refine ⟨Gxyz b y c₂, ?_, hT.shape_4B y hy' c₂ hc₂set⟩
  rw [Gxyz_eq_inf]
  exact inf_le_left

end CFSG.EvenSporadicStandard.HNRecog.Section3
