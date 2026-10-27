module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Seg27Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Seg27Data

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G] {a z : G}

private theorem gamma_seg27_Gxy_comm (x y : G) : Gxy x y = Gxy y x := by
  rw [Gxy_eq_inf, Gxy_eq_inf, inf_comm]

theorem gamma_seg27_all (H : GammaHyps a z) {b y : G} (hb : IsConj a b) (hy : y ∈ orb2A a b)
    {c₀ c₁ : G} (hc₀ : c₀ ∈ orb6A a b) (h₀ : (b * c₀) ^ 3 = y) (hc₁ : c₁ ∈ orb6A a y)
    (h₁ : (y * c₁) ^ 3 = b) {L L' : Subgroup G} (hL : L ≤ Gxy b y)
    (hLs : IsShapeZ2TimesSym 6 ↥L) (hL' : L' ≤ Gxy b y) (hL's : IsShapeZ2TimesSym 6 ↥L') :
    (∃ s ∈ Gxy b c₀ ⊓ Gxy y c₁, orderOf s = 2) ∧ (∃ s ∈ Gxy b c₀ ⊓ L, orderOf s = 2) ∧
      (∃ s ∈ Gxy y c₁ ⊓ L, orderOf s = 2) ∧ (∃ s ∈ L ⊓ L', orderOf s = 2) := by
  have hy' : y ∈ orb2A b b := (gamma_orb2A_eq hb b).symm ▸ hy
  have hM : IsShapeTwoTwoTimesA8 ↥(Gxy b y) :=
    (H.hT5 b z hb (IsConj.refl z)).shape_2A y hy'
  have hby : b * y = y * b := H.comm_of_orb2A hb hy
  have hb1 : b ≠ 1 := H.ne_one_a hb
  have hy1 : y ≠ 1 := H.ne_one_a hy.1
  have hby1 : b * y ≠ 1 := H.ne_one_a hy.2
  have hne : b ≠ y := fun h => H.ne_of_orb2A hb hy h.symm
  obtain ⟨h₀s, h₀d, h₀a, h₀o, h₀z⟩ := gamma_seg27_data H hb hc₀ h₀
  obtain ⟨h₁s, h₁d, h₁a, h₁o, h₁z⟩ := gamma_seg27_data H hy.1 hc₁ h₁
  have hG : Gxy y b = Gxy b y := gamma_seg27_Gxy_comm y b
  rw [hG] at h₁d h₁o
  rw [Set.pair_comm y b] at h₁z
  exact gamma_seg27_core H.h27 hM hby hb1 hy1 hby1 hne h₀ h₀s h₀d h₀a h₀o h₀z
    h₁ h₁s h₁d h₁a h₁o h₁z hL hLs hL' hL's

theorem gamma_seg27_S6_S6 (H : GammaHyps a z) {b y : G} (hb : IsConj a b) (hy : y ∈ orb2A a b)
    {L L' : Subgroup G} (hL : L ≤ Gxy b y) (hLs : IsShapeZ2TimesSym 6 ↥L)
    (hL' : L' ≤ Gxy b y) (hL's : IsShapeZ2TimesSym 6 ↥L') : ∃ s ∈ L ⊓ L', orderOf s = 2 := by
  obtain ⟨⟨c₀, hc₀, h₀⟩, ⟨c₁, hc₁, h₁⟩, _⟩ := gamma_seg27_fill H hb hy
  exact (gamma_seg27_all H hb hy hc₀ h₀ hc₁ h₁ hL hLs hL' hL's).2.2.2

theorem gamma_seg27_S5b_S6 (H : GammaHyps a z) {b y : G} (hb : IsConj a b) (hy : y ∈ orb2A a b)
    {c₀ : G} (hc₀ : c₀ ∈ orb6A a b) (h₀ : (b * c₀) ^ 3 = y) {L : Subgroup G}
    (hL : L ≤ Gxy b y) (hLs : IsShapeZ2TimesSym 6 ↥L) : ∃ s ∈ Gxy b c₀ ⊓ L, orderOf s = 2 := by
  obtain ⟨_, ⟨c₁, hc₁, h₁⟩, _⟩ := gamma_seg27_fill H hb hy
  exact (gamma_seg27_all H hb hy hc₀ h₀ hc₁ h₁ hL hLs hL hLs).2.1

theorem gamma_seg27_S5y_S6 (H : GammaHyps a z) {b y : G} (hb : IsConj a b) (hy : y ∈ orb2A a b)
    {c₁ : G} (hc₁ : c₁ ∈ orb6A a y) (h₁ : (y * c₁) ^ 3 = b) {L : Subgroup G}
    (hL : L ≤ Gxy b y) (hLs : IsShapeZ2TimesSym 6 ↥L) : ∃ s ∈ Gxy y c₁ ⊓ L, orderOf s = 2 := by
  obtain ⟨⟨c₀, hc₀, h₀⟩, _, _⟩ := gamma_seg27_fill H hb hy
  exact (gamma_seg27_all H hb hy hc₀ h₀ hc₁ h₁ hL hLs hL hLs).2.2.1

theorem gamma_seg27_S5_S5 (H : GammaHyps a z) {b y : G} (hb : IsConj a b) (hy : y ∈ orb2A a b)
    {c₀ c₁ : G} (hc₀ : c₀ ∈ orb6A a b) (h₀ : (b * c₀) ^ 3 = y) (hc₁ : c₁ ∈ orb6A a y)
    (h₁ : (y * c₁) ^ 3 = b) : ∃ s ∈ Gxy b c₀ ⊓ Gxy y c₁, orderOf s = 2 := by
  obtain ⟨_, _, ⟨L₀, hL₀, hL₀s⟩⟩ := gamma_seg27_fill H hb hy
  exact (gamma_seg27_all H hb hy hc₀ h₀ hc₁ h₁ hL₀ hL₀s hL₀ hL₀s).1

end CFSG.EvenSporadicStandard.HNRecog.Section3
