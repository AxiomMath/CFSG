module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Seg27Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Seg27Center
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Decomp

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem gamma_seg27_core (h27 : Segev27) {G : Type} [Group G] [Finite G] {b y c₀ c₁ : G}
    {L L' : Subgroup G} (hM : IsShapeTwoTwoTimesA8 ↥(Gxy b y)) (hby : b * y = y * b)
    (hb1 : b ≠ 1) (hy1 : y ≠ 1) (hby1 : b * y ≠ 1) (hne : b ≠ y)
    (h₀ : (b * c₀) ^ 3 = y) (h₀s : IsShapeZ2TimesSym 5 ↥(Gxy b c₀))
    (h₀d : derivedOf (Gxy b c₀) = Gxy b c₀ ⊓ derivedOf (Gxy b y))
    (h₀a : IsShapeA5 ↥(derivedOf (Gxy b c₀)))
    (h₀o : ∀ φ : alternatingGroup (Fin 8) ≃* ↥(derivedOf (Gxy b y)),
      HasSixOrbit φ (derivedOf (Gxy b c₀)))
    (h₀z : Gxy b c₀ ⊓ Subgroup.closure {b, y} = Subgroup.zpowers y)
    (h₁ : (y * c₁) ^ 3 = b) (h₁s : IsShapeZ2TimesSym 5 ↥(Gxy y c₁))
    (h₁d : derivedOf (Gxy y c₁) = Gxy y c₁ ⊓ derivedOf (Gxy b y))
    (h₁a : IsShapeA5 ↥(derivedOf (Gxy y c₁)))
    (h₁o : ∀ φ : alternatingGroup (Fin 8) ≃* ↥(derivedOf (Gxy b y)),
      HasSixOrbit φ (derivedOf (Gxy y c₁)))
    (h₁z : Gxy y c₁ ⊓ Subgroup.closure {b, y} = Subgroup.zpowers b)
    (hL : L ≤ Gxy b y) (hLs : IsShapeZ2TimesSym 6 ↥L)
    (hL' : L' ≤ Gxy b y) (hL's : IsShapeZ2TimesSym 6 ↥L') :
    (∃ s ∈ Gxy b c₀ ⊓ Gxy y c₁, orderOf s = 2) ∧ (∃ s ∈ Gxy b c₀ ⊓ L, orderOf s = 2) ∧
      (∃ s ∈ Gxy y c₁ ⊓ L, orderOf s = 2) ∧ (∃ s ∈ L ⊓ L', orderOf s = 2) := by
  have hyM : y ∈ Gxy b y := by
    rw [mem_Gxy]
    exact ⟨mem_Gx.mpr hby, self_mem_Gx y⟩
  have hbM : b ∈ Gxy b y := by
    rw [mem_Gxy]
    exact ⟨self_mem_Gx b, mem_Gx.mpr hby.symm⟩
  have hbc : ∀ g ∈ Gxy b y, b * g = g * b :=
    fun g hg => mem_Gx.mp (mem_Gxy.mp hg).1
  have hyc : ∀ g ∈ Gxy b y, y * g = g * y :=
    fun g hg => mem_Gx.mp (mem_Gxy.mp hg).2
  have hZ := gamma_center_eq (M := Gxy b y) hM hbM hyM hbc hyc hb1 hy1 hby1 hne
  have hle₀ : Gxy b c₀ ≤ Gxy b y := by
    intro g hg
    rw [mem_Gxy] at hg ⊢
    refine ⟨hg.1, mem_Gx.mpr ?_⟩
    have hb : Commute g b := (mem_Gx.mp hg.1).symm
    have hc : Commute g c₀ := (mem_Gx.mp hg.2).symm
    have hcube : Commute g y := by
      simpa [h₀] using (hb.mul_right hc).pow_right 3
    exact hcube.eq.symm
  have hle₁ : Gxy y c₁ ≤ Gxy b y := by
    intro g hg
    rw [mem_Gxy] at hg ⊢
    refine ⟨mem_Gx.mpr ?_, hg.1⟩
    have hy : Commute g y := (mem_Gx.mp hg.1).symm
    have hc : Commute g c₁ := (mem_Gx.mp hg.2).symm
    have hcube : Commute g b := by
      simpa [h₁] using (hy.mul_right hc).pow_right 3
    exact hcube.eq.symm
  obtain ⟨φG⟩ := nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8 (H := Gxy b y) hM
  let φ : alternatingGroup (Fin 8) ≃* ↥(_root_.commutator ↥(Gxy b y)) :=
    φG.trans (gammaCommEquiv (Gxy b y)).symm
  let K : Fin 4 → Subgroup ↥(Gxy b y) :=
    ![(Gxy b c₀).subgroupOf (Gxy b y), (Gxy y c₁).subgroupOf (Gxy b y),
      L.subgroupOf (Gxy b y), L'.subgroupOf (Gxy b y)]
  have hK0eq : K 0 = (Gxy b c₀).subgroupOf (Gxy b y) := by simp [K]
  have hK1eq : K 1 = (Gxy y c₁).subgroupOf (Gxy b y) := by simp [K]
  have hK2eq : K 2 = L.subgroupOf (Gxy b y) := by simp [K]
  have hK3eq : K 3 = L'.subgroupOf (Gxy b y) := by simp [K]
  have hKsmall : ∀ i : Fin 4, i.val < 2 →
      IsShapeZ2TimesSym 5 ↥(K i) ∧
        derivedOf (K i) = K i ⊓ _root_.commutator ↥(Gxy b y) ∧
        IsShapeA5 ↥(derivedOf (K i)) ∧ HasSixOrbit φ (derivedOf (K i)) := by
    intro i hi
    have hlt : i.val = 0 ∨ i.val = 1 := by omega
    rcases hlt with h | h
    · have hi0 : i = 0 := Fin.ext h
      rw [hi0, hK0eq]
      exact gamma_seg27_typeS5 (M := Gxy b y) hle₀ h₀s h₀d h₀a h₀o φ
    · have hi1 : i = 1 := Fin.ext h
      rw [hi1, hK1eq]
      exact gamma_seg27_typeS5 (M := Gxy b y) hle₁ h₁s h₁d h₁a h₁o φ
  have hK0center : K 0 ⊓ Subgroup.center ↥(Gxy b y) = Subgroup.zpowers ⟨y, hyM⟩ := by
    rw [hK0eq]
    exact gamma_inf_center_eq (M := Gxy b y) (L := Gxy b c₀) (w := y)
      hbM hyM hyM (Or.inl rfl) hZ h₀z
  have hK1center : K 1 ⊓ Subgroup.center ↥(Gxy b y) = Subgroup.zpowers ⟨b, hbM⟩ := by
    rw [hK1eq]
    exact gamma_inf_center_eq (M := Gxy b y) (L := Gxy y c₁) (w := b)
      hbM hyM hbM (Or.inr rfl) hZ h₁z
  have hKbig : ∀ i : Fin 4, 2 ≤ i.val → IsShapeZ2TimesSym 6 ↥(K i) := by
    intro i hi
    have hlt4 : i.val < 4 := i.isLt
    have hge : i.val = 2 ∨ i.val = 3 := by omega
    rcases hge with h | h
    · have hi2 : i = 2 := Fin.ext h
      rw [hi2, hK2eq]
      exact gamma_isShapeZ2TimesSym_subgroupOf (M := Gxy b y) hL hLs
    · have hi3 : i = 3 := Fin.ext h
      rw [hi3, hK3eq]
      exact gamma_isShapeZ2TimesSym_subgroupOf (M := Gxy b y) hL' hL's
  have hmain : ∀ i j : Fin 4, i ≠ j → ∃ t ∈ K i ⊓ K j, orderOf t = 2 :=
    h27 ↥(Gxy b y) ⟨y, hyM⟩ ⟨b, hbM⟩ hM hZ φ K hKsmall hK0center hK1center hKbig
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨t, ht, hto⟩ := hmain (0 : Fin 4) (1 : Fin 4) (by decide)
    rw [hK0eq, hK1eq, Subgroup.mem_inf] at ht
    exact ⟨(t : G),
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp ht.1, Subgroup.mem_subgroupOf.mp ht.2⟩,
      (Subgroup.orderOf_coe t).trans hto⟩
  · obtain ⟨t, ht, hto⟩ := hmain (0 : Fin 4) (2 : Fin 4) (by decide)
    rw [hK0eq, hK2eq, Subgroup.mem_inf] at ht
    exact ⟨(t : G),
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp ht.1, Subgroup.mem_subgroupOf.mp ht.2⟩,
      (Subgroup.orderOf_coe t).trans hto⟩
  · obtain ⟨t, ht, hto⟩ := hmain (1 : Fin 4) (2 : Fin 4) (by decide)
    rw [hK1eq, hK2eq, Subgroup.mem_inf] at ht
    exact ⟨(t : G),
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp ht.1, Subgroup.mem_subgroupOf.mp ht.2⟩,
      (Subgroup.orderOf_coe t).trans hto⟩
  · obtain ⟨t, ht, hto⟩ := hmain (2 : Fin 4) (3 : Fin 4) (by decide)
    rw [hK2eq, hK3eq, Subgroup.mem_inf] at ht
    exact ⟨(t : G),
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp ht.1, Subgroup.mem_subgroupOf.mp ht.2⟩,
      (Subgroup.orderOf_coe t).trans hto⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
