module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSec
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aTwoQuot

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace B5a

section Transport

variable {G : Type*} [Group G] [Finite G]

theorem layerIn_subgroupOf {Y G₀ : Subgroup G} (hY : Y ≤ G₀) :
    layerIn (Y.subgroupOf G₀) = (layerIn Y).subgroupOf G₀ := by
  apply map_injective G₀.subtype_injective
  rw [map_subgroupOf_eq_of_le (show layerIn Y ≤ G₀ from (map_subtype_le _).trans hY)]
  have h1 := UnbalancedCorr.map_pLayer_subgroupOf_eq G₀ Y
  rw [inf_of_le_right hY] at h1
  exact h1

theorem oddCoreIn_subgroupOf {Y G₀ : Subgroup G} (hY : Y ≤ G₀) :
    oddCoreIn (Y.subgroupOf G₀) = (oddCoreIn Y).subgroupOf G₀ := by
  apply map_injective G₀.subtype_injective
  rw [map_subgroupOf_eq_of_le (show oddCoreIn Y ≤ G₀ from (map_subtype_le _).trans hY)]
  have h1 := map_oddCoreIn_subgroupOf G₀ Y
  rw [inf_of_le_right hY] at h1
  exact h1

omit [Finite G] in
theorem centralizer_subgroupOf {E G₀ : Subgroup G} (hE : E ≤ G₀) :
    centralizer ((E.subgroupOf G₀ : Subgroup ↥G₀) : Set ↥G₀) =
      (centralizer (E : Set G)).subgroupOf G₀ := by
  ext g
  rw [mem_subgroupOf, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hg e he
    exact congrArg Subtype.val (hg ⟨e, hE he⟩ he)
  · intro hg e he
    exact Subtype.ext (hg e he)

theorem fixedLayer_subgroupOf {L E G₀ : Subgroup G} (hL : L ≤ G₀) (hE : E ≤ G₀) :
    GSLit.fixedLayer (L.subgroupOf G₀) (E.subgroupOf G₀) =
      (GSLit.fixedLayer L E).subgroupOf G₀ := by
  show layerIn (L.subgroupOf G₀ ⊓ centralizer ((E.subgroupOf G₀ : Subgroup ↥G₀) : Set ↥G₀)) =
    (layerIn (L ⊓ centralizer (E : Set G))).subgroupOf G₀
  have h1 : L.subgroupOf G₀ ⊓ (centralizer (E : Set G)).subgroupOf G₀ =
      (L ⊓ centralizer (E : Set G)).subgroupOf G₀ := (comap_inf _ _ _).symm
  rw [centralizer_subgroupOf hE, h1, layerIn_subgroupOf (inf_le_left.trans hL)]

theorem coreActionKernel_subgroupOf {L G₀ : Subgroup G} (hL : L ≤ G₀) :
    coreActionKernel (L.subgroupOf G₀) = (coreActionKernel L).subgroupOf G₀ := by
  ext g
  rw [mem_subgroupOf, mem_coreActionKernel, mem_coreActionKernel]
  have hN : g ∈ normalizer ((L.subgroupOf G₀ : Subgroup ↥G₀) : Set ↥G₀) ↔
      (g : G) ∈ normalizer (L : Set G) := by
    rw [← subgroupOf_normalizer_eq hL, mem_subgroupOf]
  rw [hN]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j hj => ?_⟩
    have h3 : _ ∈ oddCoreIn (L.subgroupOf G₀) := h2 ⟨j, hL hj⟩ hj
    rw [oddCoreIn_subgroupOf hL, mem_subgroupOf] at h3
    have h4 : j⁻¹ * (g : G)⁻¹ * j * g ∈ oddCoreIn L := by simpa only [coe_mul, coe_inv] using h3
    exact h4
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j hj => ?_⟩
    show _ ∈ oddCoreIn (L.subgroupOf G₀)
    rw [oddCoreIn_subgroupOf hL, mem_subgroupOf]
    have h3 : (j : G)⁻¹ * (g : G)⁻¹ * j * g ∈ oddCoreIn L := h2 (j : G) hj
    simpa only [coe_mul, coe_inv] using h3

end Transport

end B5a

namespace Hyp52

variable {X : Type} [Group X] [Finite X] (h : Hyp52 X) (y : X)

theorem secB0_le_G0 : h.secB0 y ≤ h.secG0 y := le_normalizer

theorem subgroupOf_le_centralizer_ker {L : Subgroup X}
    (hLc : L ≤ centralizer (h.secB0 y : Set X)) :
    L.subgroupOf (h.secG0 y) ≤ centralizer ((h.secMk y).ker : Set ↥(h.secG0 y)) := by
  rw [ker_secMk, B5a.centralizer_subgroupOf (h.secB0_le_G0 y)]
  exact fun _ hg => hLc hg

theorem isPGroup_ker_secMk : IsPGroup 2 (h.secMk y).ker := by
  rw [ker_secMk]
  exact (h.isPGroup_secB0 y).comap_subtype

variable {h y}

theorem secImage_isPComponent {L Y : Subgroup X} (hLY : L ≤ Y) (hYG : Y ≤ h.secG0 y)
    (hLc : L ≤ centralizer (h.secB0 y : Set X)) (hL : IsPComponent 2 (L.subgroupOf Y)) :
    IsPComponent 2 ((h.secImage y L).subgroupOf (h.secImage y Y)) := by
  have h1 := (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hYG 2 Nat.prime_two).mpr hL
  exact TwoQuot.isPComponent_map_of_le_centralizer (h.secMk y)
    (fun g hg => hLY hg) (h.subgroupOf_le_centralizer_ker y hLc) h1

theorem secImage_oddCoreIn {L : Subgroup X} (hLG : L ≤ h.secG0 y)
    (hLc : L ≤ centralizer (h.secB0 y : Set X)) :
    h.secImage y (oddCoreIn L) = oddCoreIn (h.secImage y L) := by
  rw [← TwoQuot.map_oddCoreIn_of_le_centralizer (h.secMk y)
    (h.subgroupOf_le_centralizer_ker y hLc), B5a.oddCoreIn_subgroupOf hLG]

theorem secImage_layerIn {L : Subgroup X} (hLG : L ≤ h.secG0 y)
    (hLc : L ≤ centralizer (h.secB0 y : Set X)) :
    h.secImage y (layerIn L) = layerIn (h.secImage y L) := by
  rw [← TwoQuot.map_layerIn_of_le_centralizer (h.secMk y)
    (h.subgroupOf_le_centralizer_ker y hLc), B5a.layerIn_subgroupOf hLG]

theorem secImage_fixedLayer {L E : Subgroup X} (hLG : L ≤ h.secG0 y)
    (hLc : L ≤ centralizer (h.secB0 y : Set X)) (hBE : h.secB0 y ≤ E) (hEG : E ≤ h.secG0 y) :
    h.secImage y (GSLit.fixedLayer L E) = GSLit.fixedLayer (h.secImage y L) (h.secImage y E) := by
  have hk : (h.secMk y).ker ≤ E.subgroupOf (h.secG0 y) := by
    rw [ker_secMk]
    exact fun _ hg => hBE hg
  rw [← TwoQuot.map_fixedLayer_of_ker_le (h.secMk y) (h.subgroupOf_le_centralizer_ker y hLc) hk
    (h.isPGroup_ker_secMk y), B5a.fixedLayer_subgroupOf hLG hEG]

theorem secMk_mem_coreActionKernel {L : Subgroup X} (hLG : L ≤ h.secG0 y) {g : X}
    (hg : g ∈ h.secG0 y) (hgL : g ∈ coreActionKernel L) :
    h.secMk y ⟨g, hg⟩ ∈ coreActionKernel (h.secImage y L) := by
  have h1 : (⟨g, hg⟩ : ↥(h.secG0 y)) ∈ coreActionKernel (L.subgroupOf (h.secG0 y)) := by
    rw [B5a.coreActionKernel_subgroupOf hLG]
    exact hgL
  exact TwoQuot.map_mem_coreActionKernel (h.secMk y) h1

theorem mem_coreActionKernel_of_secMk {L : Subgroup X} [Group.IsPerfect L]
    (hLG : L ≤ h.secG0 y) (hLc : L ≤ centralizer (h.secB0 y : Set X)) {g : X}
    (hg : g ∈ h.secG0 y) (hgN : g ∈ normalizer (L : Set X))
    (hgL : h.secMk y ⟨g, hg⟩ ∈ coreActionKernel (h.secImage y L)) :
    g ∈ coreActionKernel L := by
  have : Group.IsPerfect (L.subgroupOf (h.secG0 y)) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hLG).symm.toMonoidHom)
      (subgroupOfEquivOfLe hLG).symm.surjective
  have hgN' : (⟨g, hg⟩ : ↥(h.secG0 y)) ∈
      normalizer ((L.subgroupOf (h.secG0 y) : Subgroup ↥(h.secG0 y)) : Set ↥(h.secG0 y)) := by
    rw [← subgroupOf_normalizer_eq hLG, mem_subgroupOf]
    exact hgN
  have h1 := TwoQuot.mem_coreActionKernel_of_map (h.secMk y)
    (h.subgroupOf_le_centralizer_ker y hLc) hgN' hgL
  rw [B5a.coreActionKernel_subgroupOf hLG, mem_subgroupOf] at h1
  exact h1

theorem secMk_mem_secImage_iff {Y : Subgroup X} (hBY : h.secB0 y ≤ Y) (g : ↥(h.secG0 y)) :
    h.secMk y g ∈ h.secImage y Y ↔ (g : X) ∈ Y := by
  constructor
  · intro hg
    obtain ⟨z, hz, hzg⟩ := mem_map.mp hg
    have h1 : z⁻¹ * g ∈ h.secB0' y := by
      rw [← ker_secMk, MonoidHom.mem_ker, map_mul, map_inv, hzg, inv_mul_cancel]
    have h2 : (g : X) = z * ((z⁻¹ * g : ↥(h.secG0 y)) : X) := by simp
    rw [h2]
    exact mul_mem hz (hBY h1)
  · intro hg
    exact mem_map_of_mem _ (show g ∈ Y.subgroupOf (h.secG0 y) from hg)

theorem secImage_inf {A C : Subgroup X} (hBA : h.secB0 y ≤ A) :
    h.secImage y (A ⊓ C) = h.secImage y A ⊓ h.secImage y C := by
  apply le_antisymm
  · exact le_inf (map_mono (fun _ hg => (mem_inf.mp hg).1))
      (map_mono (fun _ hg => (mem_inf.mp hg).2))
  · rintro q ⟨hqA, hqC⟩
    obtain ⟨g, hg, rfl⟩ := mem_map.mp hqC
    have hgA := (secMk_mem_secImage_iff hBA g).mp hqA
    exact mem_map_of_mem _ (show g ∈ (A ⊓ C).subgroupOf (h.secG0 y) from mem_inf.mpr ⟨hgA, hg⟩)

theorem secImage_mono {A C : Subgroup X} (hAC : A ≤ C) : h.secImage y A ≤ h.secImage y C :=
  map_mono (fun _ hg => hAC hg)

theorem secImage_conjugate (Y : Subgroup X) {g : X} (hg : g ∈ h.secG0 y) :
    h.secImage y (conjugate Y g) = conjugate (h.secImage y Y) (h.secMk y ⟨g, hg⟩) := by
  show ((conjugate Y g).subgroupOf (h.secG0 y)).map (h.secMk y) =
    conjugate ((Y.subgroupOf (h.secG0 y)).map (h.secMk y)) (h.secMk y ⟨g, hg⟩)
  rw [show (conjugate Y g).subgroupOf (h.secG0 y) = conjugate (Y.subgroupOf (h.secG0 y)) ⟨g, hg⟩
    from (conjugate_subgroupOf_eq _ _ ⟨g, hg⟩).symm, map_conjugate]

theorem normalizer_secImage {Y : Subgroup X} (hBY : h.secB0 y ≤ Y) (hYG : Y ≤ h.secG0 y) :
    normalizer (h.secImage y Y : Set (h.secBar y)) = h.secImage y (normalizer (Y : Set X)) := by
  ext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [show (g : h.secBar y) = h.secMk y g from rfl,
    secMk_mem_secImage_iff (hBY.trans le_normalizer), mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro hgN z
    by_cases hz : z ∈ h.secG0 y
    · have h1 := hgN (h.secMk y ⟨z, hz⟩)
      rw [← map_inv, ← map_mul, ← map_mul, secMk_mem_secImage_iff hBY,
        secMk_mem_secImage_iff hBY] at h1
      simpa only [coe_mul, coe_inv] using h1
    · have h1 : z ∉ Y := fun hzY => hz (hYG hzY)
      have h2 : (g : X) * z * (g : X)⁻¹ ∉ Y := by
        intro hzY
        apply hz
        have h3 := mul_mem (mul_mem (inv_mem g.2) (hYG hzY)) g.2
        rwa [show (g : X)⁻¹ * ((g : X) * z * (g : X)⁻¹) * g = z by group] at h3
      exact iff_of_false h1 h2
  · intro hgN q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    rw [show (z : h.secBar y) = h.secMk y z from rfl, ← map_inv, ← map_mul, ← map_mul,
      secMk_mem_secImage_iff hBY, secMk_mem_secImage_iff hBY]
    simpa only [coe_mul, coe_inv] using hgN (z : X)

theorem card_secImage {Y : Subgroup X} (hBY : h.secB0 y ≤ Y) (hYG : Y ≤ h.secG0 y) :
    Nat.card (h.secImage y Y) * Nat.card (h.secB0 y) = Nat.card Y := by
  set φ := (h.secMk y).subgroupMap (Y.subgroupOf (h.secG0 y)) with hφ
  have hker : φ.ker = ((h.secB0 y).subgroupOf (h.secG0 y)).subgroupOf (Y.subgroupOf (h.secG0 y))
      := by
    ext z
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro hz
      have h1 : h.secMk y (z : ↥(h.secG0 y)) = 1 := congrArg Subtype.val hz
      rw [← MonoidHom.mem_ker, ker_secMk] at h1
      exact h1
    · intro hz
      apply Subtype.ext
      show h.secMk y (z : ↥(h.secG0 y)) = 1
      rw [← MonoidHom.mem_ker, ker_secMk]
      exact hz
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ
    ((h.secMk y).subgroupMap_surjective _)).toEquiv] at h1
  have h2 : Nat.card φ.ker = Nat.card (h.secB0 y) := by
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe (show (h.secB0 y).subgroupOf (h.secG0 y) ≤
      Y.subgroupOf (h.secG0 y) from fun _ hg => hBY hg)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (h.secB0_le_G0 y)).toEquiv]
  have h3 : Nat.card (Y.subgroupOf (h.secG0 y)) = Nat.card Y :=
    Nat.card_congr (subgroupOfEquivOfLe hYG).toEquiv
  rw [h2, h3] at h1
  exact h1.symm

end Hyp52

end CFSG.ComponentClassification.GSThmB
