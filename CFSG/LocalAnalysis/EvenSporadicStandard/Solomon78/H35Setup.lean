module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.StandardCentralizer

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem normal_subgroupOf_of_characteristic {K : Subgroup G} {t u : G}
    (ht : t ∈ centralizer (L : Set G))
    (hCt : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hKX : K ≤ L ⊓ centralizer ({u} : Set G))
    (hchar : (K.subgroupOf (L ⊓ centralizer ({u} : Set G))).Characteristic) :
    (K.subgroupOf (centralizer ({u} : Set G) ⊓ centralizer ({t} : Set G))).Normal := by
  set X : Subgroup G := L ⊓ centralizer ({u} : Set G) with hX
  have hKY : K ≤ centralizer ({u} : Set G) ⊓ centralizer ({t} : Set G) := by
    intro k hk
    exact ⟨(hKX hk).2, mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht k (hKX hk).1)⟩
  rw [Subgroup.normal_subgroupOf_iff hKY]
  intro k g hk hg
  have hgL : g ∈ normalizer (L : Set G) := hCt hg.2
  have hgX : g ∈ normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact ⟨(Subgroup.mem_normalizer_iff.1 hgL x).1 hx.1,
        (centralizer ({u} : Set G)).mul_mem ((centralizer ({u} : Set G)).mul_mem hg.1 hx.2)
          ((centralizer ({u} : Set G)).inv_mem hg.1)⟩
    · intro hx
      refine ⟨(Subgroup.mem_normalizer_iff.1 hgL x).2 hx.1, ?_⟩
      have h1 := (centralizer ({u} : Set G)).mul_mem
        ((centralizer ({u} : Set G)).mul_mem ((centralizer ({u} : Set G)).inv_mem hg.1) hx.2) hg.1
      have h2 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rwa [h2] at h1
  have hkX : k ∈ X := hKX hk
  set φ : MulAut ↥X := Subgroup.normalizerMonoidHom X ⟨g, hgX⟩ with hφ
  have hmap := Subgroup.characteristic_iff_map_eq.1 hchar φ
  have hkmem : (⟨k, hkX⟩ : ↥X) ∈ K.subgroupOf X := hk
  have h3 : φ ⟨k, hkX⟩ ∈ (K.subgroupOf X).map φ.toMonoidHom := ⟨_, hkmem, rfl⟩
  rw [hmap] at h3
  have h4 : ((φ ⟨k, hkX⟩ : ↥X) : G) = g * k * g⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe X ⟨g, hgX⟩ ⟨k, hkX⟩
  exact h4 ▸ h3

end CFSG.EvenSporadicStandard.Solomon78
