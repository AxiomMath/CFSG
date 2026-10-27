module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutAmbient

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34

open Subgroup

variable {G : Type} [Group G]

theorem conj_mem_of_charIn {A B : Subgroup G} (hAB : CharIn A B) {h : G}
    (hh : h ∈ normalizer (B : Set G)) : ∀ a ∈ A, h * a * h⁻¹ ∈ A := by
  obtain ⟨hABle, hABchar⟩ := hAB
  intro a ha
  let φ : MulAut B := Outside.conjAut B h hh
  have hmap : (A.subgroupOf B).map φ.toMonoidHom = A.subgroupOf B :=
    (Subgroup.characteristic_iff_map_eq.mp hABchar) φ
  have hφ : φ ⟨a, hABle ha⟩ ∈ A.subgroupOf B := by
    have h1 : φ ⟨a, hABle ha⟩ ∈ (A.subgroupOf B).map φ.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨⟨a, hABle ha⟩, ha, rfl⟩
    rwa [hmap] at h1
  have hcoe : ((φ ⟨a, hABle ha⟩ : B) : G) = h * a * h⁻¹ :=
    Outside.conjAut_coe B h hh ⟨a, hABle ha⟩
  have := (Subgroup.mem_subgroupOf (H := A) (K := B)).mp hφ
  rwa [hcoe] at this

theorem normalizer_le_of_charIn {A B : Subgroup G} (hAB : CharIn A B) :
    normalizer (B : Set G) ≤ normalizer (A : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => conj_mem_of_charIn hAB hh a ha, fun ha => ?_⟩
  have h2 := conj_mem_of_charIn hAB (inv_mem hh) _ ha
  simpa [mul_assoc] using h2

end CFSG.OddStandard.SmallF3.HarrisU33.L34
