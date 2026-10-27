module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.ComponentClassification.Walter86.TableII

open Subgroup

theorem normal_map_centralizer {X Y : Type*} [Group X] [Group Y] (π : X →* Y)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center X) (t : X) :
    (((centralizer ({t} : Set X)).map π).subgroupOf (centralizer ({π t} : Set Y))).Normal := by
  refine (Subgroup.normal_subgroupOf_iff ?_).mpr ?_
  · simpa using Subgroup.map_centralizer_le_centralizer_image ({t} : Set X) π
  rintro a b ha hb
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨x, rfl⟩ := hπ b
  have hht : h * t = t * h := Subgroup.mem_centralizer_singleton_iff.mp hh
  have hyt : π x * π t = π t * π x := Subgroup.mem_centralizer_singleton_iff.mp hb
  have hxt : π (x * t * x⁻¹) = π t := by
    rw [map_mul, map_mul, map_inv, hyt, mul_assoc, mul_inv_cancel, mul_one]
  have hdker : x * t * x⁻¹ * t⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxt, mul_inv_cancel]
  set d : X := x * t * x⁻¹ * t⁻¹ with hddef
  have hd : d ∈ center X := hker hdker
  have hdt : x * t * x⁻¹ = d * t := by
    rw [hddef]
    group
  have hconv :
      (x * h * x⁻¹) * (x * t * x⁻¹) = (x * t * x⁻¹) * (x * h * x⁻¹) := by
    calc (x * h * x⁻¹) * (x * t * x⁻¹) = x * (h * t) * x⁻¹ := by group
      _ = x * (t * h) * x⁻¹ := by rw [hht]
      _ = (x * t * x⁻¹) * (x * h * x⁻¹) := by group
  have hconvdt : (x * h * x⁻¹) * (d * t) = (d * t) * (x * h * x⁻¹) := by
    rw [← hdt]
    exact hconv
  have hcenterd : ∀ z : X, z * d = d * z := fun z => Subgroup.mem_center_iff.mp hd z
  have hwt : (x * h * x⁻¹) * t = t * (x * h * x⁻¹) := by
    have key : d * ((x * h * x⁻¹) * t) = d * (t * (x * h * x⁻¹)) := by
      calc d * ((x * h * x⁻¹) * t) = (d * (x * h * x⁻¹)) * t := by group
        _ = ((x * h * x⁻¹) * d) * t := by rw [hcenterd (x * h * x⁻¹)]
        _ = (x * h * x⁻¹) * (d * t) := by group
        _ = (d * t) * (x * h * x⁻¹) := hconvdt
        _ = d * (t * (x * h * x⁻¹)) := by group
    exact mul_left_cancel key
  refine Subgroup.mem_map.mpr ⟨x * h * x⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact hwt
  · simp [map_mul]

end CFSG.ComponentClassification.Walter86.TableII
