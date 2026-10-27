module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCores
import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect
  perfectCore_perfect)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_sup)

section General

variable {G : Type*} [Group G] [Finite G]

theorem perfectCore_eq_of_le_of_commutator_le {C P : Subgroup G} (hCP : C ≤ P)
    (hPC : ⁅P, P⁆ ≤ C) : perfectCore P = perfectCore C := by
  refine le_antisymm ?_ (perfectCore_mono hCP)
  have h1 : perfectCore P ≤ C :=
    calc perfectCore P = ⁅perfectCore P, perfectCore P⁆ := (perfectCore_perfect P).symm
      _ ≤ ⁅P, P⁆ := commutator_mono (perfectCore_le P) (perfectCore_le P)
      _ ≤ C := hPC
  exact le_perfectCore_of_perfect h1 (perfectCore_perfect P)

end General

section Twisted

variable {S : Type*} [Group S] {ι : Type*}

@[expose] def fixAll (α : ι → MulAut S) : Subgroup S where
  carrier := {x | ∀ i, α i x = x}
  one_mem' := fun i => map_one (α i)
  mul_mem' := fun {x y} hx hy i => by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [map_mul, hx i, hy i]
  inv_mem' := fun {x} hx i => by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [map_inv, hx i]

theorem mem_fixAll {α : ι → MulAut S} {x : S} : x ∈ fixAll α ↔ ∀ i, α i x = x :=
  Iff.rfl

theorem fixAll_comp_of_surjective {κ : Type*} (α : ι → MulAut S) {f : κ → ι}
    (hf : Function.Surjective f) : fixAll (α ∘ f) = fixAll α := by
  ext x
  simp only [mem_fixAll, Function.comp_apply]
  exact ⟨fun h i => by obtain ⟨k, rfl⟩ := hf i; exact h k, fun h k => h (f k)⟩

private theorem twist_mul (α : MulAut S) {x y : S} (hy : α y * y⁻¹ ∈ center S) :
    α (x * y) * (x * y)⁻¹ = (α x * x⁻¹) * (α y * y⁻¹) := by
  have hc := mem_center_iff.mp hy x⁻¹
  rw [map_mul, mul_inv_rev]
  calc α x * α y * (y⁻¹ * x⁻¹) = α x * ((α y * y⁻¹) * x⁻¹) := by group
    _ = α x * (x⁻¹ * (α y * y⁻¹)) := by rw [hc]
    _ = (α x * x⁻¹) * (α y * y⁻¹) := by group

@[expose] def twistedFix (α : ι → MulAut S) (Z : Subgroup S) (hZ : Z ≤ center S) :
    Subgroup S where
  carrier := {x | ∀ i, α i x * x⁻¹ ∈ Z}
  one_mem' := fun i => by simp
  mul_mem' := fun {x y} hx hy i => by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [twist_mul (α i) (hZ (hy i))]
    exact Z.mul_mem (hx i) (hy i)
  inv_mem' := fun {x} hx i => by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have hz := hx i
    have hax : α i x = (α i x * x⁻¹) * x := by group
    have key : α i x⁻¹ * x⁻¹⁻¹ = (α i x * x⁻¹)⁻¹ := by
      rw [map_inv, inv_inv]
      calc (α i x)⁻¹ * x = ((α i x * x⁻¹) * x)⁻¹ * x := by rw [← hax]
        _ = x⁻¹ * (α i x * x⁻¹)⁻¹ * x := by group
        _ = x⁻¹ * (x * (α i x * x⁻¹)⁻¹) := by
          rw [mul_assoc, (mem_center_iff.mp (Z.inv_mem hz |> hZ) x).symm]
        _ = (α i x * x⁻¹)⁻¹ := by group
    rw [key]
    exact Z.inv_mem hz

theorem mem_twistedFix {α : ι → MulAut S} {Z : Subgroup S} {hZ : Z ≤ center S} {x : S} :
    x ∈ twistedFix α Z hZ ↔ ∀ i, α i x * x⁻¹ ∈ Z :=
  Iff.rfl

theorem fixAll_le_twistedFix (α : ι → MulAut S) (Z : Subgroup S) (hZ : Z ≤ center S) :
    fixAll α ≤ twistedFix α Z hZ := fun x hx i => by
  rw [hx i, mul_inv_cancel]
  exact Z.one_mem

theorem commutator_twistedFix_le (α : ι → MulAut S) (Z : Subgroup S) (hZ : Z ≤ center S) :
    ⁅twistedFix α Z hZ, twistedFix α Z hZ⁆ ≤ fixAll α := by
  rw [commutator_le]
  intro x hx y hy i
  have ex : α i x = (α i x * x⁻¹) * x := by group
  have ey : α i y = (α i y * y⁻¹) * y := by group
  rw [map_commutatorElement, ex, ey]
  exact CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center (hZ (hx i)) (hZ (hy i))
    x y

theorem perfectCore_twistedFix [Finite S] (α : ι → MulAut S) (Z : Subgroup S)
    (hZ : Z ≤ center S) : perfectCore (twistedFix α Z hZ) = perfectCore (fixAll α) :=
  perfectCore_eq_of_le_of_commutator_le (fixAll_le_twistedFix α Z hZ)
    (commutator_twistedFix_le α Z hZ)

end Twisted

section Param

variable {S G : Type*} [Group S] [Group G]

theorem range_inf_centralizer_eq_map (Φ : S →* G) (hker : Φ.ker ≤ center S) {T : Subgroup G}
    (α : T → MulAut S) (hα : ∀ (d : T) (x : S), Φ (α d x) = (d : G) * Φ x * (d : G)⁻¹) :
    Φ.range ⊓ centralizer (T : Set G) = (twistedFix α Φ.ker hker).map Φ := by
  ext y
  simp only [mem_inf, MonoidHom.mem_range, mem_map, mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨⟨x, rfl⟩, hc⟩
    refine ⟨x, mem_twistedFix.2 fun d => ?_, rfl⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hα, mul_inv_eq_one, hc d d.2, mul_inv_cancel_right]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, fun d hd => ?_⟩
    have h := mem_twistedFix.1 hx ⟨d, hd⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hα, mul_inv_eq_one] at h
    calc d * Φ x = d * Φ x * d⁻¹ * d := by group
      _ = Φ x * d := by rw [h]

theorem perfectCore_range_inf_centralizer [Finite S] [Finite G] (Φ : S →* G)
    (hker : Φ.ker ≤ center S) {T : Subgroup G} (α : T → MulAut S)
    (hα : ∀ (d : T) (x : S), Φ (α d x) = (d : G) * Φ x * (d : G)⁻¹) :
    perfectCore (Φ.range ⊓ centralizer (T : Set G)) = (perfectCore (fixAll α)).map Φ := by
  rw [range_inf_centralizer_eq_map Φ hker α hα, ← CFSG.Quasithin.map_perfectCore,
    perfectCore_twistedFix]

theorem centralizerPerfectCore_eq_map_of_le [Finite S] [Finite G] (Φ : S →* G)
    (hker : Φ.ker ≤ center S) {Y T : Subgroup G} (hYT : Y ≤ T)
    (hrange : Φ.range = centralizerPerfectCore Y) (α : T → MulAut S)
    (hα : ∀ (d : T) (x : S), Φ (α d x) = (d : G) * Φ x * (d : G)⁻¹) :
    centralizerPerfectCore T = (perfectCore (fixAll α)).map Φ := by
  rw [← perfectCore_range_inf_centralizer Φ hker α hα, hrange, ← centralizerPerfectCore_sup,
    sup_eq_right.mpr hYT]

end Param

end CFSG.SeitzReduction.LinearPilot
