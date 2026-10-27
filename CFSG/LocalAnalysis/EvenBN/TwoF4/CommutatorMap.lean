module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCElementaryCoset
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDBasic

public section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup CFSG.LocalAnalysis.ComponentInitial

variable {G : Type*} [Group G]

@[expose] def sectionCentralizer (U V : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ normalizer (U : Set G) ∧ x ∈ normalizer (V : Set G) ∧
    ∀ u ∈ U, u⁻¹ * x⁻¹ * u * x ∈ V}
  one_mem' := ⟨one_mem _, one_mem _, fun u _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxU, hxV, hx⟩ ⟨hyU, hyV, hy⟩
    refine ⟨mul_mem hxU hyU, mul_mem hxV hyV, fun u hu => ?_⟩
    have h1 : u⁻¹ * (x * y)⁻¹ * u * (x * y) =
        (u⁻¹ * y⁻¹ * u * y) * (y⁻¹ * (u⁻¹ * x⁻¹ * u * x) * y) := by group
    rw [h1]
    exact V.mul_mem (hy u hu) ((mem_normalizer_iff''.mp hyV _).mp (hx u hu))
  inv_mem' := by
    rintro x ⟨hxU, hxV, hx⟩
    refine ⟨inv_mem hxU, inv_mem hxV, fun u hu => ?_⟩
    have hu' : x * u * x⁻¹ ∈ U := (mem_normalizer_iff.mp hxU u).mp hu
    have h1 : u⁻¹ * x⁻¹⁻¹ * u * x⁻¹ =
        ((x * u * x⁻¹)⁻¹ * x⁻¹ * (x * u * x⁻¹) * x)⁻¹ := by group
    rw [h1]
    exact V.inv_mem (hx _ hu')

theorem mem_sectionCentralizer_iff {U V : Subgroup G} {x : G} :
    x ∈ sectionCentralizer U V ↔ x ∈ normalizer (U : Set G) ∧ x ∈ normalizer (V : Set G) ∧
      ∀ u ∈ U, u⁻¹ * x⁻¹ * u * x ∈ V :=
  Iff.rfl

theorem sectionCentralizer_le_normalizer_left (U V : Subgroup G) :
    sectionCentralizer U V ≤ normalizer (U : Set G) :=
  fun _ hx => hx.1

theorem sectionCentralizer_le_normalizer_right (U V : Subgroup G) :
    sectionCentralizer U V ≤ normalizer (V : Set G) :=
  fun _ hx => hx.2.1

theorem commutator_mem_of_mem_closure {S : Set G} {V : Subgroup G} {x : G}
    (hSV : closure S ≤ normalizer (V : Set G)) (hS : ∀ s ∈ S, s⁻¹ * x⁻¹ * s * x ∈ V) {u : G}
    (hu : u ∈ closure S) : u⁻¹ * x⁻¹ * u * x ∈ V := by
  induction hu using Subgroup.closure_induction with
  | mem s hs => exact hS s hs
  | one => simp
  | mul a b ha hb iha ihb =>
    have h1 : (a * b)⁻¹ * x⁻¹ * (a * b) * x =
        (b⁻¹ * (a⁻¹ * x⁻¹ * a * x) * b) * (b⁻¹ * x⁻¹ * b * x) := by group
    rw [h1]
    exact V.mul_mem ((mem_normalizer_iff''.mp (hSV hb) _).mp iha) ihb
  | inv a ha iha =>
    have h1 : a⁻¹⁻¹ * x⁻¹ * a⁻¹ * x = a * (a⁻¹ * x⁻¹ * a * x)⁻¹ * a⁻¹ := by group
    rw [h1]
    exact (mem_normalizer_iff.mp (hSV ha) _).mp (V.inv_mem iha)

theorem mem_sectionCentralizer_iff_of_le [Finite G] {U V : Subgroup G} (hVU : V ≤ U) {x : G} :
    x ∈ sectionCentralizer U V ↔ ∀ u ∈ U, u⁻¹ * x⁻¹ * u * x ∈ V := by
  refine ⟨fun hx => hx.2.2, fun h => ⟨?_, ?_, h⟩⟩
  · have : x⁻¹ ∈ normalizer (U : Set G) :=
      CFSG.EvenSmallLie.UnitarySix.YamadaD.mem_normalizer_of_conj_mem fun u hu => by
        have h1 : x⁻¹ * u * x⁻¹⁻¹ = u * (u⁻¹ * x⁻¹ * u * x) := by group
        rw [h1]
        exact U.mul_mem hu (hVU (h u hu))
    simpa using inv_mem this
  · have : x⁻¹ ∈ normalizer (V : Set G) :=
      CFSG.EvenSmallLie.UnitarySix.YamadaD.mem_normalizer_of_conj_mem fun v hv => by
        have h1 : x⁻¹ * v * x⁻¹⁻¹ = v * (v⁻¹ * x⁻¹ * v * x) := by group
        rw [h1]
        exact V.mul_mem hv (h v (hVU hv))
    simpa using inv_mem this

theorem closure_union_eq_sup (S V : Subgroup G) : closure ((S : Set G) ∪ V) = S ⊔ V := by
  rw [Subgroup.closure_union, closure_eq, closure_eq]

theorem mem_sectionCentralizer_sup_iff [Finite G] {S V : Subgroup G}
    (hSV : S ≤ normalizer (V : Set G)) {x : G} :
    x ∈ sectionCentralizer (S ⊔ V) V ↔
      x ∈ normalizer (V : Set G) ∧ ∀ s ∈ S, s⁻¹ * x⁻¹ * s * x ∈ V := by
  constructor
  · intro hx
    exact ⟨hx.2.1, fun s hs => hx.2.2 s (mem_sup_left hs)⟩
  · rintro ⟨hxV, hS⟩
    rw [mem_sectionCentralizer_iff_of_le le_sup_right]
    intro u hu
    rw [← closure_union_eq_sup] at hu
    refine commutator_mem_of_mem_closure
      (by rw [closure_union_eq_sup]; exact sup_le hSV le_normalizer) ?_ hu
    rintro s (hs | hs)
    · exact hS s hs
    · have h1 : s⁻¹ * x⁻¹ * s * x = s⁻¹ * (x⁻¹ * s * x) := by group
      rw [h1]
      exact V.mul_mem (V.inv_mem hs) ((mem_normalizer_iff''.mp hxV s).mp hs)

theorem mem_sectionCentralizer_zpowers_sup_iff [Finite G] {V : Subgroup G} {t : G}
    (htV : t ∈ normalizer (V : Set G)) {x : G} :
    x ∈ sectionCentralizer (zpowers t ⊔ V) V ↔
      x ∈ normalizer (V : Set G) ∧ t⁻¹ * x⁻¹ * t * x ∈ V := by
  rw [mem_sectionCentralizer_sup_iff (zpowers_le.mpr htV)]
  refine ⟨fun h => ⟨h.1, h.2 t (mem_zpowers t)⟩, fun h => ⟨h.1, fun s hs => ?_⟩⟩
  rw [zpowers_eq_closure] at hs
  exact commutator_mem_of_mem_closure (by rw [← zpowers_eq_closure]; exact zpowers_le.mpr htV)
    (by rintro s rfl; exact h.2) hs

end CFSG.LocalAnalysis.EvenBN.TwoF4
