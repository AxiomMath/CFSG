module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0f1a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Basic

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator3_le_of_forall {U V : Subgroup G} (hV : NormalIn V U)
    (h : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U,
      (x * y * x⁻¹ * y⁻¹) * z * (x * y * x⁻¹ * y⁻¹)⁻¹ * z⁻¹ ∈ V) :
    ⁅⁅U, U⁆, U⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro w hw z hz
  have key : ∀ w ∈ ⁅U, U⁆, w ∈ U ∧ ∀ z ∈ U, w * z * w⁻¹ * z⁻¹ ∈ V := by
    intro w hw
    rw [Subgroup.commutator_def] at hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hx
        refine ⟨?_, fun z hz => ?_⟩
        · simpa only [commutatorElement_def] using
            mul_mem (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)) (inv_mem hg₂)
        · simpa only [commutatorElement_def] using h g₁ hg₁ g₂ hg₂ z hz
    | one => exact ⟨U.one_mem, fun z hz => by simp⟩
    | mul x y hx hy ihx ihy =>
        refine ⟨mul_mem ihx.1 ihy.1, fun z hz => ?_⟩
        have h1 : x * (y * z * y⁻¹ * z⁻¹) * x⁻¹ ∈ V := hV.2 x ihx.1 _ (ihy.2 z hz)
        have h2 : x * z * x⁻¹ * z⁻¹ ∈ V := ihx.2 z hz
        have heq : (x * y) * z * (x * y)⁻¹ * z⁻¹ =
            (x * (y * z * y⁻¹ * z⁻¹) * x⁻¹) * (x * z * x⁻¹ * z⁻¹) := by group
        rw [heq]
        exact mul_mem h1 h2
    | inv x hx ih =>
        refine ⟨inv_mem ih.1, fun z hz => ?_⟩
        have h1 : x⁻¹ * (x * z * x⁻¹ * z⁻¹)⁻¹ * x ∈ V :=
          by simpa only [inv_inv] using
            hV.2 x⁻¹ (inv_mem ih.1) _ (inv_mem (ih.2 z hz))
        have heq : x⁻¹ * z * (x⁻¹)⁻¹ * z⁻¹ =
            x⁻¹ * (x * z * x⁻¹ * z⁻¹)⁻¹ * x := by group
        rw [heq]
        exact h1
  exact (key w hw).2 z hz

theorem gamma3_le_of_index_two {U V O : Subgroup G} {l : G} (hV : NormalIn V U) (hOU : O ≤ U)
    (hlU : l ∈ U) (hl : l * l ∈ V) (hOc : ∀ a ∈ O, ∀ b ∈ O, a * b * a⁻¹ * b⁻¹ ∈ V)
    (hOsq : ∀ a ∈ O, a * a ∈ V) (hOn : ∀ a ∈ O, l * a * l⁻¹ ∈ O)
    (hgen : ∀ h ∈ U, h ∈ O ∨ ∃ a ∈ O, h = a * l) : ⁅⁅U, U⁆, U⁆ ≤ V := by
  haveI : (V.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff hV.1).mpr (fun v u hv hu => hV.2 u hu v hv)
  have key : ∀ x y z : ↥U,
      (x * y * x⁻¹ * y⁻¹) * z * (x * y * x⁻¹ * y⁻¹)⁻¹ * z⁻¹ ∈ V.subgroupOf U := by
    refine class_two_mod_of_index_two (V.subgroupOf U) (O.subgroupOf U) ⟨l, hlU⟩
      ?_ ?_ ?_ ?_ ?_
    · rw [Subgroup.mem_subgroupOf]
      simpa only [Subgroup.coe_mul] using hl
    · intro a ha b hb
      rw [Subgroup.mem_subgroupOf] at ha hb ⊢
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hOc (a : G) ha (b : G) hb
    · intro a ha
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      simpa only [Subgroup.coe_mul] using hOsq (a : G) ha
    · intro a ha
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hOn (a : G) ha
    · intro h
      rcases hgen (h : G) h.2 with hO | ⟨a, haO, haeq⟩
      · exact Or.inl (by rwa [Subgroup.mem_subgroupOf])
      · refine Or.inr ⟨⟨a, hOU haO⟩, ?_, ?_⟩
        · rwa [Subgroup.mem_subgroupOf]
        · exact Subtype.ext (by simpa only [Subgroup.coe_mul] using haeq)
  refine commutator3_le_of_forall hV (fun x hx y hy z hz => ?_)
  have hkv := key ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
  rw [Subgroup.mem_subgroupOf] at hkv
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hkv

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
