module

import Mathlib.Tactic.Group

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.CentralizerKernel

variable {G : Type*} [Group G]

theorem centralizer_subgroupOf_normal {H C : Subgroup G} (hCH : C ≤ H)
    (hC : (C.subgroupOf H).Normal) :
    ((Subgroup.centralizer (C : Set G)).subgroupOf H).Normal := by
  refine ⟨fun x hx h => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hx ⊢
  intro c hc
  have hc' : (h⁻¹ * (⟨c, hCH hc⟩ : H) * h : H) ∈ C.subgroupOf H :=
    hC.conj_mem' _ (by simpa [Subgroup.mem_subgroupOf] using hc) h
  have hc'' : ((h⁻¹ * (⟨c, hCH hc⟩ : H) * h : H) : G) ∈ C := hc'
  have := hx _ hc''
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this ⊢
  calc c * ((h : G) * x * (h : G)⁻¹)
      = (h : G) * (((h : G)⁻¹ * c * h) * (x : G)) * (h : G)⁻¹ := by group
    _ = (h : G) * ((x : G) * ((h : G)⁻¹ * c * h)) * (h : G)⁻¹ := by rw [this]
    _ = (h : G) * x * (h : G)⁻¹ * c := by group

theorem commutator_le_centralizer {H C A : Subgroup G} (hCH : C ≤ H)
    (hC : (C.subgroupOf H).Normal) (hAC : ⁅A, C⁆ = ⊥) :
    ⁅A, H⁆ ≤ Subgroup.centralizer (C : Set G) := by
  have hHC : ⁅H, C⁆ ≤ C := by
    rw [Subgroup.commutator_le]
    intro h hh c hc
    have := hC.conj_mem (⟨c, hCH hc⟩ : H) (by simpa [Subgroup.mem_subgroupOf] using hc)
      ⟨h, hh⟩
    have h2 : (h * c * h⁻¹ : G) ∈ C := by simpa [Subgroup.mem_subgroupOf] using this
    have h3 : c⁻¹ ∈ C := C.inv_mem hc
    rw [commutatorElement_def]
    exact C.mul_mem h2 h3
  have hCA : ⁅C, A⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hAC
  have h1 : ⁅⁅A, H⁆, C⁆ = ⊥ := by
    apply Subgroup.commutator_commutator_eq_bot_of_rotate
    · exact eq_bot_iff.mpr (hCA ▸ Subgroup.commutator_mono_left hHC)
    · rw [hCA]; exact Subgroup.commutator_bot_left (H₁ := H)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  have h2 := Subgroup.commutator_mem_commutator hx hc
  rw [h1, Subgroup.mem_bot, commutatorElement_def] at h2
  calc c * x = (x * c * x⁻¹ * c⁻¹) * c * x := by rw [h2]; group
    _ = x * c := by group

end CFSG.GroupTheory.CoprimeActionSupport.CentralizerKernel
