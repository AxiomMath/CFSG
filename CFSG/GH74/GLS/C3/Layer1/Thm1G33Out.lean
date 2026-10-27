module

public import CFSG.GH74.GLS.IVK.L2.ExistNotation
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G33

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK
open scoped commutatorElement Pointwise

variable {F : Type} [Field F] [Finite F] {A : Type} [Group A] [Finite A]

theorem outer_comm_mem_innAut (hF : L2Field F) (e : A ≃* L2 F) (α β : MulAut A) :
    ⁅α, β⁆ ∈ innAut A := by
  classical
  obtain ⟨T⟩ : Nonempty (Sylow 2 (MulAut A)) := inferInstance
  obtain ⟨e', N, -⟩ := ivk_1_2a_exists F hF A e T
  obtain ⟨hsup, hcyc, -, hcomm⟩ := ivk_1_2a_struct F hF A e' N
  set I : Subgroup (MulAut A) := innAut A with hI
  set H : Subgroup (MulAut A) := I ⊔ zpowers N.t with hH
  set Fa : Subgroup (MulAut A) := fieldAutSub e' with hFa
  let π : MulAut A →* MulAut A ⧸ I := QuotientGroup.mk' I
  have hker : ∀ a b : MulAut A, ⁅a, b⁆ ∈ I ↔ π a * π b = π b * π a := by
    intro a b
    have h0 : π ⁅a, b⁆ = 1 ↔ ⁅a, b⁆ ∈ I := QuotientGroup.eq_one_iff _
    rw [← h0, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  have hHn : Fa ≤ normalizer (H : Set (MulAut A)) := by
    intro f hf
    have h1 : ∀ g ∈ Fa, ∀ h ∈ H, g * h * g⁻¹ ∈ H := by
      intro g hg h hh
      have hc : ⁅g, h⁆ ∈ I := hcomm g hg h hh
      have : g * h * g⁻¹ = ⁅g, h⁆ * h := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact H.mul_mem (Subgroup.mem_sup_left hc) hh
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => h1 f hf h hh, fun hh => ?_⟩
    have := h1 f⁻¹ (Fa.inv_mem hf) _ hh
    simpa [mul_assoc] using this
  have hdec : ∀ a : MulAut A, ∃ h ∈ H, ∃ g ∈ Fa, h * g = a := by
    intro a
    have ha : a ∈ H ⊔ Fa := by rw [hsup]; exact Subgroup.mem_top a
    have h2 : (↑(H ⊔ Fa) : Set (MulAut A)) = (H : Set (MulAut A)) * (Fa : Set (MulAut A)) :=
      Subgroup.coe_mul_of_right_le_normalizer_left H Fa hHn
    have ha' : a ∈ (H : Set (MulAut A)) * (Fa : Set (MulAut A)) := by rw [← h2]; exact ha
    obtain ⟨h, hh, g, hg, hhg⟩ := ha'
    exact ⟨h, hh, g, hg, hhg⟩
  have hHim : ∀ h ∈ H, ∃ k : ℤ, π h = (π N.t) ^ k := by
    intro h hh
    have h1 : π h ∈ H.map π := Subgroup.mem_map_of_mem π hh
    have h2 : H.map π = zpowers (π N.t) := by
      rw [hH, Subgroup.map_sup, MonoidHom.map_zpowers]
      have : I.map π = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨a, ha, rfl⟩
        exact (QuotientGroup.eq_one_iff a).2 ha
      rw [this, bot_sup_eq]
    rw [h2] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
    exact ⟨k, hk.symm⟩
  have hFcomm : ∀ g₁ ∈ Fa, ∀ g₂ ∈ Fa, g₁ * g₂ = g₂ * g₁ := by
    intro g₁ hg₁ g₂ hg₂
    have := hcyc
    exact congrArg Subtype.val
      ((IsCyclic.isMulCommutative (α := ↥Fa)).is_comm.comm ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩)
  obtain ⟨h₁, hh₁, g₁, hg₁, rfl⟩ := hdec α
  obtain ⟨h₂, hh₂, g₂, hg₂, rfl⟩ := hdec β
  obtain ⟨k₁, hk₁⟩ := hHim h₁ hh₁
  obtain ⟨k₂, hk₂⟩ := hHim h₂ hh₂
  rw [hker]
  have hFH : ∀ g ∈ Fa, ∀ k : ℤ, π g * (π N.t) ^ k = (π N.t) ^ k * π g := by
    intro g hg k
    have htH : N.t ^ k ∈ H := H.zpow_mem (Subgroup.mem_sup_right (mem_zpowers N.t)) k
    have := (hker g (N.t ^ k)).1 (hcomm g hg _ htH)
    simpa using this
  have c1 : Commute ((π N.t) ^ k₁) ((π N.t) ^ k₂) := (Commute.refl (π N.t)).zpow_zpow k₁ k₂
  have c2 : Commute (π g₁) (π g₂) := by
    have := hFcomm g₁ hg₁ g₂ hg₂
    show π g₁ * π g₂ = π g₂ * π g₁
    rw [← map_mul, ← map_mul, this]
  have c3 : Commute (π g₁) ((π N.t) ^ k₂) := hFH g₁ hg₁ k₂
  have c4 : Commute (π g₂) ((π N.t) ^ k₁) := hFH g₂ hg₂ k₁
  rw [map_mul, map_mul, hk₁, hk₂]
  exact ((c1.mul_right c4.symm).mul_left (c3.mul_right c2)).eq

end CFSG.GH74.GLS.C3.Layer1.Thm1G33
