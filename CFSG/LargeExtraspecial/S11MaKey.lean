module

public import CFSG.LargeExtraspecial.S11EightD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u_G

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G}

omit [Finite G] in
theorem clSub_inf_of_z_mem {X Y : Subgroup G} (hz : S.z ∈ Y) :
    S.clSub (X ⊓ Y) = S.clSub X ⊓ S.clSub Y := by
  refine le_antisymm (le_inf (S.clSub_mono inf_le_left) (S.clSub_mono inf_le_right)) ?_
  rintro v ⟨hvX, hvY⟩
  obtain ⟨x, hxX, hxQ, rfl⟩ := S.mem_clSub_iff.mp hvX
  obtain ⟨y, hyY, hyQ, hxy⟩ := S.mem_clSub_iff.mp hvY
  rcases (S.cl_eq_cl_iff hyQ hxQ).mp hxy with h | h
  · exact S.cl_mem_clSub ⟨hxX, by rw [h]; exact hyY⟩ hxQ
  · exact S.cl_mem_clSub ⟨hxX, by rw [h]; exact Y.mul_mem hyY hz⟩ hxQ

theorem card_QG_inf_Qa_inf_Qa {k₁ k₂ : G} (hk₁Q : k₁ * S.z * k₁⁻¹ ∈ S.QG)
    (hk₁z : k₁ * S.z * k₁⁻¹ ≠ S.z) (hk₂Q : k₂ * S.z * k₂⁻¹ ∈ S.QG)
    (hk₂z : k₂ * S.z * k₂⁻¹ ≠ S.z) :
    Nat.card (S.QG ⊓ S.Qa k₁ ⊓ S.Qa k₂ : Subgroup G) =
      2 ^ (finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa k₁) ⊓ S.clSub (S.QG ⊓ S.Qa k₂)) + 1) := by
  set X := S.QG ⊓ S.Qa k₁ ⊓ S.Qa k₂ with hX
  have hXQ : X ≤ S.QG := fun x hx => hx.1.1
  have hzX : S.z ∈ X := ⟨⟨S.z_mem_QG, S.z_mem_Qa hk₁Q hk₁z⟩, S.z_mem_Qa hk₂Q hk₂z⟩
  have hcl : S.clSub X = S.clSub (S.QG ⊓ S.Qa k₁) ⊓ S.clSub (S.QG ⊓ S.Qa k₂) := by
    rw [← clSub_inf_of_z_mem (⟨S.z_mem_QG, S.z_mem_Qa hk₂Q hk₂z⟩ : S.z ∈ S.QG ⊓ S.Qa k₂)]
    congr 1
    ext x
    simp only [hX, mem_inf]
    tauto
  rw [← S.clPre_clSub hXQ hzX, S.card_clPre, S.card_submodule, hcl, pow_succ, mul_comm]

theorem Qa_inf_Qa_le_M {k₁ k₂ : G} (hk₁Q : k₁ * S.z * k₁⁻¹ ∈ S.QG)
    (hk₁z : k₁ * S.z * k₁⁻¹ ≠ S.z) (hk₂Q : k₂ * S.z * k₂⁻¹ ∈ S.QG)
    (hk₂z : k₂ * S.z * k₂⁻¹ ≠ S.z) (hne : k₁ * S.z * k₁⁻¹ ≠ k₂ * S.z * k₂⁻¹) :
    S.Qa k₁ ⊓ S.Qa k₂ ≤ S.M := by
  intro x hx
  rw [S.mem_M_iff]
  have hz₁ : (S.conjBy k₁).z = k₁ * S.z * k₁⁻¹ := rfl
  have hz₂ : (S.conjBy k₂).z = k₂ * S.z * k₂⁻¹ := rfl
  have h1 := (S.conjBy k₁).commutator_eq_one_or_z hx.1 (S.z_mem_Qa hk₁Q hk₁z)
  have h2 := (S.conjBy k₂).commutator_eq_one_or_z hx.2 (S.z_mem_Qa hk₂Q hk₂z)
  rw [hz₁] at h1
  rw [hz₂] at h2
  have e : x * S.z * x⁻¹ * S.z⁻¹ = 1 := by
    rcases h1 with h1 | h1
    · exact h1
    rcases h2 with h2 | h2
    · exact h2
    exact absurd (h1.symm.trans h2) hne
  calc x * S.z = x * S.z * x⁻¹ * S.z⁻¹ * (S.z * x) := by group
    _ = S.z * x := by rw [e, one_mul]

theorem Hyp.card_Qa_inf_Qa (hy : Hyp S g) {k₁ k₂ : G} (hb : k₂ * S.z * k₂⁻¹ ∈ S.Qa k₁)
    (hne : k₂ * S.z * k₂⁻¹ ≠ k₁ * S.z * k₁⁻¹) :
    Nat.card (S.Qa k₁ ⊓ S.Qa k₂ : Subgroup G) = 2 ^ (S.width + 1) := by
  have hmap : S.Qa k₁ ⊓ S.Qa k₂ =
      (S.QG ⊓ S.Qa (k₁⁻¹ * k₂)).map (MulAut.conj k₁).toMonoidHom := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj k₁).injective, ← S.Qa_mul, mul_inv_cancel_left,
      ← S.Qa_eq_map]
  rw [hmap, Subgroup.card_map_of_injective (MulAut.conj k₁).injective]
  have hQ : (k₁⁻¹ * k₂) * S.z * (k₁⁻¹ * k₂)⁻¹ ∈ S.QG := by
    rw [inv_mul_conj_z]
    exact (S11.mem_Qa_iff S k₁ _).mp hb
  have hz : (k₁⁻¹ * k₂) * S.z * (k₁⁻¹ * k₂)⁻¹ ≠ S.z := by
    rw [inv_mul_conj_z]
    intro h
    apply hne
    calc k₂ * S.z * k₂⁻¹ = k₁ * (k₁⁻¹ * (k₂ * S.z * k₂⁻¹) * k₁) * k₁⁻¹ := by group
      _ = k₁ * S.z * k₁⁻¹ := by rw [h]
  exact (hy.cons_of hQ hz).card_QG_inf_Qa

section Conf

variable (hy : Hyp S g) (K : Conf S g t τ u) {k₁ k₂ : G}
  (hk₁ : k₁ * S.z * k₁⁻¹ ∈ S.QG ⊓ S.Qa u) (hk₂ : k₂ * S.z * k₂⁻¹ ∈ S.QG ⊓ S.Qa u)
  (hne : k₁ * S.z * k₁⁻¹ ≠ k₂ * S.z * k₂⁻¹)
include hy K hk₁ hk₂ hne

theorem Conf.Lbar_inf_Lbar_le_Nbar : S.Lbar k₁ ⊓ S.Lbar k₂ ≤ Nbar S g t := by
  intro x hx
  obtain ⟨hk₁z, htk₁⟩ := K.base_of_mem hk₁
  refine mem_Nbar.mpr ⟨?_, fun v hv => ?_⟩
  · rw [← hy.Rbar_eq hk₁.1 hk₁z t]
    exact Lbar_le_Rbar htk₁ hx.1
  have h1 := Lbar_apply_sub_mem_span' hk₁.1 (K.Vt_le_clSub hy hk₁ hv) hx.1
  have h2 := Lbar_apply_sub_mem_span' hk₂.1 (K.Vt_le_clSub hy hk₂ hv) hx.2
  rcases mem_span_cl_iff.mp h1 with h0 | h0
  · exact sub_eq_zero.mp h0
  rcases mem_span_cl_iff.mp h2 with h0' | h0'
  · exact sub_eq_zero.mp h0'
  exfalso
  rcases (S.cl_eq_cl_iff hk₁.1 hk₂.1).mp (h0.symm.trans h0') with h3 | h3
  · exact hne h3.symm
  · apply K.z_not_mem
    have e : S.z = (k₁ * S.z * k₁⁻¹)⁻¹ * (k₂ * S.z * k₂⁻¹) := by
      rw [h3]
      group
    rw [e]
    exact mul_mem (inv_mem hk₁.2) hk₂.2

theorem Conf.Lbar_inf_Lbar_le_map :
    S.Lbar k₁ ⊓ S.Lbar k₂ ≤ (((S.Qa k₁ ⊓ S.Qa k₂) ⊓ S.Qa u).subgroupOf S.M).map S.ρ := by
  intro s hs
  have hN := K.Lbar_inf_Lbar_le_Nbar hy hk₁ hk₂ hne hs
  have h1 : s ∈ S.Lbar k₁ ⊓ Nbar S g t := ⟨hs.1, hN⟩
  have h2 : s ∈ S.Lbar k₂ ⊓ Nbar S g t := ⟨hs.2, hN⟩
  rw [K.Lbar_inf_Nbar_eq hy hk₁] at h1
  rw [K.Lbar_inf_Nbar_eq hy hk₂] at h2
  obtain ⟨y₁, hy₁, rfl⟩ := h1
  obtain ⟨y₂, hy₂, hy₂x⟩ := h2
  have hy₁' := mem_inf.mp (mem_inf.mp (mem_subgroupOf.mp hy₁)).1
  have hy₂' := mem_inf.mp (mem_inf.mp (mem_subgroupOf.mp hy₂)).1
  have hq : ((y₁⁻¹ * y₂ : S.M) : G) ∈ S.QG := by
    rw [← S.ρ_eq_one_iff, map_mul, map_inv, hy₂x, inv_mul_cancel]
  have hqE : ((y₁⁻¹ * y₂ : S.M) : G) ∈ S.QG ⊓ S.Qa u := by
    refine ⟨hq, ?_⟩
    simpa using mul_mem (inv_mem hy₁'.2) hy₂'.2
  have hqb : ((y₁⁻¹ * y₂ : S.M) : G) ∈ S.Qa k₂ := K.mem_Qa_of_mem_E hy hk₂ hqE
  have hy₁b : (y₁ : G) ∈ S.Qa k₂ := by
    have := mul_mem hy₂'.1 (inv_mem hqb)
    simpa [mul_assoc] using this
  exact ⟨y₁, mem_subgroupOf.mpr ⟨⟨hy₁'.1, hy₁b⟩, hy₁'.2⟩, rfl⟩

theorem Conf.Lbar_inf_Lbar_eq :
    S.Lbar k₁ ⊓ S.Lbar k₂ = ((S.Qa k₁ ⊓ S.Qa k₂).subgroupOf S.M).map S.ρ := by
  refine le_antisymm ((K.Lbar_inf_Lbar_le_map hy hk₁ hk₂ hne).trans
    (map_mono fun x hx => mem_subgroupOf.mpr (mem_subgroupOf.mp hx).1)) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' := mem_subgroupOf.mp hx
  exact ⟨S.ρ_mem_Lbar ⟨hx'.1, x.2⟩, S.ρ_mem_Lbar ⟨hx'.2, x.2⟩⟩

theorem Conf.map_eq_map :
    ((S.Qa k₁ ⊓ S.Qa k₂).subgroupOf S.M).map S.ρ =
      (((S.Qa k₁ ⊓ S.Qa k₂) ⊓ S.Qa u).subgroupOf S.M).map S.ρ := by
  refine le_antisymm ?_ (map_mono fun x hx => mem_subgroupOf.mpr (mem_subgroupOf.mp hx).1)
  rw [← K.Lbar_inf_Lbar_eq hy hk₁ hk₂ hne]
  exact K.Lbar_inf_Lbar_le_map hy hk₁ hk₂ hne

theorem Conf.card_mul_card :
    Nat.card (S.QG ⊓ S.Qa k₁ ⊓ S.Qa k₂ : Subgroup G) *
        Nat.card (S.Qa u ⊓ S.Qa k₁ ⊓ S.Qa k₂ : Subgroup G) =
      2 ^ (S.width + 1 + finrank (ZMod 2) (Vt S g t)) := by
  obtain ⟨hk₁z, -⟩ := K.base_of_mem hk₁
  obtain ⟨hk₂z, -⟩ := K.base_of_mem hk₂
  set X := S.Qa k₁ ⊓ S.Qa k₂ with hX
  have hXM : X ≤ S.M := Qa_inf_Qa_le_M hk₁.1 hk₁z hk₂.1 hk₂z hne
  set Y := X ⊓ S.Qa u with hY
  have hYM : Y ≤ S.M := inf_le_left.trans hXM
  have h1 := card_eq_card_map_mul hXM
  rw [card_ker_inf_eq hXM] at h1
  have h2 := card_eq_card_map_mul hYM
  rw [card_ker_inf_eq hYM, ← K.map_eq_map hy hk₁ hk₂ hne] at h2
  have hQY : S.QG ⊓ Y = S.QG ⊓ S.Qa u := by
    refine le_antisymm (inf_le_inf_left _ inf_le_right) fun x hx => ⟨hx.1, ⟨?_, ?_⟩, hx.2⟩
    · exact K.mem_Qa_of_mem_E hy hk₁ hx
    · exact K.mem_Qa_of_mem_E hy hk₂ hx
  have hX2 : Nat.card X = 2 ^ (S.width + 1) :=
    hy.card_Qa_inf_Qa (K.mem_Qa_of_mem_E hy hk₁ hk₂) hne.symm
  have e1 : (S.QG ⊓ S.Qa k₁ ⊓ S.Qa k₂ : Subgroup G) = S.QG ⊓ X := by rw [hX, inf_assoc]
  have e2 : (S.Qa u ⊓ S.Qa k₁ ⊓ S.Qa k₂ : Subgroup G) = Y := by
    ext x
    simp only [hY, hX, mem_inf]
    tauto
  rw [e1, e2, h2, hQY, K.card_QG_inf_Qa hy, pow_add, ← hX2, h1]
  ring

end Conf

end CFSG.LargeExtraspecial.S11
