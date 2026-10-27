module

public import CFSG.ClassicalInvolution.Asc77.AscCX9X3

public noncomputable section

namespace CFSG.ClassicalInvolution.Asc77.CX.MF2L

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.ClassicalInvolution.Generic
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped MatrixGroups

variable {F : Type} [Field F] {Y : Type} [Group Y]

section Hom

variable {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) (θ : SL(4, F) →* Y) (T : Subgroup Y)
  (hT : T = (spM (spForm m n)).map θ)

@[expose] def homT : StatedSp 2 F →* ↥T :=
  (θ.comp (kappa hm hn)).codRestrict T fun x => by
    rw [hT]
    exact Subgroup.mem_map_of_mem θ (kappa_mem_spM hm hn x)

theorem subtype_comp_homT : T.subtype.comp (homT hm hn θ T hT) = θ.comp (kappa hm hn) := rfl

theorem homT_surjective : Function.Surjective (homT hm hn θ T hT) := by
  rintro ⟨t, ht⟩
  rw [hT] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  rw [← kappa_range hm hn] at hs
  obtain ⟨x, rfl⟩ := hs
  exact ⟨x, rfl⟩

theorem ker_homT_le_center (hker : θ.ker = scalars 4 F) :
    (homT hm hn θ T hT).ker ≤ Subgroup.center (StatedSp 2 F) := by
  intro x hx
  have hx' : kappa hm hn x ∈ θ.ker := by
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val hx
  rw [hker] at hx'
  have hc := (scalars_eq_center 4 F).le hx'
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro y
  apply kappa_injective hm hn
  rw [map_mul, map_mul, hc (kappa hm hn y)]

include hT in
theorem block0_le_T : (blockSL F 4 2 0 (by norm_num)).range.map θ ≤ T := by
  rw [hT]
  exact Subgroup.map_mono (block0_le_spM m n)

include hT in
theorem block2_le_T : (blockSL F 4 2 2 (by norm_num)).range.map θ ≤ T := by
  rw [hT]
  exact Subgroup.map_mono (block2_le_spM m n)

theorem map_homT_longRoot0 :
    (longRootSp2 F 2 0).map (homT hm hn θ T hT) =
      ((blockSL F 4 2 0 (by norm_num)).range.map θ).subgroupOf T := by
  apply Subgroup.map_injective T.subtype_injective
  rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le (block0_le_T θ T hT),
    subtype_comp_homT, ← Subgroup.map_map, kappa_longRoot0]

theorem map_homT_longRoot1 :
    (longRootSp2 F 2 1).map (homT hm hn θ T hT) =
      ((blockSL F 4 2 2 (by norm_num)).range.map θ).subgroupOf T := by
  apply Subgroup.map_injective T.subtype_injective
  rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le (block2_le_T θ T hT),
    subtype_comp_homT, ← Subgroup.map_map, kappa_longRoot1]

end Hom

section Fam

@[expose] def famT {X : Type} [Group X] (ψ : StatedSp 2 F →* X) : Set (Subgroup X) :=
  {L | ∃ P, IsHyperbolicPlane P ∧ L = (planeGroup P).map ψ}

theorem conjSub_map {G₁ G₂ : Type} [Group G₁] [Group G₂] (ψ : G₁ →* G₂) (x : G₁)
    (H : Subgroup G₁) : conjSub (ψ x) (H.map ψ) = (H.map (MulAut.conj x).toMonoidHom).map ψ := by
  ext y
  simp only [conjSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨x * h * x⁻¹, ⟨h, hh, rfl⟩, by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨ψ h, ⟨h, hh, rfl⟩, by rw [map_mul, map_mul, map_inv]⟩

theorem conjSub_mem_famT {X : Type} [Group X] {ψ : StatedSp 2 F →* X}
    (hψ : Function.Surjective ψ) {L : Subgroup X} (hL : L ∈ famT ψ) (y : X) :
    conjSub y L ∈ famT ψ := by
  obtain ⟨P, ⟨u, w, huw, rfl⟩, rfl⟩ := hL
  obtain ⟨x, rfl⟩ := hψ y
  refine ⟨_, ⟨mat 2 F x *ᵥ u, mat 2 F x *ᵥ w, ?_, rfl⟩, ?_⟩
  · rw [form_mulVec]
    exact huw
  · rw [conjSub_map, planeGroup_span_conj]

end Fam

end CFSG.ClassicalInvolution.Asc77.CX.MF2L
