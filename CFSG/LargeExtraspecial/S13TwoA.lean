module

public import CFSG.LargeExtraspecial.S13One

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g g₁ : G} {K : Subgroup S.O}

variable (S) in
@[expose] def ptStab (W : Submodule (ZMod 2) S.Qt) : Subgroup S.O where
  carrier := {x | ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w}
  mul_mem' := fun {x y} hx hy w hw => by
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hy w hw, hx w hw]
  one_mem' := fun _ _ => rfl
  inv_mem' := fun {x} hx w hw => by
    conv_lhs => rw [← hx w hw]
    exact LinearEquiv.symm_apply_apply _ w

theorem mem_ptStab {W : Submodule (ZMod 2) S.Qt} {x : S.O} :
    x ∈ ptStab S W ↔ ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := Iff.rfl

theorem inf_eq_bot_of_ne (hK3 : Nat.card K = 3) (hfpf : FixFree S K)
    {F₁ F₂ : Submodule (ZMod 2) S.Qt} (h₁ : finrank (ZMod 2) F₁ = 2)
    (hF₁ : ∀ k ∈ K, ∀ v ∈ F₁, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ F₁)
    (hF₂ : ∀ k ∈ K, ∀ v ∈ F₂, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ F₂)
    (h₂ : finrank (ZMod 2) F₂ = 2) (hne : F₁ ≠ F₂) : F₁ ⊓ F₂ = ⊥ := by
  by_contra hb
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨k, hk, hk1⟩ : ∃ k ∈ K, k ≠ 1 := by
    by_contra h
    push Not at h
    have : K = ⊥ := (eq_bot_iff_forall K).mpr h
    rw [this, card_bot] at hK3
    omega
  have hkv0 : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v ≠ 0 := fun h =>
    hv0 (by simpa using congrArg (k : S.Qt ≃ₗ[ZMod 2] S.Qt).symm h)
  have hne' : v ≠ (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v := fun h =>
    hv0 (fix_eq_zero hK3 hfpf hk hk1 _ h.symm)
  have hli := linearIndependent_pair_zmod2 hv0 hkv0 hne'
  have hsp : Submodule.span (ZMod 2) (Set.range ![v, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v]) ≤ F₁ ⊓ F₂ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hv
    · exact ⟨hF₁ k hk v hv.1, hF₂ k hk v hv.2⟩
  have h2 := finrank_span_eq_card hli
  simp only [Fintype.card_fin] at h2
  have h3 := Submodule.finrank_mono hsp
  have h4 := Submodule.finrank_mono (inf_le_left : F₁ ⊓ F₂ ≤ F₁)
  have h5 := Submodule.finrank_mono (inf_le_right : F₁ ⊓ F₂ ≤ F₂)
  have e1 := Submodule.eq_of_le_of_finrank_le (inf_le_left : F₁ ⊓ F₂ ≤ F₁) (by omega)
  have e2 := Submodule.eq_of_le_of_finrank_le (inf_le_right : F₁ ⊓ F₂ ≤ F₂) (by omega)
  exact hne (e1.symm.trans e2)

section Conf

variable (Y : Hyp13 S g K) (Y₁ : Hyp13 S g₁ K)
include Y

theorem Hyp13.finrank_Fbar : finrank (ZMod 2) (Fbar S g K) = 2 := by
  obtain ⟨k, hk, hk1⟩ := Y.exists_K
  exact S13.finrank_Fbar Y.H Y.card_K Y.normal Y.fpf hk hk1

omit Y in
theorem Hyp13.K_apply_mem_Fbar {k : S.O} (hk : k ∈ K) {v : S.Qt} (hv : v ∈ Fbar S g K) :
    (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Fbar S g K := apply_mem_Fbar_of_mem_K hk hv

include Y₁

theorem Fbar_inf_eq_bot (hne : Fbar S g₁ K ≠ Fbar S g K) :
    Fbar S g K ⊓ Fbar S g₁ K = ⊥ :=
  inf_eq_bot_of_ne Y.card_K Y.fpf Y.finrank_Fbar (fun _ hk _ hv => Hyp13.K_apply_mem_Fbar hk hv)
    (fun _ hk _ hv => Hyp13.K_apply_mem_Fbar hk hv) Y₁.finrank_Fbar (Ne.symm hne)

theorem finrank_Dbar (hne : Fbar S g₁ K ≠ Fbar S g K) :
    finrank (ZMod 2) (Fbar S g K ⊔ Fbar S g₁ K : Submodule (ZMod 2) S.Qt) = 4 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (Fbar S g K) (Fbar S g₁ K)
  rw [Fbar_inf_eq_bot Y Y₁ hne, finrank_bot, add_zero, Y.finrank_Fbar, Y₁.finrank_Fbar] at h
  exact h

omit Y₁ in
theorem Ebar_apply_sub_mem_Fbar_of_perp {F₁ : Submodule (ZMod 2) S.Qt}
    (hperp : ∀ u ∈ Fbar S g K, ∀ v ∈ F₁, polar S.q u v = 0) {e : S.O} (he : e ∈ Ebar S g K)
    {v : S.Qt} (hv : v ∈ (Fbar S g K ⊔ F₁ : Submodule (ZMod 2) S.Qt)) :
    (e : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Fbar S g K := by
  obtain ⟨f, hf, f₁, hf₁, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, hf e he, add_sub_add_left_eq_sub]
  refine Y.Ebar_apply_sub_mem_Fbar (fun u hu => ?_) he
  rw [QuadraticMap.polar_comm]
  exact hperp u hu f₁ hf₁

end Conf

end CFSG.LargeExtraspecial.S13
