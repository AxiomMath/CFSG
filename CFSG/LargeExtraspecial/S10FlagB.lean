module

public import CFSG.LargeExtraspecial.S10FlagA
public import CFSG.LargeExtraspecial.S10TwoB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem fixCount_stab : ∀ γ : Gm, act γ E00 = E00 → γ ≠ 1 →
    Fintype.card {m : M2 // act γ m = m} = 4 := by
  decide +kernel

theorem finrank_commSpace_ρ₀_stab {γ : Gm} (hγ : act γ E00 = E00) (hγ1 : γ ≠ 1) :
    finrank (ZMod 2) (commSpace (ρ₀ γ)) = 2 := by
  have h1 := finrank_commSpace_add_finrank_fixSpace (K := ZMod 2) (ρ₀ γ)
  rw [finrank_M2] at h1
  have h2 : Nat.card (fixSpace (ρ₀ γ)) = 2 ^ finrank (ZMod 2) (fixSpace (ρ₀ γ)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h3 : Nat.card (fixSpace (ρ₀ γ)) = Fintype.card {m : M2 // act γ m = m} := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun m => by rw [mem_fixSpace]; rfl)
  rw [h3, fixCount_stab γ hγ hγ1] at h2
  have : finrank (ZMod 2) (fixSpace (ρ₀ γ)) = 2 :=
    Nat.pow_right_injective le_rfl (h2.symm.trans (by norm_num))
  omega

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace Frame

variable {X : Hyp10 S g t} (F : Frame X)
include F

theorem map_commSpace_resV (r : Rbar S g t) :
    (commSpace (resV X.haQ t r)).map (F.φ : Vt S g t →ₗ[ZMod 2] M2) =
      commSpace (ρ₀ (F.π r)) := by
  ext m
  simp only [Submodule.mem_map, mem_commSpace, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨F.φ v, by rw [map_sub, F.compat, ρ₀_apply]⟩
  · rintro ⟨m', rfl⟩
    refine ⟨_, ⟨F.φ.symm m', rfl⟩, ?_⟩
    rw [map_sub, F.compat, LinearEquiv.apply_symm_apply, ρ₀_apply]

theorem finrank_commSpace_resV (r : Rbar S g t) :
    finrank (ZMod 2) (commSpace (resV X.haQ t r)) = finrank (ZMod 2) (commSpace (ρ₀ (F.π r))) := by
  rw [← F.map_commSpace_resV, LinearEquiv.finrank_map_eq]

end Frame

theorem finrank_map_Vt (X : Hyp10 S g t) (r : Rbar S g t) :
    finrank (ZMod 2) ((Vt S g t).map
      ((((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1)) =
      finrank (ZMod 2) (commSpace (resV X.haQ t r)) := by
  have e : (Vt S g t).map ((((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) =
      (commSpace (resV X.haQ t r)).map (Vt S g t).subtype := by
    ext v
    simp only [Submodule.mem_map, mem_commSpace, Submodule.coe_subtype]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨_, ⟨⟨w, hw⟩, rfl⟩, ?_⟩
      simp [coe_resV_apply]
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, w.2, by simp [coe_resV_apply]⟩
  rw [e, Submodule.finrank_map_subtype_eq]

theorem finrank_map_Vt_of_Lbar (X : Hyp10 S g t) {x : S.O} (hxL : x ∈ S.Lbar g)
    (hxN : x ∉ Nbar S g t) :
    finrank (ZMod 2) ((Vt S g t).map
      (((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1)) = 2 := by
  obtain ⟨F⟩ := X.exists_frame
  have h := finrank_map_Vt X ⟨x, Lbar_le_Rbar X.ht hxL⟩
  rw [F.finrank_commSpace_resV] at h
  rw [h]
  refine finrank_commSpace_ρ₀_stab (F.π_mem_stabA hxL) fun h1 => hxN ((F.ker _).mp h1)

theorem finrank_commSpace_sup_Wt (X : Hyp10 S g t) {x : S.O} (hx : x ∈ Rbar S g t) :
    finrank (ZMod 2) ↥(commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ Wt S g t) =
      finrank (ZMod 2) ((Vt S g t).map
        (((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1)) +
        finrank (ZMod 2) (Wt S g t) := by
  obtain ⟨hcomm, hfix⟩ := commSpace_t_eq X.H X.C X.ht X.ht1 X.hVQ
  have hxt : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) * (x : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, commute_of_mem_Rbar X.haQ hx]
  have h := finrank_commSpace_sup_fixSpace hxt
  rw [← hcomm, ← hfix]
  exact h

theorem flag_Hyp10 (X : Hyp10 S g t) {x : S.O} (hx : x ∈ Rbar S g t) :
    2 * finrank (ZMod 2) ((Vt S g t).map
        (((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1)) +
      (finrank (ZMod 2) ↥((Wt S g t).map
        (((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ⊔ Vt S g t) - 4) ≤
      finrank (ZMod 2) (commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  have hA : (Vt S g t).map (((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ≤
      Vt S g t := by
    rintro _ ⟨v, hv, rfl⟩
    exact sub_mem (apply_mem_Vt_of_mem_Rbar X.haQ hx hv) hv
  have hB : (Wt S g t).map (((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ≤
      Wt S g t := by
    rintro _ ⟨v, hv, rfl⟩
    exact sub_mem (apply_mem_Wt X.H hx hv) hv
  have h := finrank_flag (((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1)
    (Vt_le_Wt X.H X.ht1) hA hB
  have h2 := finrank_commSpace_sup_Wt X hx
  rw [X.h4] at h
  change _ + _ + (finrank (ZMod 2) ↥(commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ Wt S g t) - _) ≤
    finrank (ZMod 2) (commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt)) at h
  omega

theorem finrank_commSpace_t (X : Hyp10 S g t) :
    finrank (ZMod 2) (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 4 := by
  rw [(commSpace_t_eq X.H X.C X.ht X.ht1 X.hVQ).1, X.h4]

theorem mem_fixWstar_of_finrank_le (X : Hyp10 S g t) {x : S.O} (hxL : x ∈ S.Lbar g)
    (hxN : x ∉ Nbar S g t)
    (hdim : finrank (ZMod 2) (commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≤ 4) :
    x ∈ fixWstar X := by
  have hxR := Lbar_le_Rbar X.ht hxL
  have h := flag_Hyp10 X hxR
  rw [finrank_map_Vt_of_Lbar X hxL hxN] at h
  have hle : (Wt S g t).map (((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ⊔
      Vt S g t ≤ Vt S g t := by
    refine le_of_eq (Submodule.eq_of_le_of_finrank_le le_sup_right ?_).symm
    rw [X.h4]
    omega
  refine ⟨hxR, fun w hw => hle (Submodule.mem_sup_left ⟨w, hw, rfl⟩)⟩

end CFSG.LargeExtraspecial.S10
