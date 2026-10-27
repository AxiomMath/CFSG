module

public import CFSG.LargeExtraspecial.S10SixC
public import CFSG.LargeExtraspecial.S10FlagC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
theorem stab_a2_mul : ∀ γ δ : Gm, act γ E00 = E00 → act δ E00 = E00 → γ ≠ 1 → δ ≠ 1 →
    γ ≠ τ₁ * τ₂ → δ ≠ τ₁ * τ₂ → γ * δ ≠ τ₁ * τ₂ → γ * δ = 1 := by
  decide +kernel

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem noFix_conj (X : Hyp10 S g t)
    (hno : ∀ x ∈ S.Lbar g, x ∉ Nbar S g t → x ∉ fixWstar X) {k : S.M}
    (hk : S.ρ k ∈ normalizer (S.Lbar g : Set S.O)) {τ : S.O}
    (hτ : τ = S.ρ k * t * (S.ρ k)⁻¹) (Y : Hyp10 S g τ) :
    ∀ x ∈ S.Lbar g, x ∉ Nbar S g τ → x ∉ fixWstar Y := by
  intro x hxL hxN hxW
  have hNc : Nbar S g τ = (Nbar S g t).map (cK S k) := by
    subst hτ
    exact Nbar_conj X.haQ k t
  rw [mem_fixWstar_conj' X hτ Y] at hxW
  refine hno _ ?_ (fun h => hxN ?_) hxW
  · have := (mem_normalizer_iff.mp (inv_mem hk) x).mp hxL
    simpa using this
  · rw [hNc, mem_map_cK_iff]
    exact h

theorem t_mem_Nbar_of_noFix (X : Hyp10 S g t)
    (hno : ∀ x ∈ S.Lbar g, x ∉ Nbar S g t → x ∉ fixWstar X) {k : S.M}
    (hk : S.ρ k ∈ normalizer (S.Lbar g : Set S.O)) {τ : S.O}
    (hτ : τ = S.ρ k * t * (S.ρ k)⁻¹) (Y : Hyp10 S g τ) : t ∈ Nbar S g τ := by
  have e : S.ρ k⁻¹ * τ * (S.ρ k⁻¹)⁻¹ = t := by
    rw [map_inv, inv_inv, hτ]
    group
  have h1 := mem_Nbar_of_noFix Y (noFix_conj X hno hk hτ Y) (m := k⁻¹) (by rw [e]; exact X.ht)
  rwa [e] at h1

theorem pi_ne_c2 (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (h7 : 7 ≤ S.width) {τ : S.O}
    (Y : Hyp10 S g τ) (F : Frame X) {x : S.O} (hx : x ∈ S.Lbar g ⊓ Nbar S g τ) :
    F.π ⟨x, Lbar_le_Rbar X.ht hx.1⟩ ≠ τ₁ * τ₂ := by
  intro h
  have h1 := width_le_finrank_commSpace hCE X F hx.1 h
  have h2 := finrank_commSpace_le_six hCE Y hx
  omega

theorem mul_mem_Nbar_of_mem (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (h7 : 7 ≤ S.width)
    {τ : S.O} (Y : Hyp10 S g τ) {x x' : S.O} (hx : x ∈ S.Lbar g ⊓ Nbar S g τ)
    (hx' : x' ∈ S.Lbar g ⊓ Nbar S g τ) (hxN : x ∉ Nbar S g t) (hx'N : x' ∉ Nbar S g t) :
    x * x' ∈ Nbar S g t := by
  obtain ⟨F⟩ := X.exists_frame
  have hxx' : x * x' ∈ S.Lbar g ⊓ Nbar S g τ := mul_mem hx hx'
  have hmul : F.π ⟨x * x', Lbar_le_Rbar X.ht hxx'.1⟩ =
      F.π ⟨x, Lbar_le_Rbar X.ht hx.1⟩ * F.π ⟨x', Lbar_le_Rbar X.ht hx'.1⟩ := by
    have e : (⟨x * x', Lbar_le_Rbar X.ht hxx'.1⟩ : Rbar S g t) =
        ⟨x, Lbar_le_Rbar X.ht hx.1⟩ * ⟨x', Lbar_le_Rbar X.ht hx'.1⟩ := Subtype.ext (by simp)
    rw [e, map_mul]
  refine (F.ker ⟨x * x', Lbar_le_Rbar X.ht hxx'.1⟩).mp ?_
  rw [hmul]
  refine stab_a2_mul _ _ (F.π_mem_stabA hx.1) (F.π_mem_stabA hx'.1)
    (fun h => hxN ((F.ker _).mp h)) (fun h => hx'N ((F.ker _).mp h))
    (pi_ne_c2 hCE X h7 Y F hx) (pi_ne_c2 hCE X h7 Y F hx') ?_
  rw [← hmul]
  exact pi_ne_c2 hCE X h7 Y F hxx'

theorem exists_mem_Abar_tau_not_mem (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) {τ : S.O}
    (Y : Hyp10 S g τ) (hτN : τ ∈ Nbar S g t) (hτt : τ ≠ t) :
    ∃ x ∈ S.Lbar g ⊓ Nbar S g τ, x ∉ Nbar S g t := by
  by_contra h
  push Not at h
  have hle : S.Lbar g ⊓ Nbar S g τ ≤ S.Lbar g ⊓ Nbar S g t := fun x hx => ⟨hx.1, h x hx⟩
  have heq : S.Lbar g ⊓ Nbar S g τ = S.Lbar g ⊓ Nbar S g t :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [X.card_Abar, Y.card_Abar])
  have hsub : S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g τ ≤ Vt S g t ⊓ Vt S g τ := by
    intro v hv
    have h1 : v ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (S.Lbar g ⊓ Nbar S g t) := by
      refine ⟨hv.1, fun x hx => ?_⟩
      rw [← heq] at hx
      exact (mem_Nbar.mp hx.2).2 v hv.2
    rw [clSub_inf_fixSub_Abar X] at h1
    exact ⟨h1.2, hv.2⟩
  have h1 := Submodule.finrank_mono hsub
  have h2 := finrank_clSub_inf_Vt Y.H Y.C Y.ht Y.ht1 Y.hVQ
  rw [Y.h4] at h2
  have h3 := finrank_Vt_inf_Vt_le hCE X Y hτN hτt
  omega

end CFSG.LargeExtraspecial.S10
