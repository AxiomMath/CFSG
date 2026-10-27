module

public import CFSG.LargeExtraspecial.S10SixK
public import CFSG.LargeExtraspecial.S10Five
public import CFSG.LargeExtraspecial.S10SixE
public import CFSG.LargeExtraspecial.S10SixF
public import CFSG.LargeExtraspecial.S10SixH

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem false_of_noFix_frame
    (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (h7 : 7 ≤ S.width)
    (hno : ∀ x ∈ S.Lbar g, x ∉ Nbar S g t → x ∉ fixWstar X) (F : Frame X) {k : S.M}
    (hk : S.ρ k ∈ normalizer (S.Lbar g : Set S.O)) {τ : S.O}
    (hτ : τ = S.ρ k * t * (S.ρ k)⁻¹) (hτN : τ ∈ Nbar S g t) (hτt : τ ≠ t) {x₁ : S.O}
    (hx₁ : x₁ ∈ S.Lbar g ⊓ Nbar S g τ) (hx₁N : x₁ ∉ Nbar S g t)
    (hπx₁ : F.π ⟨x₁, Lbar_le_Rbar X.ht hx₁.1⟩ = τ₁) : False := by
  have Y := X.conj' hk hτ
  have htN := t_mem_Nbar_of_noFix X hno hk hτ Y
  obtain ⟨k', hk'R, hπk', x, hxL, hxc, hπx⟩ := exists_mem_Lbar_inf_conj hCE X F
  have hxR := Lbar_le_Rbar X.ht hxL
  have hxN : x ∉ Nbar S g t := fun h => τ₁_ne_one (hπx.symm.trans ((F.ker _).mpr h))
  obtain ⟨h, hhN, hhτ⟩ := exists_conj_eq_mul_t hCE X hk hτ hτN hτt
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar (Nbar_le_Rbar hhN))
  have hx₁R := Lbar_le_Rbar X.ht hx₁.1
  have hxx : x₁⁻¹ * x ∈ Nbar S g t := by
    refine (F.ker ⟨x₁⁻¹ * x, mul_mem (inv_mem hx₁R) hxR⟩).mp ?_
    have e : (⟨x₁⁻¹ * x, mul_mem (inv_mem hx₁R) hxR⟩ : Rbar S g t) =
        (⟨x₁, hx₁R⟩ : Rbar S g t)⁻¹ * ⟨x, hxR⟩ := Subtype.ext (by simp)
    rw [e, map_mul, map_inv, hπx₁, hπx, inv_mul_cancel]
  have hmN : S.ρ m ∈ Nbar S g t := by rw [hm]; exact hhN
  have hmτ : S.ρ m * τ * (S.ρ m)⁻¹ = τ * t := by rw [hm]; exact hhτ
  apply hno x hxL hxN
  refine mem_fixWstar_of_finrank_le X hxL hxN ?_
  rcases mem_Nbar_or hCE X h7 hk hτ hmN hmτ hx₁ hx₁N hxL hxx with hxτ | hxτt
  · exact finrank_le_four_of_config hCE X h7 F Y hτN htN hτt.symm hk'R hπk' hxL hxc hxτ hπx
  ·
    have hmL : S.ρ m ∈ normalizer (S.Lbar g : Set S.O) :=
      Nbar_le_normalizer X.haQ X.H.conj_ne (Lbar_mem_Dset X.ht) hmN
    have hkm : S.ρ (m * k) ∈ normalizer (S.Lbar g : Set S.O) := by
      rw [map_mul]
      exact mul_mem hmL hk
    have hτ' : τ * t = S.ρ (m * k) * t * (S.ρ (m * k))⁻¹ := by
      rw [map_mul, mul_inv_rev, ← hmτ, hτ]
      group
    have Y' := X.conj' hkm hτ'
    have htN' := t_mem_Nbar_of_noFix X hno hkm hτ' Y'
    have hτtN : τ * t ∈ Nbar S g t := mul_mem hτN (self_mem_Nbar X.H X.ht)
    have hτtt : t ≠ τ * t := fun h => X.ht1 (by
      have := Y.ht1
      have e : τ = 1 := by
        calc τ = τ * t * t⁻¹ := by group
          _ = t * t⁻¹ := by rw [← h]
          _ = 1 := mul_inv_cancel t
      exact absurd e this)
    exact finrank_le_four_of_config hCE X h7 F Y' hτtN htN' hτtt hk'R hπk' hxL hxc hxτt hπx

theorem exists_mem_fixWstar
    (hCE : CentralExtInput.{u}) (X : Hyp10 S g t)
    (h104 : ∃ k : S.M, S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar g ∧ S.ρ k * t * (S.ρ k)⁻¹ ≠ t)
    (h7 : 7 ≤ S.width) : ∃ x ∈ S.Lbar g, x ∉ Nbar S g t ∧ x ∈ fixWstar X := by
  by_contra hfix
  push Not at hfix
  have hno : ∀ x ∈ S.Lbar g, x ∉ Nbar S g t → x ∉ fixWstar X := fun x hx hxN => hfix x hx hxN
  rcases timmesfeld_10_5 hCE X h104 with h6 | ⟨k, hk, hτA, hτt⟩
  · omega
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = S.ρ k * t * (S.ρ k)⁻¹ := ⟨_, rfl⟩
  rw [← hτ] at hτA hτt
  have Y := X.conj' hk hτ
  obtain ⟨x₁, hx₁, hx₁N⟩ := exists_mem_Abar_tau_not_mem hCE X Y hτA.2 hτt
  obtain ⟨F⟩ := X.exists_frame
  have hst := F.π_mem_stabA hx₁.1
  rw [mem_stabA, act_E00_iff] at hst
  rcases hst with h | h | h | h
  · exact hx₁N ((F.ker _).mp h)
  · exact false_of_noFix_frame hCE X h7 hno F hk hτ hτA.2 hτt hx₁ hx₁N h
  · refine false_of_noFix_frame hCE X h7 hno F.swap hk hτ hτA.2 hτt hx₁ hx₁N ?_
    rw [F.swap_π, h, τ₂_swap]
  · exact pi_ne_c2 hCE X h7 Y F hx₁ h

end CFSG.LargeExtraspecial.S10
