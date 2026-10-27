module

public import CFSG.LargeExtraspecial.S10SixD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem qf_act_sub_of_a2 : ∀ γ : Gm, act γ E00 = E00 → γ ≠ τ₁ * τ₂ →
    ∀ m : M2, qf (act γ m - m) = 0 := by
  decide +kernel

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_point_of_mem_inf (hCE : CentralExtInput.{u}) {t τ : S.O} (X : Hyp10 S g t)
    (Y : Hyp10 S g τ) (h7 : 7 ≤ S.width) (htN : t ∈ Nbar S g τ) (htτ : t ≠ τ) {v : S.Qt}
    (hv : v ∈ Vt S g t ⊓ Vt S g τ) (hv0 : v ≠ 0) :
    ∃ k : S.M, ∃ _ : S.ρ k ∈ Rbar S g τ,
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) = v := by
  obtain ⟨z, hz, hzN⟩ := exists_mem_Abar_tau_not_mem hCE Y X htN htτ
  obtain ⟨F⟩ := Y.exists_frame
  obtain ⟨k, hk, -, hb⟩ := X.exists_pair
  have hNX := (timmesfeld_10_1_two hCE X hk hb).2.2.2.2
  have hVW := Vt_le_Wt_of_mem_Nbar X htN
  have hD : (Vt S g τ).map (((z : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ≤
      Vt S g τ ⊓ Vt S g t := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨sub_mem (apply_mem_Vt_of_mem_Rbar Y.haQ (Lbar_le_Rbar Y.ht hz.1) hw) hw,
      hNX z hz.2 w (hVW hw)⟩
  have hDeq : (Vt S g τ).map (((z : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) =
      Vt S g τ ⊓ Vt S g t := by
    refine Submodule.eq_of_le_of_finrank_le hD ?_
    rw [finrank_map_Vt_of_Lbar Y hz.1 hzN]
    exact finrank_Vt_inf_Vt_le hCE Y X htN htτ
  have hv' : v ∈ Vt S g τ ⊓ Vt S g t := ⟨hv.2, hv.1⟩
  rw [← hDeq] at hv'
  obtain ⟨w, hw, rfl⟩ := hv'
  have hzR := Lbar_le_Rbar Y.ht hz.1
  have hsing : qf (F.φ ⟨_, hD ⟨w, hw, rfl⟩ |>.1⟩) = 0 := by
    have e : F.φ ⟨_, hD ⟨w, hw, rfl⟩ |>.1⟩ =
        act (F.π ⟨z, hzR⟩) (F.φ ⟨w, hw⟩) - F.φ ⟨w, hw⟩ := by
      rw [← F.compat', ← map_sub]
      congr 1
    rw [e]
    exact qf_act_sub_of_a2 _ (F.π_mem_stabA hz.1) (pi_ne_c2 hCE Y h7 X F hz) _
  have hne : (⟨_, hD ⟨w, hw, rfl⟩ |>.1⟩ : Vt S g τ) ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  have horb := (F.sing _ hne).mpr hsing
  rw [mem_orbitOf_RmodN_iff Y.haQ Y.ht] at horb
  obtain ⟨r, hr, hrv⟩ := horb
  obtain ⟨k', hk'⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hr)
  refine ⟨k', hk' ▸ hr, ?_⟩
  rw [← ρ_cl_conj_z S k' Y.haQ, hk']
  exact hrv.symm

end CFSG.LargeExtraspecial.S10
