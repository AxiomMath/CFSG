module

public import CFSG.LargeExtraspecial.AS35TPSym
public import CFSG.LargeExtraspecial.AS35QDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem exists_pbar_iso_YS (hS : S.SixHyp) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet)
    (htM : g * S.z * g⁻¹ ∈ S.M) (W : Submodule (ZMod 2) S.Qt)
    (hW : ∀ m ∈ S.Mbar, ∀ w ∈ W, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W)
    (hWfix : W ≤ fixSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (hWc : W ⊓ commSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥) :
    ∃ Y : Subgroup S.O, Y ≤ S.PbarAsc g ∧ S.ρ ⟨_, htM⟩ ∈ Y ∧ Nat.card Y = 2 * Nat.card W ∧
      (∀ c ∈ S.Mbar, c * S.ρ ⟨_, htM⟩ = S.ρ ⟨_, htM⟩ * c → ∀ y ∈ Y, c * y * c⁻¹ ∈ Y) ∧
      ((∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y) → ∀ w ∈ W, ∀ w' ∈ W, polar S.q w w' = 0) := by
  obtain ⟨k, hk₁, hk₂⟩ := S.exists_swap_J hS ht rfl
  obtain ⟨hi₁, hi₂⟩ := AS35T.swap_inv hk₁ hk₂
  have hK := (S.fiveOne_two hS.sixFour hS.weak ht htM).2.2
  have hWc' : ∀ y ∈ S.clPre W, y ∈ S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G) := by
    intro y hy
    have h1 : S.cl y ∈ S.cqxSub (g * S.z * g⁻¹) := by
      rw [hK]
      exact hWfix (S.mem_clPre.mp hy).2
    rw [← S.clPre_cqxSub htM]
    exact S.mem_clPre.mpr ⟨(S.mem_clPre.mp hy).1, h1⟩
  set V := (S.clPre W).map (MulAut.conj k).toMonoidHom with hV
  have hVmem : ∀ x, x ∈ V ↔ k⁻¹ * x * k ∈ S.clPre W := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro h
      exact ⟨k⁻¹ * x * k, h, by simp [mul_assoc]⟩
  have hVP : V ≤ S.Qa g ⊓ S.M := by
    rintro _ ⟨y, hy, rfl⟩
    exact AS35T.conj_mem_Qa_inf_M_swap hk₁ hk₂ (hWc' y hy)
  have hVM : V ≤ S.M := hVP.trans inf_le_right
  have key : ∀ u ∈ S.QG, k * u * k⁻¹ ∈ S.QG → S.cl u ∈
      commSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    intro u huQ hkuQ
    have h2 : k * u * k⁻¹ ∈ S.QG ⊓ S.Qa g :=
      mem_inf.mpr ⟨hkuQ, AS35T.conj_mem_Qa_of_mem_QG_swap hk₁ huQ⟩
    have h3 := AS35T.conj_mem_inf_Qa_swap hi₁ hi₂ h2
    rw [show k⁻¹ * (k * u * k⁻¹) * k⁻¹⁻¹ = u by group] at h3
    exact AS35T.cl_mem_commSpace_of_mem_inf_Qa hS ht htM h3
  have hVQ : ∀ x ∈ V, x ∈ S.QG → x = 1 := by
    intro x hxV hxQ
    obtain ⟨w, hw, rfl⟩ := hxV
    change k * w * k⁻¹ ∈ S.QG at hxQ
    change k * w * k⁻¹ = 1
    obtain ⟨hwQ, hwW⟩ := S.mem_clPre.mp hw
    have hc := key w hwQ hxQ
    have h0 : S.cl w ∈ W ⊓ commSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨hwW, hc⟩
    rw [hWc, Submodule.mem_bot] at h0
    rcases (S.cl_eq_zero_iff hwQ).mp h0 with rfl | rfl
    · group
    · exfalso
      rw [hk₁] at hxQ
      exact AS35T.rho_t_ne_one hS ht htM ((S.ρ_eq_one_iff _).mpr hxQ)
  refine ⟨(V.subgroupOf S.M).map S.ρ, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, mem_subgroupOf.mpr (hVP (mem_subgroupOf.mp hx)), rfl⟩
  · refine ⟨⟨_, htM⟩, mem_subgroupOf.mpr ?_, rfl⟩
    rw [hVmem]
    change k⁻¹ * (g * S.z * g⁻¹) * k ∈ S.clPre W
    rw [← hk₁, show k⁻¹ * (k * S.z * k⁻¹) * k = S.z by group]
    exact S.z_mem_clPre W
  · have h1 := AS35T.card_map_ρ_mul_card_inf_QG S hVM
    have h2 : Nat.card V = 2 * Nat.card W := by
      rw [hV, Subgroup.card_map_of_injective (MulAut.conj k).injective, S.card_clPre]
    have h3 : Nat.card (V ⊓ S.QG : Subgroup G) = 1 := by
      rw [Subgroup.card_eq_one, eq_bot_iff]
      intro x hx
      exact (Subgroup.mem_bot).mpr (hVQ x (mem_inf.mp hx).1 (mem_inf.mp hx).2)
    rw [h3, mul_one] at h1
    rw [h1, h2]
  · rintro _ ⟨⟨m, hmM⟩, rfl⟩ hmt _ ⟨⟨x, hxM⟩, hx, rfl⟩
    obtain ⟨m', hm'M, hm't, hm'ρ⟩ := S.exists_commute_rho_eq_J hS ht htM hmM hmt
    rw [← hm'ρ]
    have hx' : x ∈ V := mem_subgroupOf.mp hx
    have hmx : m' * x * m'⁻¹ ∈ V := by
      rw [hVmem] at hx' ⊢
      have hm'' : k⁻¹ * m' * k ∈ S.M := by
        have := AS35T.conj_mem_M_of_commute_swap hi₂ hm't
        rwa [inv_inv] at this
      have h1 := AS35T.conj_mem_clPre_of_invariant S hW hm'' hx'
      rwa [show k⁻¹ * m' * k * (k⁻¹ * x * k) * (k⁻¹ * m' * k)⁻¹ =
        k⁻¹ * (m' * x * m'⁻¹) * k by group] at h1
    refine ⟨⟨m', hm'M⟩ * ⟨x, hxM⟩ * ⟨m', hm'M⟩⁻¹, mem_subgroupOf.mpr hmx, ?_⟩
    rw [map_mul, map_mul, map_inv]
  · intro hab w hw w' hw'
    obtain ⟨x, hxQ, rfl⟩ := S.exists_cl w
    obtain ⟨x', hx'Q, rfl⟩ := S.exists_cl w'
    have hxW : x ∈ S.clPre W := S.mem_clPre.mpr ⟨hxQ, hw⟩
    have hx'W : x' ∈ S.clPre W := S.mem_clPre.mpr ⟨hx'Q, hw'⟩
    have hkx : k * x * k⁻¹ ∈ V := ⟨x, hxW, by simp [mul_assoc]⟩
    have hkx' : k * x' * k⁻¹ ∈ V := ⟨x', hx'W, by simp [mul_assoc]⟩
    have hc := hab _ ⟨⟨_, hVM hkx⟩, mem_subgroupOf.mpr hkx, rfl⟩ _
      ⟨⟨_, hVM hkx'⟩, mem_subgroupOf.mpr hkx', rfl⟩
    rw [← map_mul, ← map_mul] at hc
    have hcomm : (k * x * k⁻¹) * (k * x' * k⁻¹) = (k * x' * k⁻¹) * (k * x * k⁻¹) := by
      have hmem : (k * x * k⁻¹) * (k * x' * k⁻¹) * ((k * x' * k⁻¹) * (k * x * k⁻¹))⁻¹ ∈ V :=
        V.mul_mem (V.mul_mem hkx hkx') (V.inv_mem (V.mul_mem hkx' hkx))
      have hker : S.ρ ⟨(k * x * k⁻¹) * (k * x' * k⁻¹) * ((k * x' * k⁻¹) * (k * x * k⁻¹))⁻¹,
          hVM hmem⟩ = 1 := by
        have e : (⟨(k * x * k⁻¹) * (k * x' * k⁻¹) * ((k * x' * k⁻¹) * (k * x * k⁻¹))⁻¹,
            hVM hmem⟩ : S.M) = ⟨k * x * k⁻¹, hVM hkx⟩ * ⟨k * x' * k⁻¹, hVM hkx'⟩ *
              (⟨k * x' * k⁻¹, hVM hkx'⟩ * ⟨k * x * k⁻¹, hVM hkx⟩)⁻¹ := rfl
        rw [e, map_mul, map_inv, hc, mul_inv_cancel]
      have h1 := hVQ _ hmem ((S.ρ_eq_one_iff _).mp hker)
      exact mul_inv_eq_one.mp h1
    have hxx : x * x' = x' * x := by
      have e1 : (k * x * k⁻¹) * (k * x' * k⁻¹) = k * (x * x') * k⁻¹ := by group
      have e2 : (k * x' * k⁻¹) * (k * x * k⁻¹) = k * (x' * x) * k⁻¹ := by group
      rw [e1, e2] at hcomm
      have := congrArg (fun y => k⁻¹ * y * k) hcomm
      simpa [mul_assoc] using this
    by_contra hne
    have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    exact ((S.polar_cl_eq_one_iff hxQ hx'Q).mp ((h01 _).resolve_left hne)) hxx

end Setting

end CFSG.LargeExtraspecial
