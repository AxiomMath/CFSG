module

public import CFSG.LargeExtraspecial.AS35TPbar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem zGen_eq_top_of_fixSpace (hS : S.SixHyp)
    (h : ∀ v : S.Qt, (∀ m ∈ S.Mbar, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → v = 0) :
    S.zGen = ⊤ := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hN : S.zGen.Normal := S.zGen_normal
  set W := S.clSub (S.QG ⊓ S.zGen) with hW
  have hcomm : ∀ m ∈ S.Mbar, ∀ v : S.Qt, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ W := by
    rintro _ ⟨⟨m, hmM⟩, rfl⟩ v
    obtain ⟨x, hx, rfl⟩ := S.exists_cl v
    have hm : m ∈ S.zGen ⊔ S.QG := by
      rw [hS.sup_eq_top]
      exact mem_top m
    obtain ⟨n, hn, q, hq, rfl⟩ := mem_sup_of_normal_left.mp hm
    have hqM := S.QG_le_M hq
    have hnM : n ∈ S.M := by
      have h1 := S.M.mul_mem hmM (S.M.inv_mem hqM)
      rwa [mul_inv_cancel_right] at h1
    have hρ : S.ρ ⟨n * q, hmM⟩ = S.ρ ⟨n, hnM⟩ := by
      have e : (⟨n * q, hmM⟩ : S.M) = ⟨n, hnM⟩ * ⟨q, hqM⟩ := rfl
      rw [e, map_mul, (S.ρ_eq_one_iff ⟨q, hqM⟩).mpr hq, mul_one]
    rw [hρ, S.ρ_cl ⟨n, hnM⟩ hx]
    have h1 : n * x * n⁻¹ * x⁻¹ ∈ S.QG ⊓ S.zGen := by
      refine mem_inf.mpr ⟨S.QG.mul_mem (S.conj_mem_QG hnM hx) (S.QG.inv_mem hx), ?_⟩
      rw [show n * x * n⁻¹ * x⁻¹ = n * (x * n⁻¹ * x⁻¹) by group]
      exact S.zGen.mul_mem hn (hN.conj_mem _ (S.zGen.inv_mem hn) x)
    have h2 := S.cl_mem_clSub h1 (mem_inf.mp h1).1
    rw [S.cl_mul (S.conj_mem_QG hnM hx) (S.QG.inv_mem hx), S.cl_inv hx] at h2
    change S.cl (n * x * n⁻¹) - S.cl x ∈ W
    rwa [sub_eq_add_vec (ZMod 2)]
  have hperp : LinearMap.BilinForm.orthogonal S.q.polarBilin W = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Submodule.mem_bot]
    apply h u
    intro m hm
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hu
    have hm' : m⁻¹ ∈ S.Mbar := S.Mbar.inv_mem hm
    have hrad : ∀ w, polar S.q ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) w = 0 := by
      intro w
      set σ : S.Qt ≃ₗ[ZMod 2] S.Qt := (m : S.Qt ≃ₗ[ZMod 2] S.Qt) with hσ
      set σ' : S.Qt ≃ₗ[ZMod 2] S.Qt := ((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hσ'
      have h1 := hu _ (hcomm _ hm' w)
      change polar S.q (σ' w - w) u = 0 at h1
      have h2 : polar S.q (σ u) (σ (σ' w)) = polar S.q u (σ' w) :=
        TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup m.2 _ _
      have h3 : σ (σ' w) = w := by
        change ((m * m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w
        rw [mul_inv_cancel]
        rfl
      rw [h3] at h2
      rw [QuadraticMap.polar_sub_left, h2, polar_comm S.q u, polar_comm S.q u,
        ← QuadraticMap.polar_sub_left, h1]
    have h0 := S.q_nondegenerate.1 _ (fun w => by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hrad w)
    exact sub_eq_zero.mp h0
  have hWtop : W = ⊤ := by
    rw [← LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl W,
      hperp]
    exact LinearMap.BilinForm.orthogonal_bot
  have hQ : S.QG ≤ S.zGen := by
    intro x hx
    have h1 : S.cl x ∈ W := by
      rw [hWtop]
      exact Submodule.mem_top
    obtain ⟨y, hy, -, hyx⟩ := S.mem_clSub_iff.mp h1
    obtain ⟨hyQ, hyN⟩ := mem_inf.mp hy
    rcases (S.cl_eq_cl_iff hyQ hx).mp hyx with rfl | rfl
    · exact hyN
    · exact S.zGen.mul_mem hyN S.z_mem_zGen
  rw [← hS.sup_eq_top, sup_of_le_left hQ]

namespace AS35T

theorem conj_mem_clPre_of_invariant {W : Submodule (ZMod 2) S.Qt}
    (hW : ∀ m ∈ S.Mbar, ∀ w ∈ W, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W) {m : G} (hm : m ∈ S.M)
    {y : G} (hy : y ∈ S.clPre W) : m * y * m⁻¹ ∈ S.clPre W := by
  obtain ⟨hyQ, hyW⟩ := S.mem_clPre.mp hy
  refine S.mem_clPre.mpr ⟨S.conj_mem_QG hm hyQ, ?_⟩
  rw [← S.ρ_cl ⟨m, hm⟩ hyQ]
  exact hW _ ⟨⟨m, hm⟩, rfl⟩ _ hyW

theorem exists_pbar_sub_of_fixSpace (hS : S.SixHyp) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet)
    (htM : g * S.z * g⁻¹ ∈ S.M) (W : Submodule (ZMod 2) S.Qt)
    (hW : ∀ m ∈ S.Mbar, ∀ w ∈ W, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W)
    (hWfix : W ≤ fixSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (hWc : ¬ W ≤ commSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    ∃ Y : Subgroup S.O, Y ≤ ((S.Qa g ⊓ S.M).subgroupOf S.M).map S.ρ ∧ S.ρ ⟨_, htM⟩ ∈ Y ∧
      ¬ Y ≤ zpowers (S.ρ ⟨_, htM⟩) ∧ Nat.card Y ≤ 2 * Nat.card W ∧
      ∀ c ∈ S.Mbar, c * S.ρ ⟨_, htM⟩ = S.ρ ⟨_, htM⟩ * c → ∀ y ∈ Y, c * y * c⁻¹ ∈ Y := by
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
  refine ⟨(V.subgroupOf S.M).map S.ρ, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, mem_subgroupOf.mpr (hVP (mem_subgroupOf.mp hx)), rfl⟩
  · refine ⟨⟨_, htM⟩, mem_subgroupOf.mpr ?_, rfl⟩
    rw [hVmem]
    change k⁻¹ * (g * S.z * g⁻¹) * k ∈ S.clPre W
    rw [← hk₁, show k⁻¹ * (k * S.z * k⁻¹) * k = S.z by group]
    exact S.z_mem_clPre W
  · intro hle
    obtain ⟨v, hvW, hvc⟩ := Set.not_subset.mp hWc
    obtain ⟨w, hwQ, rfl⟩ := S.exists_cl v
    have hwW : w ∈ S.clPre W := S.mem_clPre.mpr ⟨hwQ, hvW⟩
    have hkw : k * w * k⁻¹ ∈ V := ⟨w, hwW, by simp [mul_assoc]⟩
    have hkwM := hVM hkw
    have h1 := hle ⟨⟨_, hkwM⟩, mem_subgroupOf.mpr hkw, rfl⟩
    rw [mem_zpowers_iff_of_mul_self (AS35T.rho_t_mul_self ht htM)] at h1
    have key : ∀ u ∈ S.QG, k * u * k⁻¹ ∈ S.QG → S.cl u ∈
        commSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      intro u huQ hkuQ
      have h2 : k * u * k⁻¹ ∈ S.QG ⊓ S.Qa g :=
        mem_inf.mpr ⟨hkuQ, AS35T.conj_mem_Qa_of_mem_QG_swap hk₁ huQ⟩
      have h3 := AS35T.conj_mem_inf_Qa_swap hi₁ hi₂ h2
      rw [show k⁻¹ * (k * u * k⁻¹) * k⁻¹⁻¹ = u by group] at h3
      exact AS35T.cl_mem_commSpace_of_mem_inf_Qa hS ht htM h3
    rcases h1 with h1 | h1
    · exact hvc (key w hwQ ((S.ρ_eq_one_iff _).mp h1))
    · apply hvc
      rw [← S.cl_mul_z hwQ]
      have h2 : S.ρ ⟨k * w * k⁻¹ * (g * S.z * g⁻¹), S.M.mul_mem hkwM htM⟩ = 1 := by
        have e : (⟨k * w * k⁻¹ * (g * S.z * g⁻¹), S.M.mul_mem hkwM htM⟩ : S.M) =
            ⟨k * w * k⁻¹, hkwM⟩ * ⟨_, htM⟩ := rfl
        rw [e, map_mul, h1, AS35T.rho_t_mul_self ht htM]
      have h3 := (S.ρ_eq_one_iff _).mp h2
      have e : k * (w * S.z) * k⁻¹ = k * w * k⁻¹ * (g * S.z * g⁻¹) := by
        rw [← hk₁]
        group
      exact key _ (S.QG.mul_mem hwQ S.z_mem_QG) (e ▸ h3)
  · have h1 := AS35T.card_map_ρ_mul_card_inf_QG S hVM
    have h2 : Nat.card V = 2 * Nat.card W := by
      rw [hV, Subgroup.card_map_of_injective (MulAut.conj k).injective, S.card_clPre]
    have h3 : 0 < Nat.card (V ⊓ S.QG : Subgroup G) := Nat.card_pos
    rw [← h2, ← h1]
    exact Nat.le_mul_of_pos_right _ h3
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

end AS35T

end Setting

end CFSG.LargeExtraspecial
