module

public import CFSG.LargeExtraspecial.AS35YUSpK
public import CFSG.LargeExtraspecial.AS35YUSpY

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions
  CFSG.ClassicalGroups.Orthogonal AS35YR

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem conj_mem_PbarL_of_mem_YU (hS : S.SixHyp) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet)
    (htM : g * S.z * g⁻¹ ∈ S.M) {F : Frame S.q}
    (hFt : ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = F.t) {s : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup S.q) (hsL : (⟨s, hs⟩ : S.O) ∈ S.LbarAsc)
    (hst : s * F.t = F.t * s) : ∀ p ∈ S.PbarL_YR g, s * p * s⁻¹ ∈ S.PbarL_YR g := by
  obtain ⟨-, -, -, -, hnorm, -, -⟩ := S14.asc512PbarStmt G S hS g ht htM
  intro p hp
  obtain ⟨x, hx, rfl⟩ := hp
  have hst' : (⟨s, hs⟩ : S.O) * S.ρ ⟨_, htM⟩ = S.ρ ⟨_, htM⟩ * ⟨s, hs⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hFt]
    exact hst
  exact ⟨_, hnorm _ (LbarAsc_le_Mbar_YL hsL) hst' x hx, rfl⟩

theorem radHyp_odd_YU (hS : S.SixHyp) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet)
    (htM : g * S.z * g⁻¹ ∈ S.M) (F : Frame S.q)
    (hFℓ : commSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = F.ell)
    (hFt : ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = F.t)
    (hs₁ : (⟨F.s₁, F.s₁_mem⟩ : S.O) ∈ S.LbarAsc) (hs₂ : (⟨F.s₂, F.s₂_mem⟩ : S.O) ∈ S.LbarAsc) :
    F.RadHyp (S.PbarL_YR g) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨-, -, -, hcent, -, hcomm, hfix⟩ := S14.asc512PbarStmt G S hS g ht htM
  have hA : IsTypeA S.q ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 :=
    (S.fiveOne_two hS.sixFour hS.weak ht htM).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, hcomm x hx F.a (hFℓ ▸ F.a_mem_ell), hcomm x hx F.b (hFℓ ▸ F.b_mem_ell), ?_⟩
    intro v ha hb
    have hv : v ∈ fixSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [fixSpace_eq_orthogonal_commSpace S.q_nondegenerate (S.ρ ⟨_, htM⟩).2 hA.2.2.1, hFℓ,
        OrthoF2.mem_orthogonal_iff_polar]
      intro u hu
      obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hu
      rw [polar_add_right, polar_smul_right, polar_smul_right, ha, hb]
      simp
    have := hfix x hx v hv
    rwa [hFℓ] at this
  · exact conj_mem_PbarL_of_mem_YU hS ht htM hFt F.s₁_mem hs₁ (F.s₁_comm S.q_nondegenerate)
  · exact conj_mem_PbarL_of_mem_YU hS ht htM hFt F.s₂_mem hs₂ (F.s₂_comm S.q_nondegenerate)
  · rintro _ ⟨x, hx, rfl⟩ hcen
    have hcen' : ∀ y ∈ S.PbarAsc g, x * y = y * x := by
      intro y hy
      exact Subtype.ext (hcen _ ⟨y, hy, rfl⟩)
    rcases hcent x hx hcen' with h | h
    · left
      rw [h]
      rfl
    · right
      rw [h]
      exact hFt

theorem false_of_odd_psp_YU (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc) {m : ℕ} (hm : 4 ≤ m)
    (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSp m 2 1)
    (hdim : finrank (ZMod 2) (commU_YS S) = 2 * m + 1) {r : S.Qt} (hrW : r ∈ fixW_YS S)
    (hrU : r ∈ commU_YS S) (hr : S.q r = 1)
    (hR : ∀ v ∈ fixW_YS S, v ∈ commU_YS S → v = 0 ∨ v = r) : False := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have : Finite (S.Qt ≃ₗ[ZMod 2] S.Qt) := finite_linearEquiv_YR
  have hK : ∀ {s : S.Qt ≃ₗ[ZMod 2] S.Qt} (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup S.q),
      (∀ w ∈ fixW_YS S, s w = w) → Even (finrank (ZMod 2) (commSpace s)) →
        (⟨s, hs⟩ : S.O) ∈ S.LbarAsc := fun hs hsW heven =>
    mem_LbarAsc_of_odd_psp_YU hS hst hnd hL hdim hrW hrU hr hR hs hsW heven
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := AS35YL.nontrivial_of_inspNondeg_YL hnd
  obtain ⟨t₀, ht₀⟩ := DbarAsc_nonempty_YL (S := S)
  have ht₀L : t₀ ∈ S.LbarAsc := subset_closure ht₀
  obtain ⟨t, ht, htM, rfl⟩ := ht₀
  obtain ⟨g, rfl⟩ := isConj_iff.mp (S.isConj_of_mem_ESet ht.1)
  obtain ⟨F₀, hFℓ, hFt⟩ := exists_frame_YR hS ht htM
  have hℓU := commSpace_le_commU_YS ht₀L
  have haU : F₀.a ∈ commU_YS S := hℓU (hFℓ ▸ F₀.a_mem_ell)
  have hbU : F₀.b ∈ commU_YS S := hℓU (hFℓ ▸ F₀.b_mem_ell)
  have hrperp : ∀ u ∈ commU_YS S, polar S.q u r = 0 := fun u hu => mem_commU_YS.mp hu r hrW
  have hrad : ∀ x ∈ commU_YS S, (∀ u ∈ commU_YS S, polar S.q x u = 0) → x = 0 ∨ x = r :=
    fun x hx hperp => hR x (mem_fixW_of_mem_radU_YS hperp) hx
  obtain ⟨c, hcU, c', hc'U, hcq, hc'q, hac, hbc, hac', hbc', hcc'⟩ :=
    exists_frame_in_YU hr hrU hrperp hrad haU hbU F₀.qa F₀.qb F₀.ab F₀.a_ne_zero F₀.b_ne_zero
      F₀.a_ne_b
  let F : Frame S.q := ⟨F₀.a, F₀.b, c, c', F₀.qa, F₀.qb, hcq, hc'q, F₀.ab, hac, hbc, hac', hbc',
    hcc'⟩
  have hFℓ' : commSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = F.ell := hFℓ
  have hFt' : ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = F.t := hFt
  have hpw : ∀ {u : S.Qt}, u ∈ commU_YS S → ∀ w ∈ fixW_YS S, polar S.q w u = 0 := by
    intro u hu w hw
    rw [polar_comm]
    exact mem_commU_YS.mp hu w hw
  have hs₁W : ∀ w ∈ fixW_YS S, F.s₁ w = w := fun w hw => by
    rw [Frame.s₁_apply, hpw haU w hw, hpw hcU w hw, zero_smul, zero_smul, add_zero, add_zero]
  have hs₂W : ∀ w ∈ fixW_YS S, F.s₂ w = w := fun w hw => by
    rw [Frame.s₂_apply, hpw hbU w hw, hpw hc'U w hw, zero_smul, zero_smul, add_zero, add_zero]
  have hrad' := radHyp_odd_YU hS ht htM F hFℓ' hFt'
    (hK F.s₁_mem hs₁W (F.even_finrank_commSpace_s₁ S.q_nondegenerate))
    (hK F.s₂_mem hs₂W (F.even_finrank_commSpace_s₂ S.q_nondegenerate))
  have hPU : ∀ p ∈ S.PbarL_YR g, ∀ u ∈ commU_YS S, p u ∈ commU_YS S := by
    rintro _ ⟨x, hx, rfl⟩ u hu
    obtain ⟨y, -, rfl⟩ := hx
    exact commU_YS_invariant hst ⟨y, rfl⟩ hu
  have hrX : r ∈ F.Xp := Frame.RadHyp.mem_Xp_of_perp_YU hrperp haU hbU hcU hc'U
  have hnorm : ∀ v ∈ commU_YS S, v ∈ F.Xp → ∀ hv : S.q v = 1, ∀ p ∈ S.PbarL_YR g,
      (refl1 S.q v hv * refl1 S.q r hr) * p * (refl1 S.q v hv * refl1 S.q r hr)⁻¹ ∈
        S.PbarL_YR g := by
    intro v hvU hvX hv
    obtain ⟨ha, hb, -, -⟩ := Frame.refl1_fix hvX hv
    obtain ⟨ha', hb', -, -⟩ := Frame.refl1_fix hrX hr
    have hmem := mul_mem (refl1_mem hv) (refl1_mem hr)
    have hsW : ∀ w ∈ fixW_YS S, (refl1 S.q v hv * refl1 S.q r hr) w = w := fun w hw => by
      rw [LinearEquiv.mul_apply, refl1_apply hr, hpw hrU w hw, zero_smul, add_zero,
        refl1_apply, hpw hvU w hw, zero_smul, add_zero]
    exact conj_mem_PbarL_of_mem_YU hS ht htM hFt' hmem
      (hK hmem hsW (even_finrank_commSpace_refl1_mul S.q_nondegenerate hv hr))
      (F.comm_t_of_fix_YU S.q_nondegenerate hmem (by rw [LinearEquiv.mul_apply, ha', ha])
        (by rw [LinearEquiv.mul_apply, hb', hb]))
  have hcard : 2 < Nat.card (S.PbarL_YR g) := by
    rw [card_PbarL_YR hS ht htM]
    have := hS.three_le_width
    calc 2 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * S.width - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact hrad'.false_of_odd_YU S.q_nondegenerate hcard hPU haU hbU hcU hc'U hr hrU hrperp hnorm
    (by omega)

end Setting

end CFSG.LargeExtraspecial
