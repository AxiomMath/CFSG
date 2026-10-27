module

public import CFSG.LargeExtraspecial.AS35ZMLin
public import CFSG.LargeExtraspecial.AS35HSixEightC
public import CFSG.LargeExtraspecial.AS35MKer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions

namespace AS35ZM

theorem braid_of_pow_three {X : Type*} [Group X] {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (h3 : (a * b) ^ 3 = 1) : a * b * a = b * a * b := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have e : a * b * a * (b * a * b) = 1 := by
    rw [← h3]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  calc a * b * a = (b * a * b)⁻¹ := eq_inv_of_mul_eq_one_left e
    _ = b * a * b := by rw [mul_inv_rev, mul_inv_rev, hainv, hbinv, mul_assoc]

end AS35ZM

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

section Pair

variable (hS : S.SixHyp) {r t : G} (hr : r ∈ S.DSet) (ht : t ∈ S.DSet) (hrM : r ∈ S.M)
  (htM : t ∈ S.M)

include hS hr in
theorem rhoL_typeA_ZM : IsTypeA S.q (S.rhoL hrM) 2 :=
  (S.fiveOne_two hS.sixFour hS.weak hr hrM).1

variable (h3 : orderOf (r * t) = 3)

omit hS hr ht in
include h3 in
theorem orderOf_rhoL_mul_ZM : orderOf (S.rhoL hrM * S.rhoL htM) = 3 := by
  rw [← S.rhoL_mul_mem hrM htM]
  exact S.orderOf_rhoL_eq_three _ h3

omit hS hr ht in
include h3 in
theorem rhoL_mul_pow_three_ZM : (S.rhoL hrM * S.rhoL htM) ^ 3 = 1 := by
  rw [← S.orderOf_rhoL_mul_ZM hrM htM h3]
  exact pow_orderOf_eq_one _

include hS hr ht h3 in
theorem commSpace_rt_ZM :
    commSpace (S.rhoL hrM) ⊓ commSpace (S.rhoL htM) = ⊥ ∧
      commSpace (S.rhoL hrM * S.rhoL htM) =
        commSpace (S.rhoL hrM) ⊔ commSpace (S.rhoL htM) ∧
      finrank (ZMod 2) (commSpace (S.rhoL hrM * S.rhoL htM)) = 4 ∧
      commSpace (S.rhoL hrM * S.rhoL htM) ⊓
          LinearMap.BilinForm.orthogonal S.q.polarBilin
            (commSpace (S.rhoL hrM * S.rhoL htM)) = ⊥ ∧
      fixSpace (S.rhoL hrM * S.rhoL htM) = fixSpace (S.rhoL hrM) ⊓ fixSpace (S.rhoL htM) :=
  commSpace_mul_of_orderOf_eq_three S.q_nondegenerate (S.rhoL_typeA_ZM hS hr hrM)
    (S.rhoL_typeA_ZM hS ht htM) (S.orderOf_rhoL_mul_ZM hrM htM h3)

omit hS hr ht in
include h3 in
theorem sup_commSpace_fixSpace_ZM :
    commSpace (S.rhoL hrM * S.rhoL htM) ⊔ fixSpace (S.rhoL hrM * S.rhoL htM) = ⊤ := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hinf :=
    OrthoF2.commSpace_inf_fixSpace_eq_bot_of_pow_three (S.rhoL_mul_pow_three_ZM hrM htM h3)
  have h := Submodule.finrank_sup_add_finrank_inf_eq (commSpace (S.rhoL hrM * S.rhoL htM))
    (fixSpace (S.rhoL hrM * S.rhoL htM))
  rw [hinf, finrank_bot, add_zero, finrank_commSpace_add_finrank_fixSpace] at h
  exact Submodule.eq_top_of_finrank_eq h

section Torus

variable {J : S.Qt ≃ₗ[ZMod 2] S.Qt} (hJ : ∀ v, J (J v) + J v + v = 0)
  (haJ : ∀ v, S.rhoL hrM (J v) = J (S.rhoL hrM v))
  (hbJ : ∀ v, S.rhoL htM (J v) = J (S.rhoL htM v))
  {σ : S.Qt ≃ₗ[ZMod 2] S.Qt} (hσJ : ∀ v, σ (J v) = J (σ v))
  (hσg : ∀ v, σ ((S.rhoL hrM * S.rhoL htM) v) = (S.rhoL hrM * S.rhoL htM) (σ v))
include hS hr ht h3 hJ haJ hbJ hσJ hσg

omit hσJ hσg hJ in
theorem torus_data_ZM :
    (∀ v, S.rhoL hrM (S.rhoL hrM v) = v) ∧
      (∀ v, (S.rhoL hrM * S.rhoL htM) (S.rhoL hrM v) =
        S.rhoL hrM ((S.rhoL hrM * S.rhoL htM) ((S.rhoL hrM * S.rhoL htM) v))) ∧
      (∀ v, (S.rhoL hrM * S.rhoL htM) (J v) = J ((S.rhoL hrM * S.rhoL htM) v)) ∧
      (∀ v, (S.rhoL hrM * S.rhoL htM) ((S.rhoL hrM * S.rhoL htM)
        ((S.rhoL hrM * S.rhoL htM) v)) = v) ∧
      finrank (ZMod 2) (commSpace (S.rhoL hrM * S.rhoL htM)) ≤ 4 := by
  have ha := (S.rhoL_typeA_ZM hS hr hrM).2.2.1
  have hb := (S.rhoL_typeA_ZM hS ht htM).2.2.1
  have h3' := S.rhoL_mul_pow_three_ZM hrM htM h3
  have hbr := AS35ZM.braid_of_pow_three ha hb h3'
  refine ⟨fun v => by rw [← LinearEquiv.mul_apply, ha]; rfl, fun v => ?_, fun v => ?_,
    fun v => ?_, (S.commSpace_rt_ZM hS hr ht hrM htM h3).2.2.1.le⟩
  · simp only [LinearEquiv.mul_apply]
    have e := congrArg (fun f : S.Qt ≃ₗ[ZMod 2] S.Qt => f v) hbr
    simp only [LinearEquiv.mul_apply] at e
    rw [e]
    have e2 : ∀ w, S.rhoL hrM (S.rhoL hrM w) = w := fun w => by
      rw [← LinearEquiv.mul_apply, ha]; rfl
    rw [e2]
  · simp only [LinearEquiv.mul_apply, hbJ, haJ]
  · have e : ((S.rhoL hrM * S.rhoL htM) ^ 3) v = v := by rw [h3']; rfl
    simpa only [pow_succ, pow_zero, one_mul, LinearEquiv.mul_apply] using e

theorem cube_on_commSpace_ZM :
    ∀ w ∈ commSpace (S.rhoL hrM * S.rhoL htM), σ (σ (σ w)) = w := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨haa, hag, hgJ, hg3, hW⟩ := S.torus_data_ZM hS hr ht hrM htM h3 haJ hbJ
  exact AS35ZM.torus_cube haa hag hgJ haJ hJ hg3 hW hσJ hσg

theorem two_elt_on_commSpace_ZM {k : ℕ} (hk : σ ^ (2 ^ k) = 1) :
    ∀ w ∈ commSpace (S.rhoL hrM * S.rhoL htM), σ w = w := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨haa, hag, hgJ, hg3, hW⟩ := S.torus_data_ZM hS hr ht hrM htM h3 haJ hbJ
  exact AS35ZM.torus_two_elt haa hag hgJ haJ hJ hg3 hW hσJ hσg hk

end Torus

end Pair

theorem mbarOddHyp_ZM (hS : S.SixHyp) (h65 : S.SixFiveConcl) {r t : G} (hr : r ∈ S.DSet)
    (ht : t ∈ S.DSet) (h3 : orderOf (r * t) = 3) (hxM : r * t ∈ S.M) : S.MbarOddHyp hxM := by
  intro σ hσ hσx hσC
  have hrM : r ∈ S.M := S.mem_M_of_mem_ESet hS.sixFour hr.1
  have htM : t ∈ S.M := S.mem_M_of_mem_ESet hS.sixFour ht.1
  have hx : S.rhoL hxM = S.rhoL hrM * S.rhoL htM := S.rhoL_mul_mem hrM htM
  obtain ⟨J, hJ, -, hJD, hJM⟩ := h65.fourStruct
  have haJ : ∀ v, S.rhoL hrM (J v) = J (S.rhoL hrM v) := hJD _ (S.ρ_mem_DbarAsc hr hrM)
  have hbJ : ∀ v, S.rhoL htM (J v) = J (S.rhoL htM v) := hJD _ (S.ρ_mem_DbarAsc ht htM)
  set σL : S.Qt ≃ₗ[ZMod 2] S.Qt := (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hσL
  have hσg : ∀ v, σL ((S.rhoL hrM * S.rhoL htM) v) = (S.rhoL hrM * S.rhoL htM) (σL v) := by
    intro v
    have e := congrArg (fun w : S.O => (w : S.Qt ≃ₗ[ZMod 2] S.Qt) v) hσx
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply] at e
    rw [← hx]
    exact e
  have hσC' : ∀ v ∈ fixSpace (S.rhoL hrM * S.rhoL htM), σL v = v := by
    rw [← hx]
    exact hσC
  have hσJ : ∀ v, σL (J v) = J (σL v) := by
    rcases hJM σ hσ with h | h
    · exact h
    · exfalso
      have hfin := (S.fixSpace_rt hS hr ht hrM htM h3).2
      rw [S.rhoL_mul_mem hrM htM] at hfin
      have hw := hS.three_le_width
      have hne : fixSpace (S.rhoL hrM * S.rhoL htM) ≠ ⊥ := by
        intro hbot
        rw [hbot, finrank_bot] at hfin
        omega
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have hJv : J v ∈ fixSpace (S.rhoL hrM * S.rhoL htM) := by
        rw [mem_fixSpace, LinearEquiv.mul_apply] at hv ⊢
        rw [hbJ, haJ, hv]
      have e1 := h v
      rw [hσC' _ hJv, hσC' _ hv] at e1
      exact hv0 (AS35ZM.eq_zero_of_J_eq hJ v (J.injective e1).symm)
  have hW := S.cube_on_commSpace_ZM hS hr ht hrM htM h3 hJ haJ hbJ hσJ hσg
  have htop := S.sup_commSpace_fixSpace_ZM hrM htM h3
  have hcube : σ ^ 3 = 1 := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hv : v ∈ commSpace (S.rhoL hrM * S.rhoL htM) ⊔ fixSpace (S.rhoL hrM * S.rhoL htM) :=
      htop ▸ Submodule.mem_top
    obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
    have e : ((σ ^ 3 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (w + c) = σL (σL (σL (w + c))) := by
      simp only [pow_succ, pow_zero, one_mul, Subgroup.coe_mul, LinearEquiv.mul_apply, hσL]
    rw [e, map_add, map_add, map_add, hW w hw, hσC' c hc, hσC' c hc, hσC' c hc]
    rfl
  have hdvd := orderOf_dvd_of_pow_eq_one hcube
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1 <;> rw [h1] <;> decide

end Setting

end CFSG.LargeExtraspecial
