module

public import CFSG.LargeExtraspecial.AS35ZMFrame
public import CFSG.LargeExtraspecial.AS35ZMSemi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions

namespace AS35ZM

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {J : V ≃ₗ[ZMod 2] V}

theorem comm_linear (hJ : ∀ v, J (J v) + J v + v = 0) {s w : V ≃ₗ[ZMod 2] V}
    (hs : ∀ v, s (J v) = J (J (s v))) (hw : ∀ v, w (J v) = J (w v)) (v : V) :
    (s * w * s⁻¹ * w⁻¹) (J v) = J ((s * w * s⁻¹ * w⁻¹) v) := by
  have hww : ∀ x, w (w⁻¹ x) = x := fun x => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  have hss : ∀ x, s (s⁻¹ x) = x := fun x => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  have hwi : ∀ v, w⁻¹ (J v) = J (w⁻¹ v) := fun v => by
    apply w.injective
    rw [hw, hww, hww]
  have hsi : ∀ v, s⁻¹ (J v) = J (J (s⁻¹ v)) := fun v => by
    apply s.injective
    rw [hs, hs, hss, hss, J_J_J hJ]
  simp only [LinearEquiv.mul_apply]
  rw [hwi, hsi, hw, hw, hs, hs, J_J_J hJ]

end AS35ZM

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

section Pair

variable (hS : S.SixHyp) (h65 : S.SixFiveConcl) {r t : G} (hr : r ∈ S.DSet) (ht : t ∈ S.DSet)
  (hrM : r ∈ S.M) (htM : t ∈ S.M) (h3 : orderOf (r * t) = 3)
  {J : S.Qt ≃ₗ[ZMod 2] S.Qt} (hJ : ∀ v, J (J v) + J v + v = 0)
  (hJq : ∀ v, S.q (J v) = S.q v)
  (hJD : ∀ a ∈ S.DbarAsc, ∀ v, (a : S.Qt ≃ₗ[ZMod 2] S.Qt) (J v) = J ((a : S.Qt ≃ₗ[ZMod 2] S.Qt) v))
  {R : Subgroup S.O} (hRM : R ≤ S.Mbar) (hxM : r * t ∈ S.M)
  (hRx : ∀ σ ∈ R, σ * S.ρ ⟨r * t, hxM⟩ = S.ρ ⟨r * t, hxM⟩ * σ)
  (hRn : ∀ τ ∈ S.Mbar, τ * S.ρ ⟨r * t, hxM⟩ = S.ρ ⟨r * t, hxM⟩ * τ → ∀ σ ∈ R, τ * σ * τ⁻¹ ∈ R)
  (hR2 : IsPGroup 2 R)
include hS h65 hr ht hrM htM h3 hJ hJq hJD hRM hRx hRn hR2

theorem not_semilinear_ZM {k : ℕ} (hk : S.width = k + 2) {σ : S.O} (hσ : σ ∈ R)
    (hσJ : ∀ v, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) (J v) = J (J ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v))) :
    False := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hnc := S.rho_not_commute_ZM hr ht hrM htM h3
  obtain ⟨-, -, e, he, d, hd, hda, hdb, hy, hya, hyd⟩ := S.pg_data_ZM h65 hk
    (S.ρ_mem_DbarAsc hr hrM) (S.ρ_mem_DbarAsc ht htM) hnc
  set a := S.ρ ⟨r, hrM⟩ with ha
  set b := S.ρ ⟨t, htM⟩ with hb
  set e₂ := a * b * e * (a * b)⁻¹ with he₂
  set y := e * e₂ with hydef
  have hX : S.ρ ⟨r * t, hxM⟩ = a * b := S.rho_mul_ZM hrM htM hxM
  have habM : a * b ∈ S.Mbar := S.Mbar.mul_mem
    (S.mem_Mbar_of_mem_DbarAsc_ZM (S.ρ_mem_DbarAsc hr hrM))
    (S.mem_Mbar_of_mem_DbarAsc_ZM (S.ρ_mem_DbarAsc ht htM))
  have he₂D : e₂ ∈ S.DbarAsc := S.conj_mem_DbarAsc_L habM he
  have hyM : y ∈ S.Mbar := S.Mbar.mul_mem (S.mem_Mbar_of_mem_DbarAsc_ZM he)
    (S.mem_Mbar_of_mem_DbarAsc_ZM he₂D)
  have hyX : y * S.ρ ⟨r * t, hxM⟩ = S.ρ ⟨r * t, hxM⟩ * y := by rw [hX]; exact hy
  have hyJ : ∀ v, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (J v) = J ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
    intro v
    rw [hydef, Subgroup.coe_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hJD _ he₂D,
      hJD _ he]
  have hcR := S.comm_mem_ZM hxM hRn hσ hyM hyX
  have hcJ : ∀ v, ((σ * y * σ⁻¹ * y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (J v) =
      J (((σ * y * σ⁻¹ * y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
    intro v
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact AS35ZM.comm_linear hJ hσJ hyJ v
  have hc1 := S.eq_one_of_linear_ZM hS h65 hr ht hrM htM h3 hJ hJq hJD hRM hxM hRx hRn hR2 hk
    hcR hcJ
  have hσy : σ * y = y * σ := by
    calc σ * y = σ * y * σ⁻¹ * y⁻¹ * (y * σ) := by group
      _ = y * σ := by rw [hc1, one_mul]
  have hσyL : ∀ v, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := fun v => by
    have := congrArg (fun w : S.O => (w : S.Qt ≃ₗ[ZMod 2] S.Qt) v) hσy
    simpa only [Subgroup.coe_mul, LinearEquiv.mul_apply] using this
  have hσg := S.linear_of_mem_ZM hrM htM hxM hRx hσ
  have hyg : ∀ v, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((S.rhoL hrM * S.rhoL htM) v) =
      (S.rhoL hrM * S.rhoL htM) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := fun v => by
    have e := congrArg (fun w : S.O => (w : S.Qt ≃ₗ[ZMod 2] S.Qt) v) hyX
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply] at e
    rw [← S.rhoL_mul_mem hrM htM]
    exact e
  have hgO : S.rhoL hrM * S.rhoL htM ∈ TauCeti.QuadraticMap.orthogonalGroup S.q := (a * b).2
  have hgJ : ∀ v, (S.rhoL hrM * S.rhoL htM) (J v) = J ((S.rhoL hrM * S.rhoL htM) v) := by
    intro v
    have h1 : S.rhoL htM (J v) = J (S.rhoL htM v) := hJD _ (S.ρ_mem_DbarAsc ht htM) v
    have h2 : ∀ w, S.rhoL hrM (J w) = J (S.rhoL hrM w) := hJD _ (S.ρ_mem_DbarAsc hr hrM)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h1, h2]
  have hg3 : ∀ v, (S.rhoL hrM * S.rhoL htM) ((S.rhoL hrM * S.rhoL htM)
      ((S.rhoL hrM * S.rhoL htM) v)) = v := by
    intro v
    have e : ((S.rhoL hrM * S.rhoL htM) ^ 3) v = v := by
      rw [S.rhoL_mul_pow_three_ZM hrM htM h3]; rfl
    simpa only [pow_succ, pow_zero, one_mul, LinearEquiv.mul_apply] using e
  have hW'fin : finrank (ZMod 2) (commSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≤ 4 := by
    have hle : commSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ commSpace (e : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔
        commSpace (e₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [hydef, Subgroup.coe_mul]
      exact AS35ZM.commSpace_mul_le _ _
    have h1 := (S.typeA_of_mem_DbarAsc_ZM hS he).2.2.2.1
    have h2 := (S.typeA_of_mem_DbarAsc_ZM hS he₂D).2.2.2.1
    have h4 := Submodule.finrank_sup_add_finrank_inf_eq (commSpace (e : S.Qt ≃ₗ[ZMod 2] S.Qt))
      (commSpace (e₂ : S.Qt ≃ₗ[ZMod 2] S.Qt))
    have h5 := Submodule.finrank_mono hle
    omega
  have htop := S.sup_commSpace_fixSpace_ZM hrM htM h3
  obtain ⟨haW, -, haC, -⟩ := S.rt_preserve_ZM hS hr ht hrM htM h3
  have hCW := fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate hgO
  have hCy := fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate y.2
  have hyC : ∀ c ∈ fixSpace (S.rhoL hrM * S.rhoL htM),
      (y : S.Qt ≃ₗ[ZMod 2] S.Qt) c ∈ fixSpace (S.rhoL hrM * S.rhoL htM) := fun c hc => by
    rw [mem_fixSpace] at hc ⊢
    rw [← hyg, hc]
  have hyW : ∀ w ∈ commSpace (S.rhoL hrM * S.rhoL htM),
      (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ commSpace (S.rhoL hrM * S.rhoL htM) := fun w hw =>
    AS35ZM.commSpace_mem_of_commute hyg hw
  rcases AS35ZM.semilinear_dichotomy hJ hgJ hg3 hyJ hyg hσJ hσg hσyL hW'fin with h | h
  ·
    apply hya
    have hyWt : ∀ w ∈ commSpace (S.rhoL hrM * S.rhoL htM),
        (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
      intro w hw
      rw [← mem_fixSpace, hCy]
      refine AS35ZM.le_orth_comm S.q ?_ hw
      rw [← hCW]
      exact h
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    exact AS35ZM.commute_of_triv htop hyWt hyC haC haW v
  ·
    apply hyd
    have hyCt : ∀ c ∈ fixSpace (S.rhoL hrM * S.rhoL htM), (y : S.Qt ≃ₗ[ZMod 2] S.Qt) c = c := by
      intro c hc
      rw [← mem_fixSpace, hCy, AS35ZM.mem_orth_iff]
      rw [hCW, AS35ZM.mem_orth_iff] at hc
      exact fun w hw => hc w (h hw)
    obtain ⟨hdW, -, hdC⟩ := S.Dx_facts_ZM hS h65 hr ht hrM htM h3 hd hda hdb
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    exact (AS35ZM.commute_of_triv htop hdW hdC hyCt hyW v).symm

end Pair


theorem mbarOTwoHyp_ZM (hS : S.SixHyp) (h65 : S.SixFiveConcl) {r t : G} (hr : r ∈ S.DSet)
    (ht : t ∈ S.DSet) (h3 : orderOf (r * t) = 3) (hxM : r * t ∈ S.M) : S.MbarOTwoHyp hxM := by
  intro R hRM hRx hRn hR2
  have hrM : r ∈ S.M := S.mem_M_of_mem_ESet hS.sixFour hr.1
  have htM : t ∈ S.M := S.mem_M_of_mem_ESet hS.sixFour ht.1
  obtain ⟨J, hJ, hJq, hJD, hJM⟩ := h65.fourStruct
  obtain ⟨k, hk⟩ : ∃ k, S.width = k + 2 := ⟨S.width - 2, by have := h65.four_le_width; omega⟩
  rw [eq_bot_iff]
  intro σ hσ
  rw [mem_bot]
  rcases hJM σ (hRM hσ) with hlin | hsemi
  · exact S.eq_one_of_linear_ZM hS h65 hr ht hrM htM h3 hJ hJq hJD hRM hxM hRx hRn hR2 hk hσ hlin
  · exact (S.not_semilinear_ZM hS h65 hr ht hrM htM h3 hJ hJq hJD hRM hxM hRx hRn hR2 hk hσ
      hsemi).elim

end Setting

namespace S14

theorem aschbacherSixSevenMbarStmt : AschbacherSixSevenMbarStmt :=
  fun _ _ _ S hS h65 _ hr _ ht h3 hxM =>
    ⟨S.mbarOddHyp_ZM hS h65 hr ht h3 hxM, S.mbarOTwoHyp_ZM hS h65 hr ht h3 hxM⟩

end S14

end CFSG.LargeExtraspecial
