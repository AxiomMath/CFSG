module

public import CFSG.LargeExtraspecial.S10FourD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem cl_mem_orbit (X : Hyp10 S g t) {h : S.M} (hth : t ∈ S.Lbar ((h : G) * g)) :
    S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ orbit S g t := by
  have := bV_mem_orbitOf X.H X.C X.ht X.ht1 X.hVQ X.hNo X.hΩ.not_transitive hth
  rw [mem_orbitOf_RmodN_iff X.haQ X.ht, coe_bV] at this
  exact this

theorem coe_orbV' (X : Hyp10 S g t) {k : S.M} (hk : S.ρ k ∈ Rbar S g t) :
    (orbV X.haQ X.ht hk : S.Qt) = S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
  rw [coe_orbV, ρ_cl_conj_z S k X.haQ]

theorem orbV_ne_zero' (X : Hyp10 S g t) {k : S.M} (hk : S.ρ k ∈ Rbar S g t) :
    orbV X.haQ X.ht hk ≠ 0 := fun h =>
  cl_conj_z_ne_zero S (conj_mem_QG' S k.2 X.haQ) (conj_ne_z' S k.2 X.H.conj_ne)
    ((coe_orbV' X hk).symm.trans (congrArg Subtype.val h))

theorem ρ_cl_conj_mul (X : Hyp10 S g t) (m h : S.M) :
    ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) =
      S.cl (((m * h : S.M) : G) * g * S.z * (((m * h : S.M) : G) * g)⁻¹) := by
  rw [S.ρ_cl m (conj_mem_QG' S h.2 X.haQ), Subgroup.coe_mul]
  congr 1
  group

theorem commSpace_conj (X : Hyp10 S g t) (x : S.O) :
    commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (Vt S g t).map ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := by
  rw [← (commSpace_t_eq X.H X.C X.ht X.ht1 X.hVQ).1]
  ext w
  rw [Submodule.mem_map_equiv (e := (x : S.Qt ≃ₗ[ZMod 2] S.Qt)), mem_commSpace, mem_commSpace]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v, ?_⟩
    change _ = ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) _
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, map_sub]
    rw [inv_apply_apply_O]
  · rintro ⟨v, hv⟩
    change _ = ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w at hv
    refine ⟨(x : S.Qt ≃ₗ[ZMod 2] S.Qt) v, ?_⟩
    have hw : w = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) :=
      (apply_inv_apply_O _ _).symm
    rw [hw, ← hv]
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, map_sub]
    rw [inv_apply_apply_O]

theorem StronglyClosedL.mem_Lbar_of_mem_commSpace_conj (hSC : StronglyClosedL S g t)
    (X : Hyp10 S g t) (F : Frame X) {m h : S.M}
    (hd : S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈
      commSpace ((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    S.ρ m * t * (S.ρ m)⁻¹ ∈ S.Lbar ((h : G) * g) := by
  rw [commSpace_conj X, Submodule.mem_map_equiv] at hd
  change (((S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) _ ∈ Vt S g t at hd
  rw [← map_inv, ρ_cl_conj_mul X] at hd
  have h1 := hSC.mem_Lbar_of_cl_mem_Vt X F hd
  have h2 := conj_mem_Lbar_mul S m h1
  rwa [show ((m : G) * (((m⁻¹ * h : S.M) : G) * g)) = (h : G) * g by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]; group] at h2

theorem apply_mem_Vt_Wt_of_commute (X : Hyp10 S g t) {x : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (hxt : x * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) * x) :
    (∀ v ∈ Vt S g t, x v ∈ Vt S g t) ∧ (∀ w ∈ Wt S g t, x w ∈ Wt S g t) := by
  obtain ⟨hcomm, hfix⟩ := commSpace_t_eq X.H X.C X.ht X.ht1 X.hVQ
  have hxtv : ∀ v, x ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (x v) :=
    fun v => by rw [← LinearEquiv.mul_apply, hxt, LinearEquiv.mul_apply]
  refine ⟨fun v hv => ?_, fun w hw => ?_⟩
  · rw [← hcomm] at hv ⊢
    obtain ⟨u, rfl⟩ := mem_commSpace.mp hv
    exact mem_commSpace.mpr ⟨x u, by rw [map_sub, hxtv]⟩
  · rw [← hfix, mem_fixSpace] at hw ⊢
    rw [← hxtv, hw]

theorem apply_mem_orbit_of_commute (X : Hyp10 S g t) {x : S.O} (hxM : x ∈ S.Mbar)
    (hxt : x * t = t * x) {v : S.Qt} (hv : v ∈ orbit S g t) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ orbit S g t := by
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hxM
  obtain ⟨k, hk, rfl⟩ := exists_of_mem_orbit hv X.haQ
  rw [ρ_cl_conj_mul X]
  refine cl_mem_orbit X ?_
  have h1 := conj_mem_Lbar_mul S y (mem_Lbar_mul_of_mem_Rbar X.H X.ht hk)
  rw [show S.ρ y * t * (S.ρ y)⁻¹ = t by rw [hxt]; group] at h1
  rwa [show (y : G) * ((k : G) * g) = ((y * k : S.M) : G) * g by rw [Subgroup.coe_mul]; group]
    at h1

end CFSG.LargeExtraspecial.S10
