module

public import CFSG.LargeExtraspecial.S10FourF

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem mem_commSpace_conj_iff (X : Hyp10 S g t) (m : S.M) {x : S.Qt} :
    x ∈ commSpace ((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ↔
      (((S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x ∈ Vt S g t := by
  rw [commSpace_conj X, Submodule.mem_map_equiv]
  rfl

theorem beta_conj_sub (X : Hyp10 S g t) (m : S.M) (u : Vt S g t) (w : S.Qt)
    (hw : (((S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) ∈ Vt S g t) :
    beta X.H X.C X.ht X.ht1 X.hVQ u ⟨_, hw⟩ =
      polar S.q (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) w := by
  have hy : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((((S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
      (((S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = (((S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by
    rw [map_sub]
    congr 1
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
    rw [inv_apply_apply_O]
  rw [beta_apply X.H X.C X.ht X.ht1 X.hVQ _ _ hy,
    ← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (S.ρ m).2, apply_inv_apply_O]

theorem StronglyClosedL.not_mem_orbit_of_mem_inf (hSC : StronglyClosedL S g t)
    (X : Hyp10 S g t) (F : Frame X) {m : S.M} (hne : S.ρ m * t * (S.ρ m)⁻¹ ≠ t) {w : S.Qt}
    (hw : w ∈ commSpace ((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    w ∉ orbit S g t := by
  intro hwo
  obtain ⟨k, hk, rfl⟩ := exists_of_mem_orbit hwo X.haQ
  have htk := mem_Lbar_mul_of_mem_Rbar X.H X.ht hk
  have ht'k := hSC.mem_Lbar_of_mem_commSpace_conj X F hw
  have h1 : S.ρ 1 * t * (S.ρ 1)⁻¹ ∈ S.Lbar ((k : G) * g) := by
    rw [map_one, one_mul, inv_one, mul_one]
    exact htk
  have := hSC.conj_eq_conj ht'k h1
  rw [map_one, one_mul, inv_one, mul_one] at this
  exact hne this

theorem StronglyClosedL.not_mem_orbit_conj_of_mem_inf (hSC : StronglyClosedL S g t)
    (X : Hyp10 S g t) (F : Frame X) {m : S.M} (hne : S.ρ m * t * (S.ρ m)⁻¹ ≠ t) {w : S.Qt}
    (hwV : w ∈ Vt S g t) :
    (((S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∉ orbit S g t := by
  intro hwo
  obtain ⟨k, hk, hwk⟩ := exists_of_mem_orbit hwo X.haQ
  have hw : w = S.cl (((m * k : S.M) : G) * g * S.z * (((m * k : S.M) : G) * g)⁻¹) := by
    rw [← ρ_cl_conj_mul X, ← hwk, apply_inv_apply_O]
  rw [hw] at hwV
  have h1 := hSC.mem_Lbar_of_cl_mem_Vt X F hwV
  have htk := mem_Lbar_mul_of_mem_Rbar X.H X.ht hk
  have h2 := conj_mem_Lbar_mul S m htk
  rw [show (m : G) * ((k : G) * g) = ((m * k : S.M) : G) * g by
    rw [Subgroup.coe_mul, mul_assoc]] at h2
  have h3 : S.ρ 1 * t * (S.ρ 1)⁻¹ ∈ S.Lbar (((m * k : S.M) : G) * g) := by
    rw [map_one, one_mul, inv_one, mul_one]
    exact h1
  have := hSC.conj_eq_conj h2 h3
  rw [map_one, one_mul, inv_one, mul_one] at this
  exact hne this

theorem apply_mem_clSub_of_fix (X : Hyp10 S g t) {y k : S.M}
    (hfix : ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) = S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹))
    {w : S.Qt} (hw : w ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g))) :
    ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) := by
  have h1 := apply_mem_clSub_Qa_mul (g := (k : G) * g) y hw
  rw [ρ_cl_conj_mul X] at hfix
  rwa [show (y : G) * ((k : G) * g) = ((y * k : S.M) : G) * g by
      rw [Subgroup.coe_mul, mul_assoc],
    clSub_eq_of_cl_eq (conj_mem_QG' S (y * k).2 X.haQ) (conj_ne_z' S (y * k).2 X.H.conj_ne)
      (conj_mem_QG' S k.2 X.haQ) hfix] at h1

end CFSG.LargeExtraspecial.S10
