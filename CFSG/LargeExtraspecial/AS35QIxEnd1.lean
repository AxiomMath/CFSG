module

public import CFSG.LargeExtraspecial.AS35QIxBasic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace IxSetup

variable (T : IxSetup S)

theorem rhoL_inv_zeta {c : G} (hcM : c ∈ S.M) (hcζ : S.ρ ⟨c, hcM⟩ * T.ζ * (S.ρ ⟨c, hcM⟩)⁻¹ = T.ζ⁻¹)
    (v : S.Qt) : S.rhoL hcM ((T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.rhoL hcM v)) := by
  have e : S.ρ ⟨c, hcM⟩ * T.ζ = T.ζ * T.ζ * S.ρ ⟨c, hcM⟩ := by
    have h1 : T.ζ⁻¹ = T.ζ * T.ζ :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact T.hζ3)
    calc S.ρ ⟨c, hcM⟩ * T.ζ = S.ρ ⟨c, hcM⟩ * T.ζ * (S.ρ ⟨c, hcM⟩)⁻¹ * S.ρ ⟨c, hcM⟩ := by group
      _ = T.ζ * T.ζ * S.ρ ⟨c, hcM⟩ := by rw [hcζ, h1]
  exact congrArg (fun s : S.O => (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v) e

theorem commSpace_eq_fixSpace_c {c : G} (hcM : c ∈ S.M) (hcc : c * c = 1)
    (hcζ : S.ρ ⟨c, hcM⟩ * T.ζ * (S.ρ ⟨c, hcM⟩)⁻¹ = T.ζ⁻¹) :
    commSpace (S.rhoL hcM) = fixSpace (S.rhoL hcM) :=
  commSpace_eq_fixSpace_of_inv T.finrank_Qt T.hζ2 (T.rhoL_inv_zeta hcM hcζ)
    (S.rhoL_mul_self hcM hcc)

theorem conj_eq_mul_z_of_nonsingular {c : G} (hcM : c ∈ S.M) (hcc : c * c = 1)
    (hcζ : S.ρ ⟨c, hcM⟩ * T.ζ * (S.ρ ⟨c, hcM⟩)⁻¹ = T.ζ⁻¹) {u : G} (huQ : u ∈ S.QG)
    (hfix : S.rhoL hcM (S.cl u) = S.cl u) (hq : S.q (S.cl u) ≠ 0) : c * u * c⁻¹ = u * S.z := by
  have hmem : S.cl u ∈ commSpace (S.rhoL hcM) := by
    rw [T.commSpace_eq_fixSpace_c hcM hcc hcζ]
    exact mem_fixSpace.mpr hfix
  have hinv := S.conj_eq_inv_of_cl_mem_commSpace hcM hcc huQ hmem
  have hu2 : u ^ 2 = S.z := by
    rcases S.sq_eq_one_or_z huQ with h | h
    · exact absurd ((S.q_cl_eq_zero_iff huQ).mpr h) hq
    · exact h
  rw [hinv]
  calc u⁻¹ = u⁻¹ * (u ^ 2 * S.z) := by rw [hu2, S.z_mul_z, mul_one]
    _ = u * S.z := by group

theorem exists_nonsingular_fix {c : G} (hcM : c ∈ S.M) (hcc : c * c = 1)
    (hcζ : S.ρ ⟨c, hcM⟩ * T.ζ * (S.ρ ⟨c, hcM⟩)⁻¹ = T.ζ⁻¹) :
    ∃ w : S.Qt, S.rhoL hcM w = w ∧ S.q w ≠ 0 := by
  by_contra h
  push Not at h
  have hcomm := T.commSpace_eq_fixSpace_c hcM hcc hcζ
  have hev := even_finrank_commSpace_of_forall_eq_zero S.q_nondegenerate (S.rhoL_mem hcM)
    (S.rhoL_mul_self hcM hcc) (fun x hx => h x (mem_fixSpace.mp (hcomm ▸ hx)))
  rw [hcomm, finrank_fixSpace_of_inv T.finrank_Qt T.hζ2 (T.rhoL_inv_zeta hcM hcζ)
    (S.rhoL_mul_self hcM hcc)] at hev
  exact absurd hev (by decide)

theorem conj_eq_of_singular {c : G} (hcM : c ∈ S.M) (hcc : c * c = 1)
    (hcζ : S.ρ ⟨c, hcM⟩ * T.ζ * (S.ρ ⟨c, hcM⟩)⁻¹ = T.ζ⁻¹) {u : G} (huQ : u ∈ S.QG)
    (hfix : S.rhoL hcM (S.cl u) = S.cl u) (hq : S.q (S.cl u) = 0) : c * u * c⁻¹ = u := by
  obtain ⟨w₀, hw₀, hqw₀⟩ := T.exists_nonsingular_fix hcM hcc hcζ
  obtain ⟨w, hwQ, rfl⟩ := S.exists_cl w₀
  have hwu : w * u ∈ S.QG := S.QG.mul_mem hwQ huQ
  have hpol : polar S.q (S.cl w) (S.cl u) = 0 :=
    polar_fixSpace_eq_zero_of_inv S.q_nondegenerate T.finrank_Qt T.hζ2
      (T.rhoL_inv_zeta hcM hcζ) (S.rhoL_mem hcM) (S.rhoL_mul_self hcM hcc) hw₀ hfix
  have hfix' : S.rhoL hcM (S.cl (w * u)) = S.cl (w * u) := by
    rw [S.cl_mul hwQ huQ, map_add, hw₀, hfix]
  have hq' : S.q (S.cl (w * u)) ≠ 0 := by
    rw [S.cl_mul hwQ huQ, QuadraticMap.map_add S.q, hq, hpol, add_zero, add_zero]
    exact hqw₀
  have h1 := T.conj_eq_mul_z_of_nonsingular hcM hcc hcζ hwQ hw₀ hqw₀
  have h2 := T.conj_eq_mul_z_of_nonsingular hcM hcc hcζ hwu hfix' hq'
  have hz : u * S.z = S.z * u := S.z_comm_QG huQ
  calc c * u * c⁻¹ = (c * w * c⁻¹)⁻¹ * (c * (w * u) * c⁻¹) := by group
    _ = (w * S.z)⁻¹ * (w * u * S.z) := by rw [h1, h2]
    _ = S.z⁻¹ * (u * S.z) := by group
    _ = S.z⁻¹ * (S.z * u) := by rw [hz]
    _ = u := by group

end IxSetup

end CFSG.LargeExtraspecial.AS35QIx
