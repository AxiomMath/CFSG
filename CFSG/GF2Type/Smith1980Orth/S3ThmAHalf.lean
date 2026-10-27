module

public import CFSG.GF2Type.Smith1980Orth.S3ThmACaseI

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem rho_conj_mul_self (S : Setting G) {k : G} (hxM : k * S.z * k⁻¹ ∈ S.M) :
    S.ρ ⟨_, hxM⟩ * S.ρ ⟨_, hxM⟩ = 1 := by
  rw [← map_mul]
  have : (⟨_, hxM⟩ : S.M) * ⟨_, hxM⟩ = 1 := Subtype.ext (by
    show k * S.z * k⁻¹ * (k * S.z * k⁻¹) = 1
    calc k * S.z * k⁻¹ * (k * S.z * k⁻¹) = k * (S.z * S.z) * k⁻¹ := by group
      _ = 1 := by rw [S.z_mul_z, mul_one, mul_inv_cancel])
  rw [this, map_one]

theorem commute_of_commutator_sq {x y : G} (hx2 : x ^ 2 = 1)
    (hg2 : (x * y * x⁻¹ * y⁻¹) ^ 2 = 1) : x * (x * y * x⁻¹ * y⁻¹) = (x * y * x⁻¹ * y⁻¹) * x := by
  have hxx : x * x = 1 := by rw [← pow_two, hx2]
  have hgg : (x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) = 1 := by rw [← pow_two, hg2]
  have hginv : (x * y * x⁻¹ * y⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ := inv_eq_of_mul_eq_one_right hgg
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have h1 : x * (x * y * x⁻¹ * y⁻¹) * x⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ := by
    rw [hxinv]
    calc x * (x * y * x * y⁻¹) * x = (x * x) * y * x * y⁻¹ * x := by group
      _ = y * x * y⁻¹ * x := by rw [hxx, one_mul]
      _ = (x * y * x * y⁻¹)⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, hxinv]
          group
  calc x * (x * y * x⁻¹ * y⁻¹) = x * (x * y * x⁻¹ * y⁻¹) * x⁻¹ * x := by group
    _ = (x * y * x⁻¹ * y⁻¹) * x := by rw [h1, hginv]

namespace S2Data

variable {M1 : Subgroup S.O} (D : S2Data S M1)

local notation "ρV" => D.resC

theorem even_finrank_Vt : Even (finrank (ZMod 2) (Vt S D.g D.t)) :=
  LinearMap.BilinForm.IsAlt.even_finrank D.betaV_isAlt D.betaV_nondegenerate

theorem q_eq_zero_of_mem_commSpace_Cbar {c : D.Cbar} (hcc : (c : S.O) * c = 1) {v : S.Qt}
    (hv : v ∈ commSpace ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) : S.q v = 0 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := (D.mem_commSpace_iff_coord_of_mem_Cbar c.2).mp hv
  have htt : ρV c * ρV c = 1 := LinearEquiv.ext fun w => by
    rw [LinearEquiv.mul_apply, D.resC_resC_apply hcc]
    rfl
  rw [D.q_coord, ← D.polar_QV]
  exact polar_commSpace_eq_zero (D.resC_mem_orthogonalGroup c) htt ha hb

theorem half_of_commute {k : G} (hxM : k * S.z * k⁻¹ ∈ S.M) (hxQ : k * S.z * k⁻¹ ∉ S.QG)
    (hxC : S.ρ ⟨_, hxM⟩ ∈ D.Cbar)
    (hab : ∀ u ∈ S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G),
      ∀ v ∈ S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G), u * v = v * u) :
    2 * finrank (ZMod 2) (commSpace (ρV ⟨_, hxC⟩)) = S.width ∧
      S.fixQt (k * S.z * k⁻¹) = S.clSub (S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G)) ∧
      S.commQt (k * S.z * k⁻¹) = S.fixQt (k * S.z * k⁻¹) := by
  have hcc : ((⟨_, hxC⟩ : D.Cbar) : S.O) * (⟨_, hxC⟩ : D.Cbar) = 1 :=
    rho_conj_mul_self S hxM
  have hx2 : (k * S.z * k⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have htt : ρV ⟨_, hxC⟩ * ρV ⟨_, hxC⟩ = 1 := LinearEquiv.ext fun w => by
    rw [LinearEquiv.mul_apply, D.resC_resC_apply hcc]
    rfl
  have hCw : finrank (ZMod 2) (S.clSub (S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G))) ≤
      S.width := by
    refine finrank_le_width_of_isotropic fun a ha b hb => ?_
    obtain ⟨u, hu, huQ, rfl⟩ := S.mem_clSub_iff.mp ha
    obtain ⟨v, hv, hvQ, rfl⟩ := S.mem_clSub_iff.mp hb
    exact (S.polar_cl_eq_zero_iff huQ hvQ).mpr (hab u hu v hv)
  have hfixC := SMK.finrank_fixQt_le S hxM hxQ hx2
  rw [S.fixQt_of_mem hxM] at hfixC
  have hQt := finrank_commSpace_add_finrank_fixSpace
    ((S.ρ ⟨_, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
  have hcomm2 : finrank (ZMod 2) (commSpace ((S.ρ ⟨_, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      2 * finrank (ZMod 2) (commSpace (ρV ⟨_, hxC⟩)) := D.finrank_commSpace_Cbar ⟨_, hxC⟩
  rw [S.finrank_Qt_eq_two_mul_width, hcomm2] at hQt
  have hle := two_mul_finrank_commSpace_le htt
  rw [D.finrank_Vt] at hle
  obtain ⟨r, hr⟩ := D.even_finrank_Vt
  rw [D.finrank_Vt] at hr
  have hhalf : 2 * finrank (ZMod 2) (commSpace (ρV ⟨_, hxC⟩)) = S.width := by omega
  have hrr : (S.ρ ⟨_, hxM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) * (S.ρ ⟨_, hxM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      1 := by
    rw [← Subgroup.coe_mul, rho_conj_mul_self S hxM]
    rfl
  have hcomm : S.commQt (k * S.z * k⁻¹) = S.fixQt (k * S.z * k⁻¹) := by
    rw [S.commQt_of_mem hxM, S.fixQt_of_mem hxM]
    apply Submodule.eq_of_le_of_finrank_eq (commSpace_le_fixSpace hrr)
    omega
  refine ⟨hhalf, le_antisymm (fun v hv => ?_) (S.clSub_centralizer_le_fixQt hxM), hcomm⟩
  rw [← hcomm] at hv
  have hq : S.q v = 0 := by
    rw [S.commQt_of_mem hxM] at hv
    exact D.q_eq_zero_of_mem_commSpace_Cbar hcc hv
  obtain ⟨y, hy, rfl⟩ := (S.mem_commQt_iff hxM).mp hv
  have hgQ : k * S.z * k⁻¹ * y * (k * S.z * k⁻¹)⁻¹ * y⁻¹ ∈ S.QG :=
    S.QG.mul_mem (S.conj_mem_QG hxM hy) (S.QG.inv_mem hy)
  have hg2 := (S.q_cl_eq_zero_iff hgQ).mp hq
  refine S.cl_mem_clSub ⟨hgQ, mem_centralizer_singleton_iff.mpr ?_⟩ hgQ
  exact (commute_of_commutator_sq hx2 hg2).symm

end S2Data

end CFSG.GF2Type.Smith1980Orth
