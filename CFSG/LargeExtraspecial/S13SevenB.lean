module

public import CFSG.LargeExtraspecial.S13TwoB
public import CFSG.LargeExtraspecial.S13TwoD
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

omit [Finite G] in
theorem coe_mul_inv_mul (m h : S.M) (g : G) :
    ((m * h⁻¹ : S.M) : G) * ((h : G) * g) = (m : G) * g := by
  simp [mul_assoc]

theorem polar_O_apply (x : S.O) (u v : S.Qt) :
    polar S.q ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = polar S.q u v :=
  TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup x.2 u v

namespace Hyp13

variable (Y : Hyp13 S g K)
include Y

theorem Fbar_le_perp {F : Submodule (ZMod 2) S.Qt}
    (hFK : ∀ k ∈ K, ∀ v ∈ F, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ F)
    (ha : S.cl (g * S.z * g⁻¹) ∈ perp S F) : Fbar S g K ≤ perp S F := by
  obtain ⟨k, hk, hk1⟩ := Y.exists_K
  rw [← Y.span_pair_eq (cl_mem_Fbar Y.H) (cl_conj_z_ne_zero S Y.haQ Y.hne) hk hk1,
    Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ha
  · intro w hw
    have hw' := hFK _ (inv_mem hk) w hw
    have e := polar_O_apply k (((k⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w)
      (S.cl (g * S.z * g⁻¹))
    rw [apply_inv_apply_O] at e
    show polar S.q w ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) = 0
    rw [e]
    exact ha _ hw'

end Hyp13

end CFSG.LargeExtraspecial.S13
