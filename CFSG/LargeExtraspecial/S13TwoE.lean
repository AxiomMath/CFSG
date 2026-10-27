module

public import CFSG.LargeExtraspecial.S13TwoD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g g₁ : G} {K : Subgroup S.O}

theorem sq_add_self_add_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {k : V ≃ₗ[ZMod 2] V} (hk3 : k ^ 3 = 1) (hfpf : ∀ v, k v = v → v = 0) (v : V) :
    k (k v) = k v + v := by
  have h3 : k (k (k v)) = v := by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) hk3
    simpa [pow_succ, LinearEquiv.mul_apply] using this
  have hw := hfpf (k (k v) + k v + v) (by rw [map_add, map_add, h3]; abel)
  have e : k (k v) = -(k v + v) := by
    rw [eq_neg_iff_add_eq_zero, ← add_assoc]; exact hw
  rw [e, zmod2_neg_eq]

namespace Hyp13

variable (Y : Hyp13 S g K)
include Y

theorem exists_eq_cl_of_mem_Fbar {u : S.Qt} (hu : u ∈ Fbar S g K) (hu0 : u ≠ 0) :
    ∃ m : S.M, S.ρ m ∈ K ∧ u = S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) := by
  obtain ⟨k, hk, hk1⟩ := Y.exists_K
  obtain ⟨m, rfl⟩ := Y.exists_ρ_eq hk
  rw [Fbar_eq_span Y.H Y.card_K Y.normal Y.fpf hk hk1, Submodule.mem_span_range_iff_exists_fun]
    at hu
  obtain ⟨c, hc⟩ := hu
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hkm : ∀ m' : S.M, S.cl ((m' : G) * g * S.z * ((m' : G) * g)⁻¹) =
      ((S.ρ m' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := fun m' =>
    (ρ_cl_conj_z S m' Y.haQ).symm
  rcases h01 (c 0) with h0 | h0 <;> rcases h01 (c 1) with h1 | h1 <;>
    rw [h0, h1] at hc <;> simp only [zero_smul, one_smul, zero_add, add_zero] at hc
  · exact absurd hc.symm hu0
  · exact ⟨m, hk, by rw [← hc, hkm]⟩
  · exact ⟨1, by simp, by rw [← hc]; simp⟩
  · refine ⟨m * m, by rw [map_mul]; exact mul_mem hk hk, ?_⟩
    rw [← hc, hkm, map_mul, Subgroup.coe_mul, LinearEquiv.mul_apply,
      sq_add_self_add_one (by rw [← Subgroup.coe_pow, Y.pow_three hk, Subgroup.coe_one])
        (fun v hv => fix_eq_zero Y.card_K Y.fpf hk hk1 v hv), add_comm]

end Hyp13

theorem clSub_Qa_mul_eq (m : S.M) (g' : G) {v : S.Qt} :
    v ∈ S.clSub (S.QG ⊓ S.Qa ((m : G) * g')) ↔
      (((S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa g') := by
  rw [QG_inf_Qa_mul m, mem_clSub_map_conj_iff m inf_le_left]

theorem apply_mem_clSub_Qa_mul (m : S.M) (g' : G) {v : S.Qt}
    (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g')) :
    ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa ((m : G) * g')) := by
  rw [clSub_Qa_mul_eq, inv_apply_apply_O]
  exact hv

theorem mem_fixSub_map_conj_iff (A : Subgroup S.O) (y : S.O) (v : S.Qt) :
    v ∈ fixSub S (A.map (MulAut.conj y).toMonoidHom) ↔
      ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ fixSub S A := by
  constructor
  · intro hv x hx
    have h1 := hv (y * x * y⁻¹) ⟨x, hx, rfl⟩
    have h2 := congrArg ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) h1
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, Subgroup.coe_inv] at h2 ⊢
    simpa [inv_apply_apply_O] using h2
  · rintro hv _ ⟨x, hx, rfl⟩
    have h1 := hv x hx
    have h2 := congrArg (y : S.Qt ≃ₗ[ZMod 2] S.Qt) h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
      LinearEquiv.mul_apply]
    simpa [apply_inv_apply_O] using h2

theorem finrank_inf_perp_ge (A W : Submodule (ZMod 2) S.Qt) :
    finrank (ZMod 2) A ≤ finrank (ZMod 2) (A ⊓ perp S W : Submodule (ZMod 2) S.Qt) +
      finrank (ZMod 2) W := by
  set ψ : A →ₗ[ZMod 2] (W →ₗ[ZMod 2] ZMod 2) :=
    ((S.q.polarBilin.flip).compl₂ W.subtype).comp A.subtype with hψ
  have hker : (LinearMap.ker ψ).map A.subtype ≤ A ⊓ perp S W := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨v.2, fun w hw => ?_⟩
    have := LinearMap.congr_fun (show ψ v = 0 from hv) ⟨w, hw⟩
    simpa [hψ, polarBilin_apply_apply] using this
  have h1 := LinearMap.finrank_range_add_finrank_ker ψ
  have h2 := Submodule.finrank_le (LinearMap.range ψ)
  rw [Module.finrank_linearMap_self] at h2
  have h3 := Submodule.finrank_mono hker
  rw [Submodule.finrank_map_subtype_eq] at h3
  omega

end CFSG.LargeExtraspecial.S13
