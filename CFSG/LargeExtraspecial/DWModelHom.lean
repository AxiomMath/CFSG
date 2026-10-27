module

public import CFSG.LargeExtraspecial.DWModelMat
public import CFSG.GroupTheory.GLnTwoSplitting.Main

public section

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module Matrix CFSG.GroupTheory.GLnTwoSplitting
open scoped IsMulCommutative

variable {H : Type*} [Group H] (V : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]

structure Splitting where
  centralizer_le : centralizer (V : Set H) ≤ V
  σ : (Additive V ≃ₗ[ZMod 2] Additive V) →* H
  conjLinear_σ : ∀ f, conjLinear V (σ f) = f

theorem zmod_two_eq_one_of_isUnit {a : ZMod 2} (h : IsUnit a) : a = 1 := by
  have h0 := h.ne_zero
  revert h0
  revert a
  decide

namespace Splitting

variable {V} (X : Splitting V)

include X in
theorem conjLinear_eq_one_iff' (h : H) : conjLinear V h = 1 ↔ h ∈ V := by
  rw [conjLinear_eq_one_iff V X.centralizer_le]
  exact ⟨fun ⟨e, he⟩ => he ▸ (Additive.toMul e).2, fun hh => ⟨Additive.ofMul ⟨h, hh⟩, rfl⟩⟩

theorem mul_inv_σ_mem (h : H) : h * (X.σ (conjLinear V h))⁻¹ ∈ V := by
  rw [← X.conjLinear_eq_one_iff', map_mul, map_inv, X.conjLinear_σ, mul_inv_cancel]

@[expose] noncomputable def transl (h : H) : Additive V :=
  Additive.ofMul ⟨h * (X.σ (conjLinear V h))⁻¹, X.mul_inv_σ_mem h⟩

theorem coe_transl (h : H) :
    ((Additive.toMul (X.transl h) : V) : H) = h * (X.σ (conjLinear V h))⁻¹ := rfl

theorem transl_mul (h h' : H) :
    X.transl (h * h') = X.transl h + conjLinear V h (X.transl h') := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [toMul_add, mul_comm, Subgroup.coe_mul, coe_conjLinear_apply, coe_transl, coe_transl,
    coe_transl, map_mul, map_mul]
  group

theorem transl_one : X.transl 1 = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [coe_transl, map_one, map_one, inv_one, mul_one]
  rfl

theorem transl_of_mem {v : H} (hv : v ∈ V) : X.transl v = Additive.ofMul ⟨v, hv⟩ := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [coe_transl, (X.conjLinear_eq_one_iff' v).mpr hv, map_one, inv_one, mul_one]
  rfl

theorem transl_σ (f : Additive V ≃ₗ[ZMod 2] Additive V) : X.transl (X.σ f) = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [coe_transl, X.conjLinear_σ, mul_inv_cancel]
  rfl

variable {m : ℕ} (b : Basis (Fin m) (ZMod 2) (Additive V))

noncomputable abbrev mat (h : H) : Matrix (Fin m) (Fin m) (ZMod 2) :=
  LinearMap.toMatrix b b (conjLinear V h : Additive V →ₗ[ZMod 2] Additive V)

theorem mat_mul (h h' : H) : mat b (h * h') = mat b h * mat b h' := by
  rw [mat, mat, mat, ← LinearMap.toMatrix_mul, map_mul]
  rfl

theorem mat_mulVec (h : H) (x : Additive V) :
    mat b h *ᵥ b.repr x = b.repr (conjLinear V h x) :=
  LinearMap.toMatrix_mulVec_repr b b _ x

theorem mat_one : mat b (1 : H) = 1 := by
  rw [mat, map_one]
  exact LinearMap.toMatrix_id b

theorem det_mat_ne_zero (h : H) : (mat b h).det ≠ 0 := by
  rw [mat, LinearMap.det_toMatrix]
  exact (LinearEquiv.isUnit_det' _).ne_zero

@[expose] noncomputable def toSL : H →* SpecialLinearGroup (Fin (m + 1)) (ZMod 2) where
  toFun h := ⟨affMat (b.repr (X.transl h)) (mat b h), by
    rw [det_affMat]
    exact det_eq_one_of_ne_zero_zmod_two (det_mat_ne_zero b h)⟩
  map_one' := by
    apply Subtype.ext
    change affMat (b.repr (X.transl 1)) (mat b 1) = 1
    rw [X.transl_one, map_zero, Finsupp.coe_zero, mat_one, affMat_zero_one]
  map_mul' h h' := by
    apply Subtype.ext
    change affMat _ _ = affMat _ _ * affMat _ _
    rw [affMat_mul, ← mat_mul, X.transl_mul, map_add, Finsupp.coe_add, mat_mulVec]

theorem coe_toSL (h : H) :
    ((X.toSL b h : SpecialLinearGroup (Fin (m + 1)) (ZMod 2)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) = affMat (b.repr (X.transl h)) (mat b h) :=
  rfl

theorem toSL_injective : Function.Injective (X.toSL b) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro h hh
  rw [MonoidHom.mem_ker] at hh
  have h1 : affMat (b.repr (X.transl h)) (mat b h) = affMat 0 1 := by
    rw [affMat_zero_one, ← coe_toSL]
    exact (congrArg (fun A : SpecialLinearGroup (Fin (m + 1)) (ZMod 2) =>
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2))) hh).trans
      Matrix.SpecialLinearGroup.coe_one
  obtain ⟨hw, hg⟩ := affMat_injective h1
  have hπ : conjLinear V h = 1 := by
    have : (conjLinear V h : Additive V →ₗ[ZMod 2] Additive V) = LinearMap.id :=
      (LinearMap.toMatrix b b).injective (by rw [LinearMap.toMatrix_id]; exact hg)
    exact LinearEquiv.ext fun x => LinearMap.congr_fun this x
  have hτ : X.transl h = 0 := by
    have : b.repr (X.transl h) = 0 := Finsupp.ext fun i => congrFun hw i
    simpa using this
  have h2 := congrArg (fun e : Additive V => ((Additive.toMul e : V) : H)) hτ
  simp only [coe_transl, hπ, map_one, inv_one, mul_one] at h2
  rw [mem_bot]
  exact h2

theorem coe_toSL_of_mem {v : H} (hv : v ∈ V) :
    ((X.toSL b v : SpecialLinearGroup (Fin (m + 1)) (ZMod 2)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) =
        affMat (b.repr (Additive.ofMul ⟨v, hv⟩)) 1 := by
  rw [coe_toSL, X.transl_of_mem hv, mat, (X.conjLinear_eq_one_iff' v).mpr hv]
  congr 1
  exact LinearMap.toMatrix_id b

theorem exists_toSL_eq (w : Fin m → ZMod 2) {g : Matrix (Fin m) (Fin m) (ZMod 2)}
    (hg : g.det ≠ 0) :
    ∃ h, ((X.toSL b h : SpecialLinearGroup (Fin (m + 1)) (ZMod 2)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) = affMat w g := by
  have hu : IsUnit (LinearMap.toMatrix b b (Matrix.toLin b b g)).det := by
    rw [LinearMap.toMatrix_toLin]
    exact isUnit_iff_ne_zero.mpr hg
  set f : Additive V ≃ₗ[ZMod 2] Additive V := LinearEquiv.ofIsUnitDet hu
  set x : Additive V := b.equivFun.symm w
  refine ⟨((Additive.toMul x : V) : H) * X.σ f, ?_⟩
  have hxV : ((Additive.toMul x : V) : H) ∈ V := (Additive.toMul x).2
  have hπ : conjLinear V (((Additive.toMul x : V) : H) * X.σ f) = f := by
    rw [map_mul, (X.conjLinear_eq_one_iff' _).mpr hxV, one_mul, X.conjLinear_σ]
  have hτ : X.transl (((Additive.toMul x : V) : H) * X.σ f) = x := by
    rw [X.transl_mul, X.transl_σ, map_zero, add_zero, X.transl_of_mem hxV]
    rfl
  rw [coe_toSL, hτ, mat, hπ]
  congr 1
  · rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  · change LinearMap.toMatrix b b (f : Additive V →ₗ[ZMod 2] Additive V) = g
    have hf : (f : Additive V →ₗ[ZMod 2] Additive V) = Matrix.toLin b b g := by
      ext y
      rfl
    rw [hf, LinearMap.toMatrix_toLin]

include X in
theorem nonempty_centralizer_mulEquiv (hN : 2 ≤ m + 1) {z : H} (hz : z ∈ V)
    (hb : b ⟨0, by omega⟩ = Additive.ofMul ⟨z, hz⟩) :
    Nonempty (centralizer ({z} : Set H) ≃*
      centralizer ({cornerTransvection hN} : Set (SpecialLinearGroup (Fin (m + 1)) (ZMod 2)))) := by
  have htz : X.toSL b z = cornerTransvection hN := by
    apply Subtype.ext
    rw [coe_toSL_of_mem X b hz, coe_cornerTransvection_eq_affMat, ← hb, Basis.repr_self,
      Finsupp.single_eq_pi_single]
  have hmem : ∀ c : centralizer ({z} : Set H),
      X.toSL b c ∈ centralizer ({cornerTransvection hN} :
        Set (SpecialLinearGroup (Fin (m + 1)) (ZMod 2))) := by
    intro c
    rw [mem_centralizer_singleton_iff, ← htz, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp c.2]
  let φ : centralizer ({z} : Set H) →* centralizer ({cornerTransvection hN} :
      Set (SpecialLinearGroup (Fin (m + 1)) (ZMod 2))) :=
    ((X.toSL b).comp (centralizer ({z} : Set H)).subtype).codRestrict _ hmem
  refine ⟨MulEquiv.ofBijective φ ⟨fun c c' hcc' => ?_, fun M => ?_⟩⟩
  · exact Subtype.ext (X.toSL_injective b (congrArg Subtype.val hcc'))
  · have hMc := mem_centralizer_singleton_iff.mp M.2
    have hdet : ((M : SpecialLinearGroup (Fin (m + 1)) (ZMod 2)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)).det ≠ 0 := by
      rw [(M : SpecialLinearGroup (Fin (m + 1)) (ZMod 2)).2]
      exact one_ne_zero
    obtain ⟨w, g, hwg⟩ := exists_eq_affMat_of_commute hN hdet
      (by simpa using congrArg (fun A : SpecialLinearGroup (Fin (m + 1)) (ZMod 2) =>
        (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2))) hMc)
    have hg : g.det ≠ 0 := by
      rw [← det_affMat w g, ← hwg]
      exact hdet
    obtain ⟨h, hh⟩ := X.exists_toSL_eq b w hg
    have hhM : X.toSL b h = M := Subtype.ext (hh.trans hwg.symm)
    have hcent : h ∈ centralizer ({z} : Set H) := by
      rw [mem_centralizer_singleton_iff]
      refine X.toSL_injective b ?_
      rw [map_mul, map_mul, hhM, htz, hMc]
    exact ⟨⟨h, hcent⟩, Subtype.ext hhM⟩

end Splitting

end CFSG.LargeExtraspecial.DW
