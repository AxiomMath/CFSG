module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAGen
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL2Cent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section AutDecomp

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K]

theorem kaL2_aut_decomp (e : K ≃* L2 F) (a : MulAut K) :
    ∃ (g : PGL2 F) (σ : F ≃+* F), a = innDiagHom e g * fieldAutHom e σ ∧
      orderOf σ ∣ orderOf a := by
  set x : PGammaL2 F := (pgammaAut e).symm a with hx
  have hxa : pgammaAut e x = a := by simp [hx]
  refine ⟨x.left, x.right, ?_, ?_⟩
  · conv_lhs => rw [← hxa, ← SemidirectProduct.inl_left_mul_inr_right x]
    rw [map_mul, pgammaAut_inl, pgammaAut_inr]
  · have h1 : orderOf x.right ∣ orderOf x := orderOf_map_dvd (SemidirectProduct.rightHom) x
    have h2 : orderOf x = orderOf a := by rw [← hxa]; exact (MulEquiv.orderOf_eq _ _).symm
    rw [h2] at h1
    exact h1

theorem kaL2_toPGL_apply (e : K ≃* L2 F) (g : PGL2 F) (σ : F ≃+* F) (k : K) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL
        (toPSL e ((innDiagHom e g * fieldAutHom e σ) k)) =
      g * pgl2FieldAut F σ (Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e k)) * g⁻¹ := by
  rw [MulAut.mul_apply, toPGL_toPSL_innDiagHom, toPSL_fieldAutHom, psl2FieldAut_toPGL]

end AutDecomp

section OddInner

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem kaL2_odd_mem_innAut (hF : L2Field F) (e : K ≃* L2 F) {a : MulAut K}
    (ha : a ∈ innDiagSub e) (hodd : Odd (orderOf a)) : a ∈ innAut K := by
  have hidx : ((innAut K).subgroupOf (innDiagSub e)).index = 2 := innAut_relIndex_two e hF
  have h1 : ∀ x y : ↥(innDiagSub e), x * y ∈ (innAut K).subgroupOf (innDiagSub e) ↔
      (x ∈ (innAut K).subgroupOf (innDiagSub e) ↔ y ∈ (innAut K).subgroupOf (innDiagSub e)) :=
    fun x y => Subgroup.mul_mem_iff_of_index_two hidx
  set x : ↥(innDiagSub e) := ⟨a, ha⟩ with hxdef
  have hsq : x * x ∈ (innAut K).subgroupOf (innDiagSub e) := (h1 x x).mpr Iff.rfl
  have hxo : Odd (orderOf x) := by
    rw [hxdef, Subgroup.orderOf_mk]
    exact hodd
  have := ka_odd_mem_of_sq_mem hsq hxo
  exact this

end OddInner

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
