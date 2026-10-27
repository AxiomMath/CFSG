module

public import CFSG.GH74.GLS.LU.Local.FiveStdMat6
public import CFSG.GH74.GLS.LU.Local.FiveBundles
public import CFSG.GH74.GLS.LU.Local.FiveStdMat4

public section

open Subgroup CFSG.GH74.GLS.LU.Local

namespace CFSG.GH74.GLS.LU.Local.Five

open CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.FiveStd.Mat CFSG.GH74.L5U5
  CFSG.GH74.GLS.Stage2.Final.ModelBlock

section Block

variable {F : Type} [Field F] [CharP F 5]

omit [CharP F 5] in
theorem cjL_eq_of_conj_mem {G : Type} [Group G] [Finite G] {g : G} {K : Subgroup G}
    (h : ∀ k ∈ K, g * k * g⁻¹ ∈ K) : cjL g K = K := by
  have hle : cjL g K ≤ K := by
    rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem glE_commute_y {x : E} (hx : validE x = true) (hs : x.s = false) :
    glE x * yGL F = yGL F * glE x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_glE hx, yGL_mat]
  exact mat4_comm_y_false hs

theorem ιF_mem_C0 {x : E} (hx : validE x = true) (hs : x.s = false) :
    ιF F x ∈ C0 (ModelData.lin F) := by
  rw [ιF_eq hx]
  exact ⟨⟨glE x, glE_mem_K4 hx⟩, mem_Dsub.2 (Subtype.ext (glE_commute_y hx hs)), rfl⟩

theorem ιF_block [Finite F] {x : E} (hx : validE x = true) (hs : x.s = false) :
    cjL (ιF F x) (K1 (ModelData.lin F)) = K1 (ModelData.lin F) ∧
      cjL (ιF F x) (K2 (ModelData.lin F)) = K2 (ModelData.lin F) := by
  have hc := ιF_mem_C0 (F := F) hx hs
  exact ⟨cjL_eq_of_conj_mem (fun k hk => C0_conj_K1 _ two_ne_zero_F hc hk),
    cjL_eq_of_conj_mem (fun k hk => C0_conj_K2 _ two_ne_zero_F hc hk)⟩

end Block

end CFSG.GH74.GLS.LU.Local.Five

namespace CFSG.GH74.GLS.LU.Local.FiveStd.Mat

open CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final.ModelBlock Matrix

variable {F : Type} [Field F] [CharP F 5]

@[expose] def scaleE (c : Fin 5) (x : E) : E :=
  ⟨c * x.a0, c * x.a1, c * x.a2, c * x.a3, c * x.b0, c * x.b1, c * x.b2, c * x.b3, x.s⟩

theorem normE_eq_scaleE (z : E) : normE z = scaleE (cn z) z := rfl

theorem det_scale2 : ∀ c a0 a1 a2 a3 : ZMod 5,
    (c * a0) * (c * a3) - (c * a1) * (c * a2) = c * c * (a0 * a3 - a1 * a2) := by
  intros
  ring

theorem detA_scaleE (c : Fin 5) (x : E) : detA (scaleE c x) = c * c * detA x :=
  det_scale2 c x.a0 x.a1 x.a2 x.a3

theorem detB_scaleE (c : Fin 5) (x : E) : detB (scaleE c x) = c * c * detB x :=
  det_scale2 c x.b0 x.b1 x.b2 x.b3

theorem inv5_mul_cancel : ∀ c f : Fin 5, c ≠ 0 → inv5 c * (c * f) = f := by decide

theorem cn_scale : ∀ c a0 a1 : Fin 5, c ≠ 0 → (a0 = 1 ∨ (a0 = 0 ∧ a1 = 1)) →
    inv5 (if c * a0 ≠ 0 then c * a0 else c * a1) = inv5 c := by decide

theorem normE_scaleE {x : E} (hx : isNorm x = true) {c : Fin 5} (hc : c ≠ 0) : normE (scaleE c x) = x := by
  have h := cn_scale c x.a0 x.a1 hc ((isNorm_iff x).1 hx)
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, xs⟩ := x
  have key : ∀ d : Fin 5, d = inv5 c →
      (⟨d * (c * x0), d * (c * x1), d * (c * x2), d * (c * x3), d * (c * x4), d * (c * x5), d * (c * x6),
        d * (c * x7), xs⟩ : E) = ⟨x0, x1, x2, x3, x4, x5, x6, x7, xs⟩ := by
    intro d hd
    subst hd
    simp only [inv5_mul_cancel _ _ hc]
  simp only [normE, scaleE] at h ⊢
  exact key _ h

end CFSG.GH74.GLS.LU.Local.FiveStd.Mat
