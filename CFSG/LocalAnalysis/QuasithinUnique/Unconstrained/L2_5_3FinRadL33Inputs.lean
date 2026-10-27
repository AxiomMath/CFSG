module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadListCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsSL3Raw
public import Mathlib.GroupTheory.Nilpotent
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.QuasithinUnique.Fin253
open CFSG.QuasithinUnique.Unc25K1

@[expose] def rinv (x : R9) : R9 :=
  ⟨x.e * x.i - x.f * x.h, -(x.b * x.i) + x.c * x.h, x.b * x.f - x.c * x.e,
   -(x.d * x.i) + x.f * x.g, x.a * x.i - x.c * x.g, -(x.a * x.f) + x.c * x.d,
   x.d * x.h - x.e * x.g, -(x.a * x.h) + x.b * x.g, x.a * x.e - x.b * x.d⟩

theorem rr_inv (x : S3) : rr x⁻¹ = rinv (rr x) := by
  simp [rr, rinv, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
  exact ⟨rfl, rfl, rfl, rfl⟩

@[expose] def s3Model : ListModel S3 R9 where
  enc := rr
  inj := rr_inj
  mul := rmul
  one := rone
  inv := rinv
  enc_mul := rr_mul
  enc_one := rr_one
  enc_inv := rr_inv
  elems := rawList
  mem_elems := fun y =>
    ⟨fun h => ⟨ofR9 y (det_of_mem_rawList h), rr_ofR9 _ _⟩, fun ⟨x, hx⟩ => hx ▸ rr_mem x⟩

@[expose] def s3Invs : List R9 :=
  s3Model.elems.filter fun t => decide (t ≠ s3Model.one ∧ s3Model.mul t t = s3Model.one)

@[expose] def s3Ord4 : List R9 :=
  s3Model.elems.filter fun u => decide (lpow s3Model.mul s3Model.one u 4 = s3Model.one ∧
    lpow s3Model.mul s3Model.one u 2 ≠ s3Model.one)

end CFSG.QuasithinUnique.Fin253
