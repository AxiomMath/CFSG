module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Spec

public section

namespace CFSG.KC.FzUT

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open CFSG.OddStandard.SmallF3.FritzII

theorem kcF4_add_self : ∀ a : F4c, a + a = 0 := by decide +kernel

theorem kcF4_frob_add : ∀ a b : F4c, (a + b) * (a + b) = a * a + b * b := by decide +kernel

theorem kcInZ_iff : ∀ x : FzUT, (x.a = 0 ∧ x.b = 0) ↔ ∀ y : FzUT, x * y = y * x := by
  intro x
  constructor
  · rintro ⟨ha, hb⟩ y
    exact UT3.ext (add_comm _ _) (add_comm _ _) (by
      change x.c + y.c + x.a * y.b = y.c + x.c + y.a * x.b
      rw [ha, hb, zero_mul, mul_zero, add_comm x.c])
  · intro h
    have h1 : x.c + 0 + x.a * 1 = 0 + x.c + 0 * x.b := congrArg UT3.c (h ⟨0, 1, 0⟩)
    have h2 : x.c + 0 + x.a * 0 = 0 + x.c + 1 * x.b := congrArg UT3.c (h ⟨1, 0, 0⟩)
    constructor
    · simpa using h1
    · simpa using h2.symm

theorem kcInZ_map (σ : MulAut FzUT) {z : FzUT} (h : FzInZ z) : FzInZ (σ z) := by
  refine (kcInZ_iff (σ z)).mpr fun y => ?_
  obtain ⟨y', rfl⟩ := σ.surjective y
  rw [← map_mul, ← map_mul, (kcInZ_iff z).mp h]

end CFSG.KC.FzUT
