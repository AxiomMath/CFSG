module

public import CFSG.GH74.GLS.Bg.TwoGroups.L26Case
public import CFSG.GH74.GLS.Bg.TwoGroups.L23Models

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L26

open L23 L23.F16c

theorem two_add_F4c : ∀ x : F4c, x + x = 0 := by decide +kernel

theorem two_add_F16c : ∀ x : F16c, x + x = 0 := by decide +kernel

theorem barc_neg : ∀ y : F16c, barc (-y) = -barc y := by decide +kernel

theorem barc_zero : barc (0 : F16c) = 0 := by decide +kernel

theorem comm_UT3 {R : Type} [CommRing R] (g h : UT3 R) :
    g * h * g⁻¹ * h⁻¹ = ⟨0, 0, g.a * h.b - h.a * g.b⟩ := by
  ext <;> simp only [UT3.mul_def, UT3.inv_def] <;> ring

theorem central_UT3 {R : Type} [CommRing R] (z : R) (x : UT3 R) :
    x * (⟨0, 0, z⟩ : UT3 R) = (⟨0, 0, z⟩ : UT3 R) * x := by
  ext <;> simp only [UT3.mul_def] <;> ring

theorem comm_UHc (g h : UHc) :
    g * h * g⁻¹ * h⁻¹ = ⟨0, g.a * barc h.a - h.a * barc g.a⟩ := by
  refine UHc.ext ?_ ?_
  · simp only [UHc.mul_def, UHc.inv_def]
    ring
  · simp only [UHc.mul_def, UHc.inv_def, barc_neg]
    ring

theorem central_UHc (z : F16c) (x : UHc) :
    x * (⟨0, z⟩ : UHc) = (⟨0, z⟩ : UHc) * x := by
  refine UHc.ext ?_ ?_ <;> simp only [UHc.mul_def, barc_zero] <;> ring

theorem sq_UT3 (g : UT3 F4c) : g * g = ⟨0, 0, g.c + g.c + g.a * g.b⟩ :=
  UT3.ext (two_add_F4c _) (two_add_F4c _) rfl

theorem sq_UHc (g : UHc) : g * g = ⟨0, g.b + g.b + g.a * barc g.a⟩ :=
  UHc.ext (two_add_F16c _) rfl

theorem sfacts_UT3 : SFacts (UT3 F4c) := by
  refine ⟨card_UT3c, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · intro g h x
    rw [comm_UT3]
    exact central_UT3 _ x
  · intro g x
    rw [sq_UT3]
    exact central_UT3 _ x
  · decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

theorem sfacts_sylSU3c : SFacts ↥sylSU3c := by
  refine ⟨card_sylSU3c, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · intro g h x
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [comm_UHc]
    exact central_UHc _ _
  · intro g x
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [sq_UHc]
    exact central_UHc _ _
  · decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

theorem sfacts_SylSL3_4 : SFacts SylSL3_4 := SFacts.of_equiv sylLCongr sfacts_UT3

theorem sfacts_SylSU3_4 : SFacts SylSU3_4 := SFacts.of_equiv sylCongr sfacts_sylSU3c

end L26

end CFSG.GH74.GLS.Bg.TwoGroups
