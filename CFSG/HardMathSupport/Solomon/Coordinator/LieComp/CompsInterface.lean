module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Fi22

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md42047359a2a

@[expose] def LieCompsOn (p : ℕ) (F : LieFamily) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, lieFamily idx.1 = F →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
    ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 →
      (lieIndexChar idx.1 ≠ p ∨ ∀ a : S, MulAut.conj a ≠ β) →
        LieCompsExport (lieIndexChar idx.1) β

private theorem lieIndexChar_eq_characteristic' (d : TauCeti.LieTypeIndex) :
    lieIndexChar d = d.characteristic := by
  cases d <;> simp [lieIndexChar]


theorem fi22LieSSC_of_lieCompsOn (hb : LieOrderBridge) (h : ∀ F, LieCompsOn 5 F) :
    Fi22LieSSC := by
  intro S _ _ hs hna idx he h5 x hx5 hx1 hF
  exfalso
  have hZ : Subgroup.center S = ⊥ := b3Lie_center_eq_bot hna
  have hβ1 : MulAut.conj x ≠ 1 := by
    intro h1
    apply hx1
    have hxZ : x ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 : x * g * x⁻¹ = g := by
        have := congrArg (fun φ : MulAut S => φ g) h1
        simpa [MulAut.conj_apply] using this
      calc g * x = (x * g * x⁻¹) * x := by rw [h2]
        _ = x * g := by group
    rw [hZ] at hxZ
    exact Subgroup.mem_bot.1 hxZ
  have hβ5 : MulAut.conj x ^ 5 = 1 := by rw [← map_pow, hx5, map_one]
  have hq : lieIndexChar idx.1 ≠ 5 := by rwa [lieIndexChar_eq_characteristic']
  exact false_of_fi22Cfg_of_comps hb
    (h (lieFamily idx.1) S hs hna idx rfl he (MulAut.conj x) hβ5 hβ1 (Or.inl hq)) hF

theorem fi22LieOuterC_of_lieCompsOn (hb : LieOrderBridge) (h : ∀ F, LieCompsOn 5 F) :
    Fi22LieOuterC := by
  intro S _ _ hs hna idx he _ α hα5 hout hF
  exfalso
  have hα1 : α ≠ 1 := fun h1 => hout 1 (by rw [h1, map_one])
  exact false_of_fi22Cfg_of_comps hb
    (h (lieFamily idx.1) S hs hna idx rfl he α hα5 hα1 (Or.inr hout)) hF

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
