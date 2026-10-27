module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterGen
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutLift

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.FrameVertex
  CFSG.ClassicalInvolution.ModelFacts.Orth15

section Lift

variable {S H P : Type} [Group S] [Group H] [Group P]

theorem innerHom_coe_eq_conj (ψ : S →* H) (s : S) :
    ((innerHom ψ s : ↥(inducedAutOn ψ.range)) : MulAut ↥ψ.range) =
      MulAut.conj (ψ.rangeRestrict s) := by
  apply MulEquiv.ext
  intro ℓ
  apply Subtype.ext
  rfl

theorem innerHom_congr (ψ : S →* H) {s s' : S} (h : ψ s = ψ s') : innerHom ψ s = innerHom ψ s' := by
  rw [innerHom_apply, innerHom_apply]
  exact congrArg _ (Subtype.ext h)

theorem conj_innerHom_of_outerAction [Group.IsPerfect S] (ψ : S →* H)
    (hψ : ψ.ker ≤ Subgroup.center S) (π : S →* P) (hπ : Function.Surjective π)
    (hπk : π.ker = Subgroup.center S) (w : ↥(inducedAutOn ψ.range)) {s s' : S}
    (h : outerAction ψ hψ π hπ hπk w (π s) = π s') :
    w * innerHom ψ s * w⁻¹ = innerHom ψ s' := by
  have h1 := outerAction_apply ψ hψ π hπ hπk w (π s)
  rw [h] at h1
  simp only [outerEquiv_apply] at h1
  exact h1.symm

theorem apply_rangeRestrict_eq [Group.IsPerfect S] (ψ : S →* H) (w : ↥(inducedAutOn ψ.range))
    (σ : MulAut S) (h : ∀ s, w * innerHom ψ s * w⁻¹ = innerHom ψ (σ s)) (s : S) :
    (w : MulAut ↥ψ.range) (ψ.rangeRestrict s) = ψ.rangeRestrict (σ s) := by
  have hconj : ∀ (y : MulAut ↥ψ.range) (g : ↥ψ.range),
      y * MulAut.conj g * y⁻¹ = MulAut.conj (y g) := by
    intro y g
    apply MulEquiv.ext
    intro l
    show y (g * y.symm l * g⁻¹) = y g * l * (y g)⁻¹
    simp
  have key : ((w : MulAut ↥ψ.range).toMonoidHom.comp ψ.rangeRestrict) =
      ψ.rangeRestrict.comp σ.toMonoidHom := by
    refine CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.hom_eq_of_central_ker_perfect
      (θ := (MulAut.conj : ↥ψ.range →* MulAut ↥ψ.range)) ?_ _ _ ?_
    · intro g hg
      rw [Subgroup.mem_center_iff]
      intro z
      have h2 : g * z * g⁻¹ = z := DFunLike.congr_fun (MonoidHom.mem_ker.mp hg) z
      calc z * g = (g * z * g⁻¹) * g := by rw [h2]
        _ = g * z := by group
    · intro s'
      have h1 := congrArg Subtype.val (h s')
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, innerHom_coe_eq_conj] at h1
      rw [hconj] at h1
      exact h1
  exact DFunLike.congr_fun key s

end Lift

section Pair

theorem mem_closure_pair_cases {G : Type} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) :
    ∀ g ∈ Subgroup.closure ({a, b} : Set G), g = 1 ∨ g = a ∨ g = b ∨ g = a * b := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hba : b * a = a * b := hab.symm
  have e1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have e2 : b * (a * b) = a := by rw [← hba, ← mul_assoc, hb, one_mul]
  have e3 : a * b * a = b := by rw [mul_assoc, hba, ← mul_assoc, ha, one_mul]
  have e4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have e5 : a * b * (a * b) = 1 := by rw [← mul_assoc, e3, hb]
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact Or.inr (Or.inl rfl)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul y z _ _ ihy ihz =>
    rcases ihy with h | h | h | h <;> rcases ihz with h' | h' | h' | h' <;>
      simp [h, h', ha, hb, hba, e1, e2, e3, e4, e5]
  | inv y _ ihy =>
    rcases ihy with h | h | h | h <;> simp [h, ha', hb', hba]

end Pair

end CFSG.ClassicalInvolution.Q3.Q3OT
