module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux19
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenData4
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux17

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
open scoped commutatorElement

set_option linter.unusedSectionVars false


section CCalc

variable {R : Type} [Field R] [CharP R 2]

theorem comm_root2 {α β : Fin Tag.E8.rank → ℤ} (hα : α ∈ rootFinset Tag.E8)
    (hβ : β ∈ rootFinset Tag.E8) (hne : α ≠ β) (hne' : α ≠ -β) (hs : α + β ∈ rootFinset Tag.E8)
    (c d : R) :
    ⁅pinnedX Tag.E8 R α c, pinnedX Tag.E8 R β d⁆ = pinnedX Tag.E8 R (α + β) (c * d) := by
  obtain ⟨ε, hε, h⟩ := comm_root (L := R) hα hβ hne hne' hs c d
  rw [h, sign_eq_one hε, one_mul]

theorem comm_prod_aux {G : Type*} [Group G] (a x y q₀ q₁ z : G) (e₀ : ⁅a, x⁆ = q₀)
    (e₁ : ⁅a, y⁆ = q₁) (e₂ : ⁅x, q₁⁆ = z) : ⁅a, x * y⁆ = q₀ * z * q₁ := by
  subst e₀ e₁ e₂
  simp only [commutatorElement_def]
  group

theorem c_calc {β₀ β₁ : Fin Tag.E8.rank → ℤ} (hA : PairData β₀ β₁) (s d t : R) :
    ⁅pinnedX Tag.E8 R (-highRoot Tag.E8) t, pinnedX Tag.E8 R β₀ s * pinnedX Tag.E8 R β₁ d⁆ =
      pinnedX Tag.E8 R (-highRoot Tag.E8 + β₀) (t * s) *
        pinnedX Tag.E8 R (β₀ + (-highRoot Tag.E8 + β₁)) (s * (t * d)) *
        pinnedX Tag.E8 R (-highRoot Tag.E8 + β₁) (t * d) := by
  have hnθr : -highRoot Tag.E8 ∈ rootFinset Tag.E8 := mem_rootFinset.2 (isRoot_neg_highRoot _)
  exact comm_prod_aux _ _ _ _ _ _
    (comm_root2 hnθr hA.h₀ hA.m₀ hA.m₀' hA.r₀ t s)
    (comm_root2 hnθr hA.h₁ hA.m₁ hA.m₁' hA.r₁ t d)
    (comm_root2 hA.h₀ hA.r₁ hA.z₀ hA.z₀' hA.zr s (t * d))

@[expose] def E3 (γ₀ γZ γ₁ : Fin Tag.E8.rank → ℤ) (a b c : R) : ModGL Tag.E8 R :=
  pinnedX Tag.E8 R γ₀ a * pinnedX Tag.E8 R γZ b * pinnedX Tag.E8 R γ₁ c

theorem E3_mul {γ₀ γZ γ₁ : Fin Tag.E8.rank → ℤ}
    (h₀Z : ∀ a b : R, pinnedX Tag.E8 R γZ b * pinnedX Tag.E8 R γ₀ a =
      pinnedX Tag.E8 R γ₀ a * pinnedX Tag.E8 R γZ b)
    (h₀₁ : ∀ a c : R, pinnedX Tag.E8 R γ₁ c * pinnedX Tag.E8 R γ₀ a =
      pinnedX Tag.E8 R γ₀ a * pinnedX Tag.E8 R γ₁ c)
    (hZ₁ : ∀ b c : R, pinnedX Tag.E8 R γ₁ c * pinnedX Tag.E8 R γZ b =
      pinnedX Tag.E8 R γZ b * pinnedX Tag.E8 R γ₁ c) (a b c a' b' c' : R) :
    E3 γ₀ γZ γ₁ a b c * E3 γ₀ γZ γ₁ a' b' c' = E3 γ₀ γZ γ₁ (a + a') (b + b') (c + c') := by
  unfold E3
  rw [pinnedX_add, pinnedX_add, pinnedX_add]
  calc pinnedX Tag.E8 R γ₀ a * pinnedX Tag.E8 R γZ b * pinnedX Tag.E8 R γ₁ c *
        (pinnedX Tag.E8 R γ₀ a' * pinnedX Tag.E8 R γZ b' * pinnedX Tag.E8 R γ₁ c')
      = pinnedX Tag.E8 R γ₀ a * pinnedX Tag.E8 R γZ b *
        (pinnedX Tag.E8 R γ₁ c * pinnedX Tag.E8 R γ₀ a') * pinnedX Tag.E8 R γZ b' *
        pinnedX Tag.E8 R γ₁ c' := by simp only [mul_assoc]
    _ = pinnedX Tag.E8 R γ₀ a * pinnedX Tag.E8 R γZ b *
        (pinnedX Tag.E8 R γ₀ a' * pinnedX Tag.E8 R γ₁ c) * pinnedX Tag.E8 R γZ b' *
        pinnedX Tag.E8 R γ₁ c' := by rw [h₀₁ a' c]
    _ = pinnedX Tag.E8 R γ₀ a * (pinnedX Tag.E8 R γZ b * pinnedX Tag.E8 R γ₀ a') *
        pinnedX Tag.E8 R γ₁ c * pinnedX Tag.E8 R γZ b' * pinnedX Tag.E8 R γ₁ c' := by
          simp only [mul_assoc]
    _ = pinnedX Tag.E8 R γ₀ a * (pinnedX Tag.E8 R γ₀ a' * pinnedX Tag.E8 R γZ b) *
        pinnedX Tag.E8 R γ₁ c * pinnedX Tag.E8 R γZ b' * pinnedX Tag.E8 R γ₁ c' := by
          rw [h₀Z a' b]
    _ = pinnedX Tag.E8 R γ₀ a * pinnedX Tag.E8 R γ₀ a' * pinnedX Tag.E8 R γZ b *
        (pinnedX Tag.E8 R γ₁ c * pinnedX Tag.E8 R γZ b') * pinnedX Tag.E8 R γ₁ c' := by
          simp only [mul_assoc]
    _ = pinnedX Tag.E8 R γ₀ a * pinnedX Tag.E8 R γ₀ a' * pinnedX Tag.E8 R γZ b *
        (pinnedX Tag.E8 R γZ b' * pinnedX Tag.E8 R γ₁ c) * pinnedX Tag.E8 R γ₁ c' := by
          rw [hZ₁ b' c]
    _ = pinnedX Tag.E8 R γ₀ a * pinnedX Tag.E8 R γ₀ a' *
        (pinnedX Tag.E8 R γZ b * pinnedX Tag.E8 R γZ b') *
        (pinnedX Tag.E8 R γ₁ c * pinnedX Tag.E8 R γ₁ c') := by simp only [mul_assoc]

theorem E3_zero (γ₀ γZ γ₁ : Fin Tag.E8.rank → ℤ) : E3 γ₀ γZ γ₁ (0 : R) 0 0 = 1 := by
  unfold E3
  simp [pinnedX_zero]

theorem E3_inv {γ₀ γZ γ₁ : Fin Tag.E8.rank → ℤ}
    (h₀Z : ∀ a b : R, pinnedX Tag.E8 R γZ b * pinnedX Tag.E8 R γ₀ a =
      pinnedX Tag.E8 R γ₀ a * pinnedX Tag.E8 R γZ b)
    (h₀₁ : ∀ a c : R, pinnedX Tag.E8 R γ₁ c * pinnedX Tag.E8 R γ₀ a =
      pinnedX Tag.E8 R γ₀ a * pinnedX Tag.E8 R γ₁ c)
    (hZ₁ : ∀ b c : R, pinnedX Tag.E8 R γ₁ c * pinnedX Tag.E8 R γZ b =
      pinnedX Tag.E8 R γZ b * pinnedX Tag.E8 R γ₁ c) (a b c : R) :
    (E3 γ₀ γZ γ₁ a b c)⁻¹ = E3 γ₀ γZ γ₁ (-a) (-b) (-c) := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [E3_mul h₀Z h₀₁ hZ₁, neg_add_cancel, neg_add_cancel, neg_add_cancel, E3_zero]

theorem PairData.comm3 {β₀ β₁ : Fin Tag.E8.rank → ℤ} (hA : PairData β₀ β₁) :
    (∀ a b : R, pinnedX Tag.E8 R (β₀ + (-highRoot Tag.E8 + β₁)) b *
      pinnedX Tag.E8 R (-highRoot Tag.E8 + β₀) a =
      pinnedX Tag.E8 R (-highRoot Tag.E8 + β₀) a *
        pinnedX Tag.E8 R (β₀ + (-highRoot Tag.E8 + β₁)) b) ∧
    (∀ a c : R, pinnedX Tag.E8 R (-highRoot Tag.E8 + β₁) c * pinnedX Tag.E8 R (-highRoot Tag.E8 + β₀) a =
      pinnedX Tag.E8 R (-highRoot Tag.E8 + β₀) a * pinnedX Tag.E8 R (-highRoot Tag.E8 + β₁) c) ∧
    (∀ b c : R, pinnedX Tag.E8 R (-highRoot Tag.E8 + β₁) c *
      pinnedX Tag.E8 R (β₀ + (-highRoot Tag.E8 + β₁)) b =
      pinnedX Tag.E8 R (β₀ + (-highRoot Tag.E8 + β₁)) b *
        pinnedX Tag.E8 R (-highRoot Tag.E8 + β₁) c) := by
  have hQ₀ := hA.r₀
  have hQ₁ := hA.r₁
  have hZ := hA.zr
  refine ⟨fun a b => ?_, fun a c => ?_, fun b c => ?_⟩
  · exact (pinnedX_commute_of_not_root hQ₀ hZ hA.c₀Z.1 hA.c₀Z.2.1 hA.c₀Z.2.2 a b).symm
  · exact (pinnedX_commute_of_not_root hQ₀ hQ₁ hA.c₀₁.1 hA.c₀₁.2.1 hA.c₀₁.2.2 a c).symm
  · exact (pinnedX_commute_of_not_root hZ hQ₁ hA.cZ₁.1 hA.cZ₁.2.1 hA.cZ₁.2.2 b c).symm

theorem Z_extract {β₀ β₁ : Fin Tag.E8.rank → ℤ} (hA : PairData β₀ β₁) {ω : R}
    (hω : ω ^ 2 + ω + 1 = 0) (t : R) :
    (⁅pinnedX Tag.E8 R (-highRoot Tag.E8) t, pinnedX Tag.E8 R β₀ 1 * pinnedX Tag.E8 R β₁ (1 ^ 2)⁆ *
        ⁅pinnedX Tag.E8 R (-highRoot Tag.E8) t, pinnedX Tag.E8 R β₀ ω * pinnedX Tag.E8 R β₁ (ω ^ 2)⁆⁻¹)⁻¹ *
      ⁅pinnedX Tag.E8 R (-highRoot Tag.E8) t,
        pinnedX Tag.E8 R β₀ (ω ^ 2) * pinnedX Tag.E8 R β₁ ((ω ^ 2) ^ 2)⁆ =
      pinnedX Tag.E8 R (β₀ + (-highRoot Tag.E8 + β₁)) t := by
  obtain ⟨hc1, hc2, hc3⟩ := hA.comm3 (R := R)
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  rw [c_calc hA, c_calc hA, c_calc hA]
  have e : ∀ s : R, pinnedX Tag.E8 R (-highRoot Tag.E8 + β₀) (t * s) *
      pinnedX Tag.E8 R (β₀ + (-highRoot Tag.E8 + β₁)) (s * (t * s ^ 2)) *
      pinnedX Tag.E8 R (-highRoot Tag.E8 + β₁) (t * s ^ 2) =
      E3 (-highRoot Tag.E8 + β₀) (β₀ + (-highRoot Tag.E8 + β₁)) (-highRoot Tag.E8 + β₁)
        (t * s) (s * (t * s ^ 2)) (t * s ^ 2) := fun s => rfl
  rw [e, e, e, E3_inv hc1 hc2 hc3, E3_mul hc1 hc2 hc3, E3_inv hc1 hc2 hc3, E3_mul hc1 hc2 hc3]
  have : E3 (-highRoot Tag.E8 + β₀) (β₀ + (-highRoot Tag.E8 + β₁)) (-highRoot Tag.E8 + β₁)
      (-(t * 1 + -(t * ω)) + t * ω ^ 2) (-(1 * (t * 1 ^ 2) + -(ω * (t * ω ^ 2))) + ω ^ 2 * (t * (ω ^ 2) ^ 2))
      (-(t * 1 ^ 2 + -(t * ω ^ 2)) + t * (ω ^ 2) ^ 2) =
      E3 (-highRoot Tag.E8 + β₀) (β₀ + (-highRoot Tag.E8 + β₁)) (-highRoot Tag.E8 + β₁) 0 t 0 := by
    have a1 : -(t * 1 + -(t * ω)) + t * ω ^ 2 = 0 := by linear_combination t * hω - t * h2
    have a2 : -(1 * (t * 1 ^ 2) + -(ω * (t * ω ^ 2))) + ω ^ 2 * (t * (ω ^ 2) ^ 2) = t := by
      linear_combination t * hω3 + t * (ω ^ 3 + 1) * hω3
    have a3 : -(t * 1 ^ 2 + -(t * ω ^ 2)) + t * (ω ^ 2) ^ 2 = 0 := by
      linear_combination t * hω - t * h2 + t * ω * hω3
    rw [a1, a2, a3]
  rw [this]
  unfold E3
  simp [pinnedX_zero]

end CCalc

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
