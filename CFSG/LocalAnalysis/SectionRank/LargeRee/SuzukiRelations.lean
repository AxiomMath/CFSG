module

public import CFSG.LocalAnalysis.SectionRank.LargeRee.Suzuki

public section

namespace CFSG.SectionRank.LargeRee

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Simplicity

section Matrices

variable (a : ℕ) {K : Type} [Field K]

omit [Field K] in
theorem zpow_mul_zpow_eq_one {G₀ : Type*} [GroupWithZero G₀] {x : G₀} (hx : x ≠ 0) {p q : ℤ}
    (h : p + q = 0) : x ^ p * x ^ q = 1 := by
  rw [← zpow_add₀ hx, h, zpow_zero]

theorem suzukiD_mul_suzukiD_inv (l : Kˣ) :
    CFSG.Blueprint.suzukiD a l * CFSG.Blueprint.suzukiD a l⁻¹ = 1 := by
  rw [CFSG.Blueprint.suzukiD, CFSG.Blueprint.suzukiD, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext k
  fin_cases k <;> simp
  · exact zpow_mul_zpow_eq_one l.ne_zero (by ring)
  · exact mul_inv_cancel₀ (zpow_ne_zero _ l.ne_zero)
  · exact inv_mul_cancel₀ (zpow_ne_zero _ l.ne_zero)
  · exact zpow_mul_zpow_eq_one l.ne_zero (by ring)

theorem suzukiD_inv_mul_suzukiD (l : Kˣ) :
    CFSG.Blueprint.suzukiD a l⁻¹ * CFSG.Blueprint.suzukiD a l = 1 := by
  have h := suzukiD_mul_suzukiD_inv a l⁻¹
  rwa [inv_inv] at h

@[expose] noncomputable def suzukiDElt (l : Kˣ) : CFSG.Blueprint.suzukiGroup a K :=
  ⟨⟨CFSG.Blueprint.suzukiD a l, CFSG.Blueprint.suzukiD a l⁻¹, suzukiD_mul_suzukiD_inv a l,
    suzukiD_inv_mul_suzukiD a l⟩, Subgroup.subset_closure (.inr (.inl ⟨l, rfl⟩))⟩

theorem suzukiDElt_inv (l : Kˣ) : (suzukiDElt a l)⁻¹ = suzukiDElt a l⁻¹ :=
  Subtype.ext (Units.ext rfl)

theorem suzukiW_mul_suzukiD_mul_suzukiW (l : Kˣ) :
    CFSG.Blueprint.suzukiW K * CFSG.Blueprint.suzukiD a l * CFSG.Blueprint.suzukiW K =
      CFSG.Blueprint.suzukiD a l⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.Blueprint.suzukiW, CFSG.Blueprint.suzukiD, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.diagonal_apply, sub_eq_add_neg]
  all_goals rw [add_comm]

end Matrices

section Transport

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) (ha : 1 ≤ a)

theorem r2EquivSuzuki_reeTorusHom
    (b : Kˣ) :
    r2EquivSuzuki K a hK ha ⟨reeTorusHom a hK fi_one_mem_longSet b, blockT_le_r2 hK ⟨b, rfl⟩⟩ =
      suzukiDElt a (b ^ (1 - 2 * (2 ^ a : ℤ))) := by
  refine Subtype.ext ?_
  rw [coe_r2EquivSuzuki]
  exact Units.ext (vMat_reeTorus_one hK b)

end Transport

end CFSG.SectionRank.LargeRee
