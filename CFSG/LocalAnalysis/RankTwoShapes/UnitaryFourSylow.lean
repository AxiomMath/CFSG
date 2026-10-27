module

public import CFSG.LocalAnalysis.RankTwoShapes.OrderSixtyFour
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Presented

public section

namespace CFSG.RankTwoShapes

universe u

theorem nonempty_mulEquiv_unitaryFourPresented {Q : Type u} [Group Q] [Finite Q]
    (hcard : Nat.card Q = 64) (x y g h : Q) (hx4 : x ^ 4 = 1) (hy4 : y ^ 4 = 1)
    (hxy : rcomm x y = 1) (hgh : rcomm g h = 1) (hg2 : g ^ 2 = y ^ 2)
    (hh2 : h ^ 2 = x ^ 2 * y ^ 2) (hxg : rcomm x g = x ^ 2) (hyg : rcomm y g = x ^ 2 * y ^ 2)
    (hxh : rcomm x h = x ^ 2 * y ^ 2) (hyh : rcomm y h = y ^ 2)
    (hgen : Subgroup.closure ({x, y, g, h} : Set Q) = ⊤) :
    Nonempty (Q ≃* UnitaryFourPresented) := by
  have hrels : ∀ r ∈ unitaryFourRels, FreeGroup.lift ![x, y, g, h] r = 1 := by
    intro r hr
    simp only [unitaryFourRels, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons]
    · exact hx4
    · exact hy4
    · exact hxy
    · exact hgh
    · rw [hg2, mul_inv_cancel]
    · rw [hh2, mul_inv_cancel]
    · rw [show x⁻¹ * g⁻¹ * x * g = rcomm x g from rfl, hxg, mul_inv_cancel]
    · rw [show y⁻¹ * g⁻¹ * y * g = rcomm y g from rfl, hyg, mul_inv_cancel]
    · rw [show x⁻¹ * h⁻¹ * x * h = rcomm x h from rfl, hxh, mul_inv_cancel]
    · rw [show y⁻¹ * h⁻¹ * y * h = rcomm y h from rfl, hyh, mul_inv_cancel]
  let φ := PresentedGroup.toGroup hrels
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨PresentedGroup.of 0, PresentedGroup.toGroup.of _⟩
    · exact ⟨PresentedGroup.of 1, PresentedGroup.toGroup.of _⟩
    · exact ⟨PresentedGroup.of 2, PresentedGroup.toGroup.of _⟩
    · exact ⟨PresentedGroup.of 3, PresentedGroup.toGroup.of _⟩
  have : Finite UnitaryFourPresented :=
    Nat.finite_of_card_ne_zero (by rw [unitaryFourPresented_card]; norm_num)
  have hbij : Function.Bijective φ := hsurj.bijective_of_nat_card_le (by
    rw [hcard, unitaryFourPresented_card])
  exact ⟨(MulEquiv.ofBijective φ hbij).symm⟩

theorem free_three_action_unitary_sylow {Q : Type u} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (hrank : TwoRankLeTwo Q) (hnonab : ∃ a b : Q, a * b ≠ b * a) (α : MulAut Q)
    (hα : α ^ 3 = 1) (hfpf : ∀ q : Q, α q = q → q = 1) :
    ∃ (H : Type) (_ : Group H) (U : Sylow 2 H),
      CFSG.Assembly.LowTwoRank.StatedClassicalModel H .PSU 3 2 2 ∧
      Nonempty (Q ≃* (U : Subgroup H)) := by
  obtain ⟨hcard, -, -, -, -, x, y, g, h, -, -, hx4, hy4, hxy, hgh, hg2, hh2, hxg, hyg, hxh, hyh,
    hgen⟩ := free_three_action_order_sixty_four hQ hrank hnonab α hα hfpf
  obtain ⟨e⟩ := nonempty_mulEquiv_unitaryFourPresented hcard x y g h hx4 hy4 hxy hgh hg2 hh2 hxg
    hyg hxh hyh hgen
  obtain ⟨H, hH, U, hmodel, ⟨e'⟩⟩ := unitaryFourPresented_isSylow
  exact ⟨H, hH, U, hmodel, ⟨e.trans e'⟩⟩

end CFSG.RankTwoShapes
