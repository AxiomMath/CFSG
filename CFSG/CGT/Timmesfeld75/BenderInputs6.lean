module

public import CFSG.CGT.Timmesfeld75.Sec3Def
import CFSG.CGT.Timmesfeld75.BenderInputsBasic
import CFSG.CGT.Timmesfeld75.L2Basic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups

theorem isConj_of_orderOf_eq_two_of_mulEquiv_sz {K : Type*} [Group K] {a : ℕ} (ha : 1 ≤ a)
    (e : K ≃* Sz a) {x y : K} (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  have hK := isBenderGroup_of_mulEquiv_sz ha e
  have := finite_of_isBenderGroup hK
  exact CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isConj_of_orderOf_eq_two hK hx hy

theorem isConj_of_orderOf_eq_two_of_mulEquiv_psl2 {K : Type*} [Group K] {f : ℕ} (hf : 2 ≤ f)
    (e : K ≃* PSL(2, GaloisField 2 f)) {x y : K} (hx : orderOf x = 2) (hy : orderOf y = 2) :
    IsConj x y := by
  have hK := isBenderGroup_of_mulEquiv_psl2 hf e
  have := finite_of_isBenderGroup hK
  exact CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isConj_of_orderOf_eq_two hK hx hy

theorem involutionClassInput_of_dihedral
    (hD : ∀ (K : Type) [Group K], (∃ n : ℕ, Odd n ∧ 3 ≤ n ∧ Nonempty (K ≃* DihedralGroup n)) →
      ∀ x y : K, orderOf x = 2 → orderOf y = 2 → IsConj x y) :
    InvolutionClassInput := by
  intro K _ hK x y hx hy
  rcases hK with ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩ | hd
  · exact isConj_of_orderOf_eq_two_of_mulEquiv_psl2 hf e hx hy
  · exact isConj_of_orderOf_eq_two_of_mulEquiv_sz ha e hx hy
  · exact hD K hd x y hx hy

theorem involutionClassInput_of_repo : InvolutionClassInput := by
  refine involutionClassInput_of_dihedral ?_
  intro K _ h x y hx hy
  exact involutionClass_of_dihedral h hx hy

end CFSG.CGT.Timmesfeld75
