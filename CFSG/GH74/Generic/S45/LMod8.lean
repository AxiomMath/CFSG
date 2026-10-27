module

public import CFSG.GH74.Generic.S45.LSporCommon

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem exists_four_dvd_of_hasL2Model_pm_one {L : Type} [Group L]
    (h : HasL2Model L (fun q => q % 8 = 1 ∨ q % 8 = 7)) (hinv : ∃ v : L, orderOf v = 2) :
    ∃ x : L, 4 ∣ orderOf x := by
  obtain ⟨p, f, hp, hf, hq, hL⟩ := h
  obtain ⟨-, F, hFfield, hFfin, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSL hL
  have : Fact p.Prime := ⟨hp⟩
  let e' : L ≃* PSL(2, F) := e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have hodd : Odd p := by
    by_contra hp'
    have hpe : Even p := Nat.not_odd_iff_even.1 hp'
    have h2 : Even (p ^ f) := Nat.even_pow.2 ⟨hpe, by omega⟩
    rcases hq with h8 | h8 <;> exact absurd (Nat.even_iff.1 h2) (by omega)
  have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  obtain ⟨v, hv⟩ := hinv
  have hv' : orderOf (e' v) = 2 := by rw [MulEquiv.orderOf_eq]; exact hv
  obtain ⟨hc1, hc3⟩ := CFSG.Walter.psl2_centralizer_involution F hF hodd (by omega) hv'
  rcases hq with h8 | h8
  · obtain ⟨-, ⟨d⟩⟩ := hc1 (by omega)
    have hn : NeZero ((p ^ f - 1) / 2) := ⟨by omega⟩
    refine ⟨e'.symm (d.symm (DihedralGroup.r 1) : PSL(2, F)), ?_⟩
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
    omega
  · obtain ⟨-, ⟨d⟩⟩ := hc3 (by omega)
    have hn : NeZero ((p ^ f + 1) / 2) := ⟨by omega⟩
    refine ⟨e'.symm (d.symm (DihedralGroup.r 1) : PSL(2, F)), ?_⟩
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
    omega

theorem Hyp1310.mod_eight {K : Type} [Group K] [Finite K] {y : MulAut K} {L : Subgroup K}
    (h : Hyp1310 K y L) :
    ∃ q : ℕ, 5 ≤ q ∧ Odd q ∧ (q % 8 = 3 ∨ q % 8 = 5) ∧ Nat.card ↥L * 2 = q * (q ^ 2 - 1) ∧
      ∀ P : ℕ → Prop, P q → HasL2Model ↥L P := by
  obtain ⟨-, -, -, hLfix, hno4, -, -, hLinv, q, hq5, hqodd, hqcard, hmodel⟩ := h.data
  refine ⟨q, hq5, hqodd, ?_, hqcard, hmodel⟩
  by_contra hq8
  have hq8' : q % 8 = 1 ∨ q % 8 = 7 := by
    obtain ⟨k, hk⟩ := hqodd
    omega
  obtain ⟨v, hvL, hv⟩ := hLinv
  obtain ⟨x, hx⟩ := exists_four_dvd_of_hasL2Model_pm_one (hmodel _ hq8')
    ⟨⟨v, hvL⟩, by rw [Subgroup.orderOf_mk]; exact hv⟩
  exact hno4 (x : K) (hLfix _ x.2) (by rw [Subgroup.orderOf_coe]; exact hx)

end CFSG.GH74.Generic.S45
