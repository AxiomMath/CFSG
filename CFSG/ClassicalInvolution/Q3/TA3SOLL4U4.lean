module

public import CFSG.ClassicalInvolution.Q3.TA3SOLDefs
public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4Lin
public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4Uni

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial LinearFlag L4U4

theorem noDatumL4U4_holds : NoDatumL4U4 := by
  rintro X _ _ _ p f hp hp2 h5 hcases hF ⟨R, S, t, hD⟩
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hz : orderOf t = 2 := hD.order
  rcases hcases with ⟨h8, hc⟩ | ⟨h8, hc⟩
  · obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hc
    let e : X ≃* projectiveSL 4 K := e₀.trans ((projectiveSpecialLinearGroupEquivStatedProj 4
      K).symm.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 K))
    have hKodd : Odd (Nat.card K) := hK ▸ hodd
    have hchar : ringChar K ≠ 2 := by
      have := Fintype.ofFinite K
      rw [Ne, FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card]
      obtain ⟨k, hk⟩ := hKodd
      omega
    rcases lin_shape hchar (by rw [hK]; exact h8) (z := e t) (by rw [MulEquiv.orderOf_eq]; exact hz)
      with hs | hs
    · exact not_fourGenerated_of_twoSL2Shape hD hKodd (by rw [hK]; omega) (hs.of_mulEquiv e) hF
    · exact false_of_normalSimpleShape hD (hs.of_mulEquiv e)
  · obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e₀⟩⟩ := hc
    have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    obtain ⟨R₀, hR₀⟩ := exists_isHypTransport (r := 2) (ε := 0) h
    let e : X ≃* hypPSU h 2 0 := e₀.trans (hypPSUEquivStatedProj h hR₀ (by omega)).symm
    have hFq : Nat.card h.fixedField = p ^ f := h.card_fixedField
    rcases uni_shape h hp2 h8 (z := e t) (by rw [MulEquiv.orderOf_eq]; exact hz) with hs | hs
    · exact not_fourGenerated_of_twoSL2Shape hD (hFq ▸ hodd) (by rw [hFq]; omega)
        (hs.of_mulEquiv e) hF
    · exact false_of_normalSimpleShape hD (hs.of_mulEquiv e)

end CFSG.ClassicalInvolution.Q3.TA3
