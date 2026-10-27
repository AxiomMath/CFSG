module

public import Certificates.Certificate131003
public import CFSG.HardMathSupport.Foote.E27.LieTwo.Kill
public import CFSG.HardMathSupport.Foote.E27.LieTwo.MatChecks
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.HardMathSupport.Foote.E27

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.Sporadic.He.Native

section Certificates


theorem sp8_cover : ∃ S B : Subgroup (SpJ 4), Nat.card S = 3 ^ 5 ∧ Nat.card B = 3 ^ 4 ∧
    (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧
    (∀ s ∈ S, s ^ 3 = 1 → s ≠ 1 → ∃ x : SpJ 4, x * s * x⁻¹ ∈ B) :=
  Certificates.certificate131003

theorem E27Config.false_of_psp_eight {X : Type} [Group X] [Finite X] {K R T : Subgroup X}
    {z : X} (h : E27Config X K R T z) (hz : z ∈ K)
    (hcl : StatedClassicalModel (↥K) .PSp 4 2 1) : False := by
  obtain ⟨e⟩ := nonempty_mulEquiv_spJ (by norm_num) hcl
  have hcard : Nat.card (SpJ 4) = 3 ^ 5 * 194969600 := by
    rw [← Nat.card_congr e.toEquiv, (CFSG.Timmesfeld.card_statedClassicalModel_two hcl).2.2.1 rfl]
    decide
  have hfac : (Nat.card (SpJ 4)).factorization 3 = 5 :=
    factorization_three_of_eq hcard (by norm_num)
  obtain ⟨S, B, hS, hB, hBab, hcov⟩ := sp8_cover
  exact h.false_of_torus_cover hz e S (by rw [hS, hfac]) B hBab (by rw [hB]; norm_num) hcov

end Certificates

end CFSG.HardMathSupport.Foote.E27
