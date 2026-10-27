
module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43AutBase

public import Certificates.Certificate3962

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut

open CFSG.LieType.Multipliers.U43 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv

theorem autFacts : AutFacts := by
  have h := Certificates.certificate3962
  simp only [u43AutCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.all_eq_true] using h3
  · intro i hi j hj
    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at h4
    obtain ⟨hinv, hk⟩ := h4 i hi j hj
    refine ⟨hinv, fun k hk' l hl => ?_⟩
    have := hk k hk' l hl
    simpa [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] using this
  · simpa only [List.all_eq_true] using h5
  · simpa using h6
  · intro r hr
    simp only [List.all_eq_true, List.mem_range] at h7
    exact h7 r hr

theorem autModel :
    ∃ e : (Nrm : Subgroup Gp) ≃* MulAut X₀,
      ∀ (a : (Nrm : Subgroup Gp)) (x : X₀), psi (e a x) = (a : Gp) * psi x * (a : Gp)⁻¹ :=
  ⟨autEquiv autFacts, psi_autEquiv autFacts⟩

theorem card_Nrm :
    Nat.card (Nrm : Subgroup Gp) = 26127360 := by
  obtain ⟨e, -⟩ := autModel
  have h1 : Nat.card (MulAut X₀) = Nat.card (MulAut Nsub) :=
    Nat.card_congr (MulAut.congr e0).toEquiv
  have h2 := card_mulAut_Nsub_le
  have h3 := le_card_Nrm autFacts
  have h4 : Nat.card (Nrm : Subgroup Gp) = Nat.card (MulAut X₀) := Nat.card_congr e.toEquiv
  omega

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut
